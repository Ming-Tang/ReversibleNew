module ReversibleNetwork.Builders
open Network

let private unionMap m1 m2 =
  Map.fold (fun m0 k v -> Map.add k v m0) m1 m2

let inverse f =
  let { Inputs = is; Outputs = os; Vertices = vs; Edges = es; Gates = ss } = f
  let es' = es |> Seq.map (fun (KeyValue(k, v)) -> v, k) |> Map.ofSeq
  let ss' = ss |> Set.map Gate.inverse
  { f with Edges = es'; Inputs = os; Outputs = is; Gates = ss' }

[<AutoOpen>]
module RandomString =
  let private rsLock = obj()
  let mutable private _i = 103

  /// Random string
  let rs() = 
    lock rsLock <| fun _ ->
      _i <- _i + 1 
      string _i

let rec ensureDisjoint f g =
  let { Vertices = fvs }, { Vertices = gvs } = f, g
#if DISJOINT
  let pre1, pre2 = rs(), rs()
  prefix [pre1] f, prefix [pre2] g
#else
  let ne = not (Set.isEmpty fvs) && not (Set.isEmpty gvs)
  if ne && (Set.contains (Set.minElement fvs) gvs || not (Set.isEmpty (Set.intersect fvs gvs))) then
    let pre1, pre2 = rs(), rs()
    if pre1 = pre2 then
      failwith $"pre1 = pre2: {pre1}, {pre2}"
    prefix [pre1] f, prefix [pre2] g
  else
    f, g
#endif

let stack f g =
  let f', g' = ensureDisjoint f g
  {
    Vertices = Set.union f'.Vertices g'.Vertices
    Edges = unionMap f'.Edges g'.Edges
    Gates = Set.union f'.Gates g'.Gates
    Inputs = f'.Inputs @ g'.Inputs
    Outputs = f'.Outputs @ g'.Outputs
  }

let compose f g =
  let { Outputs = fo }, { Inputs = gi } = f, g
  if fo.Length <> gi.Length then
    invalidArg (nameof f) $"compose: requires conformable outputs/inputs: {fo.Length} != {gi.Length}"

  let f', g' = ensureDisjoint f g
  let { Outputs = fo' }, { Inputs = gi' } = f', g'
  let outToIn = Seq.zip fo' gi' |> dict
  let func = (fun v -> if outToIn.ContainsKey v then outToIn.[v] else v)
  let f' = renameDict outToIn f'
  // let g' = rename func g'
#if P || !P
  {
    Vertices = Set.union f'.Vertices g'.Vertices
    Edges = unionMap f'.Edges g'.Edges
    Gates = Set.union f'.Gates g'.Gates
    Inputs = f'.Inputs
    Outputs = g'.Outputs
  }
#else
  let requireBuf = false
  // let requireBuf = not(Set.isEmpty f'.Gates) && not(Set.isEmpty g'.Gates)
  // let requireBuf = true
  let edges, gates = 
    if requireBuf then
      unionMap f'.Edges g'.Edges,
      (
        let s = Buffer (Seq.zip fo' gi' |> List.ofSeq)
        in Set.add s (Set.union f'.Gates g'.Gates)
      )
    else
      (
        let bridges = Seq.zip fo' gi' |> Map.ofSeq
        unionMap bridges (unionMap f'.Edges g'.Edges)
      ),
      Set.union f'.Gates g'.Gates

  {
    Vertices = Set.union f'.Vertices g'.Vertices
    Edges = edges
    Gates = gates
    Inputs = f'.Inputs
    Outputs = g'.Outputs
  }
#endif

let fromPerm p =
  let sorted = Array.sort p
  let ascending = Array.init p.Length id
  if List.ofArray sorted <> List.ofArray ascending then
    invalidArg (nameof p) $"fromPerm: invalid permutation: %A{p}"

#if P || !P
  let inputs = Array.init p.Length (fun i -> [$"p{i}"; rs()])
  let outputs = [ for i in 0 .. inputs.Length - 1 -> inputs.[p.[i]] ]
  {
    Vertices = Set.ofSeq (Seq.append inputs outputs)
    Edges = Map.empty
    Gates = Set.empty
    Inputs = List.ofArray inputs
    Outputs = outputs
  }
#else
  let inputs = Array.init p.Length (fun i -> [$"p{i}"; rs()])
  let outputs = Array.init p.Length (fun i -> [$"q{i}"; rs()])
  let edges = 
    seq {
      for i, o in Seq.indexed outputs ->
        inputs.[p.[i]], o
    }
    |> Map.ofSeq

  {
    Vertices = Set.ofSeq (Seq.append inputs outputs)
    Edges = edges
    Gates = Set.empty
    Inputs = List.ofArray inputs
    Outputs = List.ofArray outputs
  }
#endif

let identity n = fromPerm (Array.init n id)

let reverse n = fromPerm (Array.init n (fun i -> i) |> Array.rev)

let rotate n k = fromPerm (Array.init n (fun i -> (n + i - k % n) % n))

let comm a b = fromPerm (Array.append [| a .. a + b - 1 |] [| 0 .. a - 1 |])

let multiplex n =
  let inputs = Array.init n (fun i -> [$"xi{i}"; rs()])
  let inputInterms = Array.init n (fun i -> [$"xiI{i}"; rs()])
  let outPs = Array.init n (fun i -> [$"xp{i}"; rs()])
  let outMs = Array.init n (fun i -> [$"xm{i}"; rs()])
  let outPInterms = Array.init n (fun i -> [$"xpI{i}"; rs()])
  let outMInterms = Array.init n (fun i -> [$"xmI{i}"; rs()])
  let ci, co = ["ci"; rs()], ["co"; rs()]
  let cii, coi = ["ciI"; rs()], ["coI"; rs()]
  let interms = Array.init (n + 1) <| fun i -> 
    if i = 0 then cii elif i = n then coi else [$"c_I{i}"; rs()]

  let ins = [ yield ci; yield! inputs ]
  let outs = [ yield co; yield! outPs; yield! outMs ]
  let vs = Seq.concat [inputs; inputInterms; outPs; outMs; outPInterms; outMInterms; interms; [|ci; co|]] |> Set.ofSeq
  let gs = Array.init n <| fun i -> 
    Split((interms.[i], interms.[i + 1], inputInterms.[i], outPInterms.[i], outMInterms.[i]), SplitDir.SDForward)

  let es = 
    seq {
      yield ci, cii
      yield coi, co
      for xs, ys in [inputs, inputInterms; outPInterms, outPs; outMInterms, outMs] do
        yield! Seq.zip xs ys
    }
    |> Map.ofSeq

  { Vertices = vs; Edges = es; Gates = Set.ofArray gs
    Inputs = ins; Outputs = outs }

let demultiplex n = multiplex n |> inverse

let buffer n =
  let inputs = Array.init n (fun i -> [$"bi{i}"; rs()])
  let outputs = Array.init n (fun i -> [$"bo{i}"; rs()])
  let vs = Seq.append inputs outputs |> Set.ofSeq
  let s = Buffer(Seq.zip inputs outputs |> List.ofSeq)
  { Vertices = vs; Edges = Map.empty; Gates = Set.singleton s
    Inputs = List.ofArray inputs; Outputs = List.ofArray outputs }

let extract (i0, n) =
  let inputs = Array.init n (fun i -> [$"bi{i}"; rs()])
  let outputs = Array.init n (fun i -> [$"bo{i}"; rs()])
  let vs = Seq.append inputs outputs |> Set.ofSeq
  let edges =
    seq {
      for i in 0 .. n do
        if i <> i0 then yield inputs.[i], outputs.[i]
    }
    |> Map.ofSeq
  { Vertices = vs; Edges = edges; Gates = Set.empty
    Inputs = List.ofArray inputs; Outputs = List.ofArray outputs }, (inputs.[i0], outputs.[i0])

module Operators =
  let inline (~~) a = inverse a
  let inline (>>>) f g = compose f g
  let inline (&&&) a b = stack a b

open Operators

let moveToLast n i = identity i &&& comm 1 (n - i - 1)
let symMoveToLast n i = identity i &&& comm (n - i - 1) 1
let cond n i (f : Network) = 
  let m = f.Inputs.Length
  if m <> f.Outputs.Length then
    invalidArg (nameof f) "cond: mismatch arity"

  if i >= n || i < 0 then
    invalidArg (nameof i) "cond: out of range"

  let pre = moveToLast n i &&& identity m
  let post = symMoveToLast n i &&& identity m
  let body = multiplex m >>> (identity 1 &&& (f &&& identity m)) >>> demultiplex m
  pre >>> (identity (n - 1) &&& body) >>> post

let mcond conds (f : Network) =
  match conds with
  | [] -> invalidArg (nameof conds) "mcond: no conditions"
  | [i, n] -> cond n i f
  | (i0, n0) :: xs ->
    let m = f.Inputs.Length
    if m <> f.Outputs.Length then
      invalidArg (nameof f) "mcond: mismatch arity"

    let rec cmcond conds =
      match conds with
      | [] -> multiplex m >>> (identity 1 &&& (f &&& identity m)) >>> demultiplex m
      | (i0, n0) :: xs ->
        let nr = m + List.sumBy snd xs
        let ciToLast = (identity 1 &&& moveToLast n0 i0) >>> comm 1 n0 >>> (identity (n0 - 1) &&& comm 1 1)
        let rmpx = multiplex 1 >>> (identity 1 &&& comm 1 1)
        let mPart = identity (n0 - 1) &&& rmpx
        let prefix = ((ciToLast >>> mPart) &&& identity nr)
        let postfix = ~~prefix
        prefix >>> (identity (n0 + 1) &&& cmcond xs) >>> postfix

    let nr = m + List.sumBy snd xs
    let prefix = moveToLast n0 i0 &&& identity nr
    let postfix = symMoveToLast n0 i0 &&& identity nr
    let mid = identity (n0 - 1) &&& cmcond xs
    prefix >>> mid >>> postfix

let rec repeat i (f : Network) =
  let m = f.Inputs.Length
  if m <> f.Outputs.Length then
    invalidArg (nameof f) "repeat: mismatch arity"

  let rec rep i =
    match i with
    | 0 -> identity m
    | 1 -> f
    | n -> f >>> (rep (i - 1))

  rep i

let condRepeat n f =
  seq {
    for i in 0 .. n - 1 ->
      cond n i (repeat i f)
  }
  |> Seq.reduce (>>>)
