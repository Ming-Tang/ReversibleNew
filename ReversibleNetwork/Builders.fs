﻿module ReversibleNetwork.Builders
open Network

let private unionMap m1 m2 =
  Map.fold (fun m0 k v -> Map.add k v m0) m1 m2

let inverse f =
  let { Inputs = is; Outputs = os; Vertices = vs; Edges = es; Splits = ss } = f
  let es' = es |> Seq.map (fun (KeyValue(k, v)) -> v, k) |> Map.ofSeq
  let ss' = ss |> Set.map Split.inverse
  { f with Edges = es'; Inputs = os; Outputs = is; Splits = ss' }

let private rsLock = obj()
let mutable private _i = 0
/// Random string
let private rs() = 
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
    Splits = Set.union f'.Splits g'.Splits
    Inputs = f'.Inputs @ g'.Inputs
    Outputs = f'.Outputs @ g'.Outputs
  }

let compose f g =
  let { Outputs = fo }, { Inputs = gi } = f, g
  if fo.Length <> gi.Length then
    invalidArg "f" $"compose: requires conformable outputs/inputs: {fo.Length} != {gi.Length}"

  let f', g' = ensureDisjoint f g
  let { Outputs = fo' }, { Inputs = gi' } = f', g'
  let bridges = Seq.zip fo' gi' |> Map.ofSeq
  {
    Vertices = Set.union f'.Vertices g'.Vertices
    Edges = unionMap bridges (unionMap f'.Edges g'.Edges)
    Splits = Set.union f'.Splits g'.Splits
    Inputs = f'.Inputs
    Outputs = g'.Outputs
  }

let forwardSplit =
  let (c, c', x, xp, xm) as spl = ["ci"; rs()], ["co"; rs()], ["xi"; rs()], ["xp"; rs()], ["xm"; rs()]
  {
    Vertices = Set.ofList [c; c'; x; xp; xm]
    Edges = Map.empty
    Splits = Set.ofList [split (spl, SplitDir.SDForward)]
    Inputs = [c; x]
    Outputs = [c'; xp; xm]
  }

let reverseSplit = inverse forwardSplit

let fromPerm p =
  let sorted = Array.sort p
  let ascending = Array.init p.Length id
  if List.ofArray sorted <> List.ofArray ascending then
    invalidArg "p" $"fromPerm: invalid permutation: %A{p}"

  let inputs = Array.map (fun x -> [sprintf "p%d" x; rs()]) ascending
  let outputs = Array.map (fun x -> [sprintf "q%d" x; rs()]) ascending
  let edges = inputs |> Seq.mapi (fun i inp -> inp, outputs.[p.[i]]) 
              |> Map.ofSeq
  {
    Vertices = Set.ofSeq (Seq.append inputs outputs)
    Edges = edges
    Splits = Set.empty
    Inputs = List.ofArray inputs
    Outputs = List.ofArray outputs
  }

let identity n = fromPerm (Array.init n id)

let reverse n = fromPerm (Array.init n (fun i -> i) |> Array.rev)

let rotate n k = fromPerm (Array.init n (fun i -> (n + i + k % n) % n))

let comm a b = fromPerm (Array.append [| a .. a + b - 1 |] [| 0 .. a - 1 |])

let multiplex n =
  let inputs = Array.init n (fun i -> [$"xi{i}"; rs()])
  let outPs = Array.init n (fun i -> [$"xp{i}"; rs()])
  let outMs = Array.init n (fun i -> [$"xm{i}"; rs()])
  let ci, co = ["ci"; rs()], ["co"; rs()]
  let interms = Array.init (n + 1) <| fun i -> 
    if i = 0 then ci elif i = n then co else [$"cI{i}"; rs()]

  let ins = [ yield ci; yield! inputs ]
  let outs = [ yield co; yield! outPs; yield! outMs ]
  let vs = Set.ofSeq <| Seq.concat [inputs; outPs; outMs; interms]
  let splits = Array.init n <| fun i -> 
    { CIn = interms.[i]; COut = interms.[i + 1]; XIn = inputs.[i]
      XOutPlus = outPs.[i]; XOutMinus = outMs.[i]; Dir = SDForward }

  { Vertices = vs; Edges = Map.empty; Splits = Set.ofArray splits
    Inputs = ins; Outputs = outs }

let demultiplex n = multiplex n |> inverse

module Operators =
  let inline (~~) a = inverse a
  let inline (>>>) f g = compose f g
  let inline (&&&) a b = stack a b

open Operators
let cond n i (f : Network) = 
  let m = f.Inputs.Length
  if m <> f.Outputs.Length then
    invalidArg "f" "cond: mismatch arity"

  let pToLast = fromPerm [| yield! seq { 0 .. i - 1 }; yield! { i + 1 .. n - 1 }; yield i |]
  let pre = pToLast &&& identity m
  let body = multiplex m >>> (identity 1 &&& (f &&& identity m)) >>> demultiplex m
  pre >>> (identity (n - 1) &&& body) >>> ~~pre

let rec repeat i (f : Network) =
  let m = f.Inputs.Length
  if m <> f.Outputs.Length then
    invalidArg "f" "repeat: mismatch arity"

  let rec rep i =
    match i with
    | 0 -> identity m
    | 1 -> f
    | n -> f >>> (rep (i - 1))

  rep i

let condRepeat n f =
  seq {
    for i in 0 .. n - 1 -> cond n i (repeat i f)
  }
  |> Seq.reduce (>>>)

