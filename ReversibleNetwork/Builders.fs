module ReversibleNetwork.Builders
open Network

let private unionMap m1 m2 =
  Map.ofSeq <| seq {
    for KeyValue(k, v) in m1 -> k, v
    for KeyValue(k, v) in m2 -> k, v
  }

let inverse f =
  let { Inputs = is; Outputs = os; Vertices = vs; Edges = es; Splits = ss } = f
  let es' = es |> Seq.map (fun (KeyValue(k, v)) -> v, k) |> Map.ofSeq
  let ss' = ss |> Set.map Split.inverse
  { f with Edges = es'; Inputs = os; Outputs = is; Splits = ss' }

let stack (n1, f) (n2, g) =
  checkPrefixes n1 n2
  let f', g' = prefix n1 f, prefix n2 g
  {
    Vertices = Set.union f'.Vertices g'.Vertices
    Edges = unionMap f'.Edges g'.Edges
    Splits = Set.union f'.Splits g'.Splits
    Inputs = f'.Inputs @ g'.Inputs
    Outputs = f'.Outputs @ g'.Outputs
  }

let compose (n1, f) (n2, g) =
  checkPrefixes n1 n2
  let { Outputs = fo }, { Inputs = gi } = f, g
  if fo.Length <> gi.Length then
    failwith $"compose: requires conformable outputs/inputs: {fo.Length} != {gi.Length}"

  let f', g' = prefix n1 f, prefix n2 g
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
  let (c, c', x, xp, xm) as spl = ["ci"], ["co"], ["xi"], ["xp"], ["xm"]
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
    failwith $"fromPerm: invalid permutation: %A{p}"

  let inputs = Array.map (fun x -> [sprintf "p%d" x]) ascending
  let outputs = Array.map (fun x -> [sprintf "q%d" x]) ascending
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

let reverse n = fromPerm (Array.init n (fun i -> n - i - 1))

let rotate n k = fromPerm (Array.init n (fun i -> (2 * n - i - 1 + k) % n))

let comm a b = fromPerm (Array.append [| a .. a + b - 1 |] [| 0 .. a - 1 |])

let multiplex n =
  let inputs = Array.init n (fun i -> [$"xi{i}"])
  let outPs = Array.init n (fun i -> [$"xp{i}"])
  let outMs = Array.init n (fun i -> [$"xm{i}"])
  let ci, co = ["ci"], ["co"]
  let interms = Array.init (n + 1) <| fun i -> 
    if i = 0 then ci elif i = n then co else [$"cI{i}"]

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
  let (~~) a = inverse a
  let (>>>) a b = compose (["f"], a) (["g"], b)
  let (&&&) a b = stack (["a"], a) (["b"], b)

open Operators
let cond n i (f : Network) = 
  let m = f.Inputs.Length
  if m <> f.Outputs.Length then
    failwith "cond: mismatch arity"

  let pToLast = fromPerm [| yield! seq { 0 .. i - 1 }; yield! { i + 1 .. n - 1 }; yield i |]
  let pre = pToLast &&& identity m
  let body = multiplex m >>> (identity 1 &&& (f &&& identity m)) >>> demultiplex m
  pre >>> (identity (n - 1) &&& body) >>> ~~pre

let rec repeat i (f : Network) =
  let m = f.Inputs.Length
  if m <> f.Outputs.Length then
    failwith "repeat: mismatch arity"

  let rec rep i =
    match i with
    | 0 -> identity m
    | n -> f >>> (rep (i - 1))

  rep i

let condRepeat n f =
  seq { 0 .. n - 1 }
  |> Seq.map (fun i -> cond n i (repeat i f))
  |> Seq.reduce (>>>)

