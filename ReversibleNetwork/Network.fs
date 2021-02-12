module ReversibleNetwork.Network

open ReversibleNetwork
open System.Collections.Generic

let empty = { Vertices = Set.empty; Edges = Map.empty; Gates = Set.empty; Inputs = []; Outputs = [] }

type AdjType = AdjVertex | AdjGate of Gate

let gatesDict ss =
  seq {
    for s in ss do
      let is, os = Gate.insOuts s
      for v in is ->
        v, (is, os, s)
  }
  |> dict

let makeGetAdjacents { Vertices = vs; Edges = es; Gates = ss; Outputs = outs } =
  let sd = lazy gatesDict ss
  fun v ->
    if es.ContainsKey(v) then
      Some (AdjVertex, [es.[v]])
    elif sd.Value.ContainsKey(v) then
      let _, os, s = sd.Value.[v]
      Some (AdjGate s, os)
    else 
      None
      
let private primarySimplify { Vertices = vs; Edges = es; Gates = ss; Inputs = is; Outputs = os } =
  let stk = Stack(is)
  let mutable vs' = Set.empty
  let vs'' = HashSet(vs.Count)
  let mutable es' = Map.empty
  let gs = gatesDict ss

  while stk.Count > 0 do
    let v = stk.Pop()
    if not <| vs''.Contains(v) then
      vs' <- Set.add v vs'
      vs''.Add(v) |> ignore
      let mutable v' = v
      while es.ContainsKey(v') do
        v' <- es.[v']

      if v = v' then
        if gs.ContainsKey(v) then
          let _, os, _ = gs.[v]
          Seq.iter stk.Push os
        elif not <| Seq.contains v os then
          failwith $"simplify: Dead-end vertex {v}"
      else
        // es'.Add(v, v')
        es' <- es'.Add(v, v')
        stk.Push(v')
          
  {
    Vertices = vs'
    Edges = es' |> Seq.map (|KeyValue|) |> Map.ofSeq
    Gates = ss
    Inputs = is
    Outputs = os
  }

let private secondarySimplify ({ Inputs = ins; Outputs = outs; Vertices = vs; Edges = es; Gates = ss } as n) =
  let insSet = Set.ofList ins
  let mutable vs' = vs
  let mutable es' = es
  let rec get v =
    let mutable v' = v
    while es.ContainsKey(v') do 
      vs' <- Set.remove v' vs'
      es' <- Map.remove v' es'
      v' <- es.[v']
    v'

  let ss' = 
    seq {
      for s in ss -> Gate.mapOuts get s
    }
    |> Set.ofSeq

  { 
    Inputs = ins
    Outputs = outs
    Vertices = vs'
    Edges = es'
    Gates = ss'
  }

let simplify = primarySimplify >> secondarySimplify

let getDepths ({ Inputs = ins; Outputs = outs; Vertices = vs } as n) =
  let getAdjacents = makeGetAdjacents n
  let ds = Dictionary(seq { for v in vs -> KeyValuePair(v, 0) })
  let visited = HashSet()
  let stk = Stack(seq { for v in ins -> v, 0 })
  while stk.Count > 0 do
    let v, dist = stk.Pop()
    visited.Add(v) |> ignore
    ds.[v] <- max ds.[v] dist
    let dist = ds.[v]
    match getAdjacents v with
    | None -> ()
    | Some (AdjVertex, vs) ->
      for v' in vs do
        stk.Push(v', 1 + dist)
    | Some (AdjGate s, _) ->
      let ins, outs = Gate.insOuts s
      for v' in ins do
        ds.[v'] <- max ds.[v] dist

      if Seq.forall visited.Contains ins then
        for v' in outs do
          stk.Push(v', 1 + dist)

  let maxOut = Seq.map (fun v -> ds.[v]) outs |> Seq.max
  for v in outs do 
    ds.[v] <- maxOut

  ds

let refUses { Edges = es; Gates = ss; Inputs = is; Outputs = os } : Vertex Set =
  Set.ofSeq <| seq {
    for KeyValue(v1, v2) in es do
      yield v1
      yield v2

    for s in ss do
      yield! Gate.toList s

    yield! is
    yield! os
  }

let refSources { Vertices = vs; Gates = ss; Inputs = is; Outputs = os } : Vertex Set =
  Set.ofSeq <| seq {
    yield! vs
  }

let names n = Set.union (refSources n) (refUses n)

/// Returns undefined refs and unused refs in a network
let brokenRefs n = refUses n - refSources n, refSources n - refUses n

let rename f { Vertices = vs; Edges = es; Gates = ss; Inputs = is; Outputs = os } =
  let mf = List.map f
  let es' = es |> Seq.map (fun (KeyValue(k, v)) -> f k, f v) |> Map.ofSeq
  let ss' = Set.map (Gate.map f) ss
  {
    Vertices = Set.map f vs
    Edges = es'
    Gates = ss'
    Inputs = mf is
    Outputs = mf os 
  }

let renameDict (d : #IDictionary<_, _>) { Vertices = vs; Edges = es; Gates = ss; Inputs = is; Outputs = os } =
  let f v = if d.ContainsKey v then d.[v] else v
  let mf = List.map f
  let es' = es |> Seq.map (fun (KeyValue(k, v)) -> f k, f v) |> Map.ofSeq
  let ss' = Set.map (Gate.map f) ss
  {
    Vertices = vs - Set.ofSeq d.Keys + Set.ofSeq d.Values
    Edges = es'
    Gates = ss'
    Inputs = mf is
    Outputs = mf os 
  }

let prefix (p : Vertex) = rename (fun n -> p @ n)

let checkPrefixes (n1 : Prefix) (n2 : Prefix) =
  if n1 = [] || n2 = [] then
    failwith $"checkPrefixes: empty $%A{(n1, n2)}"
  if n1 = n2 then
    failwith $"checkPrefixes: same $%A{(n1, n2)}"

let relabel ({ Inputs = is; Outputs = os; Vertices = vs } as n) = 
  let is, os = Array.ofList is, Array.ofList os
  let vs' = Array.ofSeq (vs - Set.ofArray is - Set.ofArray os)
  let vi = Seq.indexed vs' |> Seq.map (fun (i, v) -> v, i) |> dict
  let fmt = String.replicate (vs'.Length.ToString().Length) "0"
  let pad i = (i : int).ToString(fmt)
  let memo = Dictionary()
  let f name =
    if memo.ContainsKey(name) then
      memo.[name]
    else
      let res =
        match Array.tryFindIndex ((=) name) is with
        | None ->
          match Array.tryFindIndex ((=) name) os with
          | None ->
            let i = vi.[name] 
            [$"v{pad i}"]
          | Some j ->
            [$"o{pad j}"]
        | Some j ->
          [$"i{pad j}"]

      memo.Add(name, res)
      res
  rename f n

/// Canonical representation
let canonicalize = simplify >> relabel

/// Determines of two networks are equivalent
let equiv a b = canonicalize a = canonicalize b

