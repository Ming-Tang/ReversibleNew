module ReversibleNetwork.Network

open ReversibleNetwork
open System.Collections.Generic
open System.Text

let empty = { Vertices = Set.empty; Edges = Map.empty; Splits = Set.empty; Inputs = []; Outputs = [] }

let toGraphviz (getLabel: Vertex -> string) { Vertices = vs; Edges = es; Splits = ss; Inputs = is; Outputs = os } =
  let ids = Dictionary()
  let vertexId (v : Vertex) = v |> String.concat "." |> sprintf "%A"

  let vertexList vs = 
    vs
    |> Seq.map vertexId
    |> Seq.indexed 
    |> Seq.map(fun (i, v) -> 
      $"{v} [label=%A{i}, group=a]"
    )
    |> String.concat "; "

  // let vertexChain vs = 
  //   vs
  //   |> Seq.map vertexId
  //   |> Seq.map (fun v -> $"{v}")
  //   |> String.concat " -> "

  let sb = StringBuilder()
  sb.AppendLine("digraph G {") |> ignore
  sb.AppendLine("  rankdir=LR; node[shape=circle, margin=0, width=0.1, fontsize=8];") |> ignore

  sb.AppendLine("  subgraph cluster_inputs {") |> ignore
  sb.AppendLine("    rank=source; edge[style=invis];") |> ignore
  sb.AppendLine($"    {vertexList is};") |> ignore
  // sb.AppendLine($"    {vertexChain is};") |> ignore
  sb.AppendLine("  }") |> ignore

  sb.AppendLine("  subgraph cluster_outputs {") |> ignore
  sb.AppendLine("    rank=sink; edge[style=invis];") |> ignore
  sb.AppendLine($"    {vertexList os};") |> ignore
  // sb.AppendLine($"    {vertexChain os};") |> ignore
  sb.AppendLine("  }") |> ignore

  for v in vs do
    sb.AppendLine($"  {vertexId v}[label=%A{getLabel v}]") |> ignore

  for KeyValue(v1, v2) in es do
    sb.AppendLine($"  {vertexId v1} -> {vertexId v2}") |> ignore

  for i, { CIn = cIn; COut = cOut; XIn = xIn; XOutPlus = xOutPlus; XOutMinus = xOutMinus; Dir = sd } in Seq.indexed ss do
    sb.AppendLine("  {") |> ignore
    let rarr, larr = "&rarr;", "&larr;"
    sb.AppendLine($"    split_{i} [shape=square, label=\"{if sd = SDForward then rarr else larr}\"]") |> ignore
    match sd with
    | SDForward -> 
      sb.AppendLine($"    {vertexId cIn} -> split_{i} [label=c]") |> ignore
      sb.AppendLine($"    {vertexId xIn} -> split_{i} [label=x]") |> ignore
      sb.AppendLine($"    split_{i} -> {vertexId cOut} [label=c1]") |> ignore
      sb.AppendLine($"    split_{i} -> {vertexId xOutPlus} [label=xp]") |> ignore
      sb.AppendLine($"    split_{i} -> {vertexId xOutMinus} [label=xm]") |> ignore
    | SDBackward -> 
      sb.AppendLine($"    split_{i} -> {vertexId cIn} [label=c]") |> ignore
      sb.AppendLine($"    split_{i} -> {vertexId xIn} [label=x]") |> ignore
      sb.AppendLine($"    {vertexId cOut} -> split_{i} [label=c1]") |> ignore
      sb.AppendLine($"    {vertexId xOutPlus} -> split_{i} [label=xp]") |> ignore
      sb.AppendLine($"    {vertexId xOutMinus} -> split_{i} [label=xm]") |> ignore
    sb.AppendLine("  }") |> ignore

  sb.AppendLine("}") |> ignore
  sb.ToString()

type AdjType = AdjVertex | AdjSplit of Split

let splitsDict ss =
  seq {
    for s in ss do
      match s.Dir with
      | SDForward ->
        let outs = Split.outs s 
        for v in Split.ins s -> v, (outs, s)
      | SDBackward ->
        let ins = Split.ins s
        for v in Split.outs s -> v, (ins, s)
  }
  |> dict

let makeGetAdjacents { Vertices = vs; Edges = es; Splits = ss; Outputs = outs } =
  let sd = lazy splitsDict ss
  fun v ->
    if es.ContainsKey(v) then
      Some (AdjVertex, [es.[v]])
    elif sd.Value.ContainsKey(v) then
      let adjs, sp = sd.Value.[v]
      Some (AdjSplit sp, adjs)
    else 
      None
      
let private primarySimplify { Vertices = vs; Edges = es; Splits = ss; Inputs = is; Outputs = os } =
  let stk = Stack(is)
  let vs' = HashSet()
  let es' = Dictionary()

  let splits = splitsDict ss

  while stk.Count > 0 do
    let v = stk.Pop()
    if not <| vs'.Contains(v) then
      vs'.Add(v) |> ignore
      let mutable v' = v
      while es.ContainsKey(v') do
        v' <- es.[v']

      if v = v' then
        if splits.ContainsKey(v) then
          Seq.iter stk.Push <| fst splits.[v]
        elif not <| Seq.contains v os then
          failwith $"simplify: Dead-end vertex ${v}"
      else
        es'.Add(v, v')
        stk.Push(v')
          
  {
    Vertices = Set.ofSeq vs'
    Edges = es' |> Seq.map (|KeyValue|) |> Map.ofSeq
    Splits = ss
    Inputs = is
    Outputs = os
  }

let private secondarySimplify ({ Inputs = ins; Outputs = outs; Vertices = vs; Edges = es; Splits = ss } as n) =
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
      for s in ss ->
        match s.Dir with
        | SDForward -> Split.mapOut get s
        | SDBackward -> Split.mapIn get s
    }
    |> Set.ofSeq

  { 
    Inputs = ins
    Outputs = outs
    Vertices = vs'
    Edges = es'
    Splits = ss'
  }

let simplify = primarySimplify >> secondarySimplify

let refUses { Edges = es; Splits = ss; Inputs = is; Outputs = os } : Vertex Set =
  Set.ofSeq <| seq {
    for KeyValue(v1, v2) in es do
      yield v1
      yield v2

    for s in ss do
      yield! Split.toList s
  }

let refSources { Vertices = vs; Splits = ss; Inputs = is; Outputs = os } : Vertex Set =
  Set.ofSeq <| seq {
    yield! vs
    yield! is
    yield! os
  }

let names n = Set.union (refSources n) (refUses n)

/// Returns undefined refs and unused refs in a network
let brokenRefs n = refUses n - refSources n, refSources n - refUses n

let rename f { Vertices = vs; Edges = es; Splits = ss; Inputs = is; Outputs = os } =
  let mf = List.map f
  let es' = es |> Seq.map (fun (KeyValue(k, v)) -> f k, f v) |> Map.ofSeq
  let ss' = Set.map (Split.map f) ss
  { Vertices = Set.map f vs; Edges = es'; Splits = ss'; Inputs = mf is; Outputs = mf os }

let prefix (p : Vertex) = rename (fun n -> p @ n)

let checkPrefixes (n1 : Prefix) (n2 : Prefix) =
  if n1 = [] || n2 = [] then
    failwith $"checkPrefixes: empty $%A{(n1, n2)}"
  if n1 = n2 then
    failwith $"checkPrefixes: same $%A{(n1, n2)}"

let relabel ({ Inputs = is; Outputs = os; Vertices = vs } as n) = 
  let is, os = Array.ofList is, Array.ofList os
  let vs' = Array.ofSeq (vs - Set.ofArray is - Set.ofArray os)
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
            let i = Array.findIndex ((=) name) vs'
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

