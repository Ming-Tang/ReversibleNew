[<AutoOpen>]
module ReversibleNetwork.ToGraphviz
open ReversibleNetwork
open ReversibleNetwork.Network
open System.Collections.Generic
open System.Text

let toGraphviz (getLabel: Vertex -> string) { Vertices = vs; Edges = es; Gates = ss; Inputs = is; Outputs = os } =
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

  for i, sp in Seq.indexed ss do
    match sp with
    | { CIn = cIn; COut = cOut; XIn = xIn; XOutPlus = xOutPlus; XOutMinus = xOutMinus; Buffer = bs; Dir = sd; } ->
      sb.AppendLine("  {") |> ignore
      let rarr, larr = "&rarr;", "&larr;"
      let arr =
        match sd with 
        | SplitDir.SDForward -> rarr 
        | SplitDir.SDBackward -> larr
        | SplitDir.SDBuffer -> ""

      let splitLine = lazy $"    split_{i} [shape=square, label=\"{arr}\"]"
      match sd with
      | SplitDir.SDBuffer ->
        let mids = bs |> Seq.mapi (fun j _ -> $"buf{i}_{j} [label=b{i}]") |> String.concat "; "
        sb.AppendLine($"    subgraph cluster_mid{i} {{ rank=same; edge[style=invis]; {mids} }}") |> ignore
        for j, (v, v') in Seq.indexed bs do
          sb.AppendLine($"    {vertexId v} -> buf{i}_{j} -> {vertexId v'}") |> ignore

      | SplitDir.SDForward -> 
        sb.AppendLine(splitLine.Value) |> ignore
        sb.AppendLine($"    {vertexId cIn} -> split_{i} [label=c]") |> ignore
        sb.AppendLine($"    {vertexId xIn} -> split_{i} [label=x]") |> ignore
        sb.AppendLine($"    split_{i} -> {vertexId cOut} [label=c1]") |> ignore
        sb.AppendLine($"    split_{i} -> {vertexId xOutPlus} [label=xp]") |> ignore
        sb.AppendLine($"    split_{i} -> {vertexId xOutMinus} [label=xm]") |> ignore

      | SplitDir.SDBackward -> 
        sb.AppendLine(splitLine.Value) |> ignore
        sb.AppendLine($"    split_{i} -> {vertexId cIn} [label=c]") |> ignore
        sb.AppendLine($"    split_{i} -> {vertexId xIn} [label=x]") |> ignore
        sb.AppendLine($"    {vertexId cOut} -> split_{i} [label=c1]") |> ignore
        sb.AppendLine($"    {vertexId xOutPlus} -> split_{i} [label=xp]") |> ignore
        sb.AppendLine($"    {vertexId xOutMinus} -> split_{i} [label=xm]") |> ignore

      sb.AppendLine("  }") |> ignore

  sb.AppendLine("}") |> ignore
  sb.ToString()

