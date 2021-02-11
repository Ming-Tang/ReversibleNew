module Main
open System.IO
open System.Diagnostics
open ReversibleNetwork
open ReversibleNetwork.Network
// open Builders
// open Builders.Operators
open Simulator
open Propagator
open ReversibleArith.Iso
open ReversibleArith.Num
open ReversibleArith.NumIso

let printBools xs =
  new string(xs |> Array.map (fun b -> if b then '1' else '0'))
  |> printfn "%s"

let benchmark s =
  let iso' = (s :> ISuccAddBuilder<_>).AddMultiple 3
  for i in 0 .. 100 do
    iso'
    |> getSymIso 
    |> FromIso.fromSymIso Network.simplify
    |> Network.canonicalize
    |> ignore

let runNetwork2 (s : #ISuccAddBuilder<_>) n formatExpr formatResult =
  let sim = Propagator(n, boolForward, boolBackward)
  let m = getBases s |> List.reduce (*)
  let p = getBases s |> List.reduce (+)
  for n1 in 0 .. m - 1 do
    for n2 in 0 .. m - 1 do
      let input = boolsFromIntPair (s, s) (n1, n2)
      printBools input
      printfn "%s%s" (String.replicate p "a") (String.replicate p "b")
      let res = sim.Evaluate(input)
      printBools res
      printfn "%s%s" (String.replicate p "c") (String.replicate p "d")
      let p, q = intPairFromBools (s, s) res
      printfn $"{formatExpr n1 n2} = {formatResult p q} (mod {m})"

let runNetwork (s : #ISuccAddBuilder<_>) n formatExpr =
  let sim = Propagator(n, boolForward, boolBackward)
  let m = getBases s |> List.reduce (*)
  for n1 in 0 .. m - 1 do
    let input = intToBools s n1
    printBools input
    let n1 = sim.Evaluate(input)
    printBools n1
    let a = intFromBools s input
    let b = intFromBools s n1
    printfn $"{formatExpr a} = {b} (mod {m})"

let exportSymIso iso =
  let s = symIsoToLaTeX None (getSymIso iso)
  File.WriteAllText("Output.md", $"\n$${s}$$\n")

let exportGraphviz n =
  async {
    File.WriteAllText("output.svg", "")
    let ds = getDepths n
    let maxDepth = ds |> Seq.map ((|KeyValue|) >> snd) |> Seq.max
    printfn $"vertices={n.Vertices.Count} edges={n.Edges.Count} gates={n.Gates.Count} maxDepth={maxDepth}"

    let graphviz = 
      n
      |> toGraphviz (fun v -> $"""{String.concat "." v}:{ds.[v]}""") 
      |> sprintf "%s"
    File.WriteAllText("input.dot", graphviz)
    let p = Process.Start("dot", "-Tsvg input.dot -o output.svg")
    p.WaitForExit()
    return ()
  }

let bIsoToNetwork biso =
  biso |> getSymIso |> FromIso.fromSymIso Network.simplify |> Network.canonicalize

[<EntryPoint>]
let main argv =
#if X
  let s = succNum B2 (succNum B2 (succDigit B2)) :> ISuccAddBuilder<_>
  let f = s.PlusConst 3 |> bIsoToNetwork
  let g = s.Neg |> bIsoToNetwork
  let composed = 
    Builders.multiplex 5
    // let (>>>) = Builders.Operators.(>>>)
    // (Builders.cond 5 2 f >>> Builders.cond 5 3 g)
    |> Network.canonicalize

  exportGraphviz composed
  0
#else

  let s = succNum B2 (succNum B2 (succDigit B2)) :> ISuccAddBuilder<_>
  // let s = succNum B2 (succNum B2 (succNum B2 (succDigit B2)))
  // let s = succNum B5 (succNum B4 (succNum B4 (succDigit B6)))

  // let plusConst = 35
  // let pc = s.PlusConst plusConst
  // let neg = s.Neg
  // let iso = ReversibleArith.Iso.Operators.(>>>) pc neg

  let add = s.AddMultiple 3
  // let add = s.Add
  let nAdd = bIsoToNetwork add
  runNetwork2 s nAdd (fun a b -> $"{a} + 3*{b}") (fun a b -> $"{a}")
  let t = exportGraphviz nAdd |> Async.StartAsTask
  exportSymIso add
  t.Wait()
  printfn "-"

  0
#endif

