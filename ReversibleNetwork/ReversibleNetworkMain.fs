module Main
open System.IO
open System.Diagnostics
open ReversibleNetwork
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
  let ds = getDepths n
  let maxDepth = ds |> Seq.map ((|KeyValue|) >> snd) |> Seq.max
  printfn $"vertices={n.Vertices.Count} edges={n.Edges.Count} splits={n.Splits.Count} maxDepth={maxDepth}"

  let graphviz = 
    n
    |> Network.toGraphviz (fun v -> $"""{String.concat "." v}:{ds.[v]}""") 
    |> sprintf "%s"
  File.WriteAllText("input.dot", graphviz)
  let p = Process.Start("dot", "-Tsvg input.dot -o output.svg")
  p.WaitForExit()

[<EntryPoint>]
let main argv =

  // let s = succDigit B5
  let s = succNum B2 (succDigit B2)
  // let s = succNum B2 (succNum B2 (succNum B2 (succDigit B2)))
  // let s = succNum B5 (succNum B4 (succNum B4 (succDigit B6)))

  let plusConst = 35
  let pc = (s :> ISuccAddBuilder<_>).PlusConst plusConst
  let neg = (s :> ISuccAddBuilder<_>).Neg
  let add = (s :> ISuccAddBuilder<_>).AddMultiple 1
  exportSymIso add
  // let iso = ReversibleArith.Iso.Operators.(>>>) pc neg
  printfn "-"
  let nAdd = 
    add 
    |> getSymIso 
    |> FromIso.fromSymIso Network.simplify
    |> Network.simplify
    |> Network.canonicalize

  exportGraphviz nAdd
  // runNetwork s n (fun n -> $"-({n} + {plusConst})")
  runNetwork2 s nAdd (fun a b -> $"{a} + {b}") (fun a b -> $"{a}, {b}")

  printfn "-"

  0

