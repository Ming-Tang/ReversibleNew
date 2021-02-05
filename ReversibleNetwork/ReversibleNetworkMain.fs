module Main
open System.IO
open System.Diagnostics
open ReversibleNetwork
open Builders
open Builders.Operators
open Simulator
open ReversibleArith.Iso
open ReversibleArith.Num
open ReversibleArith.NumIso

[<EntryPoint>]
let main argv =
  let s = succNum B2 (succNum B2 (succNum B2 (succNum B2 (succNum B2 (succDigit B2)))))
  // let iso = (s :> ISuccAddBuilder<_>).AddMultiple 7
  let plusConst = 9
  let iso = (s :> ISuccAddBuilder<_>).PlusConst plusConst
  printfn "-"
  let n = 
    iso 
    |> getSymIso 
    |> FromIso.fromSymIso (fun x -> x) // Network.simplify
    |> Network.canonicalize

  let ds = getDepths n
  let maxDepth = ds |> Seq.map ((|KeyValue|) >> snd) |> Seq.max
  printfn $"vertices={n.Vertices.Count} edges={n.Edges.Count} splits={n.Splits.Count} maxDepth={maxDepth}"

  let sim = Simulator(n)
  for x in 0 .. 1000 do
    for n1 in 0 .. 63 do
      let input = [| 
        for k in [2; 4; 8; 16; 32; 64] do
          yield (n1 % k) / (k / 2) = 0
          yield (n1 % k) / (k / 2) = 1
      |]
      //printfn "%A" input
      let num0 = fromDigits s <| fromBools s input
      let n1 = sim.Evaluate(input)
      //n1
      //|> printfn "%A"
      let num1 = fromDigits s <| fromBools s n1
      ()
      //printfn $"{numberValue num0} + {plusConst} = {numberValue num1} (mod {modValue num1})"

  printfn "-"

  do
    let graphviz = 
      n
      |> Network.toGraphviz (fun v -> $"""{String.concat "." v}:{ds.[v]}""") 
      |> sprintf "%s"
    File.WriteAllText("input.dot", graphviz)
    let p = Process.Start("dot", "-Tsvg input.dot -o output.svg")
    p.WaitForExit()

  printfn "-"

  0

