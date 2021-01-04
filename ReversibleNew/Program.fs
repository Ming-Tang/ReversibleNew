open Reversible
open Reversible.RType
open Reversible.Machine
open Reversible.MachineState

let showState x =
  x |> Seq.map (Array.toList >> showWires) |> Seq.iter (printfn "%s")
[<EntryPoint>]
let main argv =

  printfn "%A" (MachineBuilder.Tn TDir.PlusMinus 3)
  let inputs = [|
    [| false; false |]
    [| false; true |]
    [| true; false |]
    [| true; true |]
  |]
  runMachine (MachineBuilder.Tn TDir.PlusMinus 1) inputs
  |> showState
  printfn ""

  vstack (Block [[Identity 3]; [Identity 3]]) (Block [[Identity 3]; [TGate PlusMinus; Identity 1]; [Permute <| Perm.create [|1;2;0;3|]]])
  |> printfn "%A"
  printfn ""

  //let b1 = Block [[Identity 1; Permute (Perm.reverse 5); Identity 1]; [Identity 7]]
  let b1 = (Block [[Identity 1; Identity 1; Identity 1]; [Identity 1; TGate PlusMinus];
                   [TGate PlusMinus; Identity 1; Identity 1]])
  let ms = MachineState(Machine.hstack b1 (Machine.inverse b1))
  printfn "%A" <| ms.Evaluate(
    [|
      [| true; false; false |]
      [| false; true; false |]
      [| false; false; true |]
      [| true; true; false |]
      [| true; false; true |]
      [| false; true; true |]
      [| true; true; true |]
    |] 
  )

  printfn "---------"
  let ms = MachineState(Machine.hstack b1 (Machine.inverse b1))
  printfn "%A" ms.Block
  //ms.State.[0] <- [| true; false; false; true; false; true; true |]
  for i in 1 .. Machine.depth ms.Block do
    if i = 1 then
      ms.State.[0] <- [| true; false; false |]
    elif i = 2 then
      ms.State.[0] <- [| false; true; false |]
    elif i = 3 then
      ms.State.[0] <- [| false; false; true |]
    elif i = 4 then
      ms.State.[0] <- [| true; true; false |]
    elif i = 5 then
      ms.State.[0] <- [| true; false; true |]

    ms.State |> showState
    printfn ""
    ms.Step()

  printfn "----------"
  for i in 1 .. 5 do
    ms.State |> Seq.last |> Seq.singleton |> showState
    ms.Step()
    
#if FALSE
  combs 7 3
  |> Seq.map showWires
  |> Seq.iter (printfn "%s")
    
  printfn ""
  let t0 = TSum [TSum [B 5 3]; TSum [TProd [B 6 4; B 7 3; TProd [B 2 2]]; B 4 2]]
  printfn "%A" t0
  printfn "%A" (collect t0)
  printfn ""
  let t1 = TSum [TProd [TBinom(5, 3); TBinom(2, 1)]; TBinom(3, 2); TBinom(2, 1)]
  printfn "%A" t1
  printfn "%A" (card t1)
  printfn "%A" (width t1)
  printfn "%A" (count t1)
  printfn ""
    
  vals t1
  |> Seq.map showWires
  |> Seq.iter (printfn "%s")
#endif

  0
    