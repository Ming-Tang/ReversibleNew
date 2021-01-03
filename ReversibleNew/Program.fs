open Reversible
open Reversible.RType
open Reversible.Machine
open Reversible.MachineState

[<EntryPoint>]
let main argv =
  vstack (Block [[Identity 3]; [Identity 3]]) (Block [[Identity 3]; [TGate PlusMinus; Identity 1]; [Permute <| Perm.create [|1;2;0;3|]]])
  |> printfn "%A"
  printfn ""

  //let b1 = Block [[Identity 1; Permute (Perm.reverse 5); Identity 1]; [Identity 7]]
  let b1 = (Block [[Identity 1; Identity 1; Identity 1]; [Identity 1; TGate PlusMinus];
                   [TGate PlusMinus; Identity 1; Identity 1]])
  let ms = MachineState(Machine.hstack b1 (Machine.inverse b1))
  printfn "%A" ms.Block
  //ms.State.[0] <- [| true; false; false; true; false; true; true |]
  ms.State.[0] <- [| false; false; false |]
  for i in 1 .. Machine.depth ms.Block do
    ms.State |> Seq.map (Array.toList >> showWires) |> Seq.iter (printfn "%s")
    printfn ""
    ms.Step()

  printfn ""
    
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
    