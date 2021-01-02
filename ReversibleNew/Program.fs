open Reversible
open Reversible.RType

[<EntryPoint>]
let main argv =
  Perm.create [1; 3; 2; 0]
  |> Perm.expand [5; 3; 2; 1]
  |> Array.ofSeq
  |> Perm.create
  |> printfn "%A"
    
  printfn "%A" (Perm.create [3; 1; 0; 4; 2])
  printfn "%A" (Perm.create [3; 1; 0; 4; 2] |> Perm.invert)
  printfn "%A" (Perm.create [3; 1; 0; 4; 2] |> Perm.invert |> Perm.invert)
  printfn "%A" (Perm.create [0; 1; 2; 3])
    
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
  0
    