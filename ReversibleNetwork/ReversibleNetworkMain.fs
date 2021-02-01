module Main
open ReversibleNetwork
open Builders
open Builders.Operators
open ReversibleArith.Iso
open ReversibleArith.Num
open ReversibleArith.NumIso

[<EntryPoint>]
let main argv =
  let s = succNum B2 (succDigit B2)
  let iso = (s :> ISuccAddBuilder<_>).AddMultiple 1
  let n = 
    iso 
    |> getSymIso 
    |> FromIso.fromSymIso Network.canonicalize

  n
  |> Network.toGraphviz
  |> printfn "%s"
  printfn ""

  0

