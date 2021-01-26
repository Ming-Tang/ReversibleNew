module ReversibleArith.Main
open Iso
open Num
open NumIso

[<EntryPoint>]
let main argv =
  let s = succNum B10 (succNum B10 (succNum B10 (succDigit B10)))
  let sn = (s :> SuccBuilder<_>).Succ
  let addn = (s :> AddBuilder<_>).Add
  printfn "%A" <| numberValue (Num(Digit(2, B10), Num(Digit(3, B10), Digit(4, B10))))
  printfn "%A" <| (add B10 <<| (Digit(7, B10), Digit(6, B10)))
  printfn "%A" <| (mult B10 <<| ((Digit(2, B10), Digit(3, B10)), Digit(4, B10)))

  let d5499 = Num(Digit(9, B10), Num(Digit(9, B10), Num(Digit(4, B10), Digit(5, B10))))
  let d1237 = Num(Digit(7, B10), Num(Digit(3, B10), Num(Digit(2, B10), Digit(1, B10))))
  printfn "%A" <| (sn <<| d5499)
  printfn "%A" <| (addn <<| (d5499, d1237))
  printfn "%A" <| (addn <<| (d1237, d5499))

  printfn ""
  printfn ""
  printfn "%s" (showBIso None sn)
  printfn "\\\\"
  printfn "%s" (showBIso None addn)

  // printfn ""
  // printfn ""
  // printfn "%s" (showBIso' sn)
  // printfn "%s" (showBIso' addn)
  0 // return an integer exit code

