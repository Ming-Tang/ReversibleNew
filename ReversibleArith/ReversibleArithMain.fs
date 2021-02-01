module ReversibleArith.Main
open Iso
open Iso.Operators
open Num
open NumIso

[<EntryPoint>]
let main argv =
  let sfl = succFromList [16; 8; 3; 4; 5]
  printfn "%A %A" sfl (sfl.NumFromList([3; 5; 1; 0; 2]))

  let s = succNum B10 (succNum B10 (succNum B10 (succDigit B10)))
  let s' = succNum B8 (succDigit B6)
  let s'' = succNum B4 (succNum B5 (succDigit B6))
  let sn = (s :> ISuccAddBuilder<_>).Succ
  let addn = (s :> ISuccAddBuilder<_>).Add
  let pcn = (s :> ISuccAddBuilder<_>).PlusConst(47)

  let multn = (s'' :> ISuccAddBuilder<_>).Mult''(s', s)
  printfn "%A" <| numberValue (Num(Digit(2, B10), Num(Digit(3, B10), Digit(4, B10))))
  printfn "%A" <| (add B10 <<| (Digit(7, B10), Digit(6, B10)))
  printfn "%A" <| (mult B10 <<| ((Digit(2, B10), Digit(3, B10)), Digit(4, B10)))

  let d5499 = Num(Digit(9, B10), Num(Digit(9, B10), Num(Digit(4, B10), Digit(5, B10))))
  let d1237 = Num(Digit(7, B10), Num(Digit(3, B10), Num(Digit(2, B10), Digit(1, B10))))
  printfn "%A" <| (sn <<| d5499)
  printfn "%A" <| (addn <<| (d5499, d1237))
  printfn "%A" <| (addn <<| (d1237, d5499))

  printfn ""
  printfn "# Successor"
  printfn "$$%s$$" (showBIso None sn)

  printfn ""
  printfn "# + Const"
  printfn "$$%s$$" (showBIso None pcn)

  printfn ""
  printfn "# Add"
  printfn "$$%s$$" (showBIso None addn)

  printfn ""
  printfn "# Mult"
  printfn "$$%s$$" (showBIso None multn)

  // printfn ""
  // printfn ""
  // printfn "%s" (showBIso' sn)
  // printfn "%s" (showBIso' addn)
  0 // return an integer exit code

