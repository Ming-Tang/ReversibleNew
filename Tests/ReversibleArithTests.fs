module Reversible.ReversibleArithTests

open ReversibleArith.Num
open FsCheck
open FsCheck.Xunit
open ReversibleArith.Iso
open ReversibleArith.NumIso

type Num0 = Num0 of Digit<B10>
type Num1 = Num1 of Num<B6, Num<B10, Digit<B8>>>
type Num2 = Num2 of Num<B9, Num<B5, Num<B6, Digit<B7>>>>

let genBase i =
  Gen.choose (2, max 2 i) 
  |> Gen.map mkBase

let rec listGen xs =
  gen {
    match xs with
    | [] -> return []
    | x :: xs ->
      let! x' = x
      let! xs' = listGen xs
      return x' :: xs'
  }

let rec listWithProd n =
  gen {
    if n <= 2 then
      return [2]
    else
      let! a = Gen.choose (2, min n 32)
      let! xs = listWithProd (n / a)
      return a :: xs
  }

type Generators =
  static member Base() =
    Gen.sized genBase
    |> Arb.fromGen

  static member Num0() =
    gen {
      let! a = Gen.choose (0, 9)
      return Digit(a, B10)
    }
    |> Arb.fromGen

  static member Num1() =
    Gen.sized (fun i ->
      gen {
        let! a = Gen.choose (0, 8)
        let! b = Gen.choose (0, 4)
        let! c = Gen.choose (0, 5)
        let! d = Gen.choose (0, 6)
        return Num2(Num(Digit(a, B9), Num(Digit(b, B5), Num(Digit(c, B6), Digit(c, B7)))))
      }
      |> Gen.filter (fun (Num2 n) -> numberValue n <= pown 2 (2 + min 16 i))
    )
    |> Arb.fromGen

  static member Num2() =
    Gen.sized (fun i ->
      gen {
        let! a = Gen.choose (0, 5)
        let! b = Gen.choose (0, 9)
        let! c = Gen.choose (0, 7)
        return Num1(Num(Digit(a, B6), Num(Digit(b, B10), Digit(c, B8))))
      }
      |> Gen.filter (fun (Num1 n) -> numberValue n <= pown 2 (2 + min 16 i))
    )
    |> Arb.fromGen

  static member Num() =
    Gen.sized (fun n -> 
      gen {
        let! bs' = listWithProd n
        let bs = List.map mkBase bs'
        let! ds = listGen <| List.map (fun n -> Gen.choose (0, getBase n - 1)) bs
        return
          List.zip ds bs
          |> Seq.fold (fun o (d, b) -> 
            match o with
            | None -> Some (Digit(d, b) :> INum)
            | Some n -> Some (Num(Digit(d, b), n) :> INum)
          ) None
          |> Option.get
      }
      |> Gen.filter (fun n ->
        try
          ignore (n.Mod)
          true
        with
        | :? System.OverflowException -> false
      ))
    |> Arb.fromGen

[<Properties(Arbitrary = [| typeof<Generators> |], MaxTest = 1000)>]
module NumTests =
  [<Property>]
  let ``product of Bases = Mod = Base``(n : INum) =
    let a = List.fold (Checked.(*)) 1 n.Bases
    let b = n.Mod
    let c = n.Base
    sprintf "prod=%A Mod=%A Base=%A" a b c @| (a = b && b = c)

  [<Property>]
  let ``NumberValue is within range of Mod``(n : INum) =
    sprintf "nv=%A mod=%d bs=%A" n.NumberValue n.Mod n.Bases @| (
      (n.NumberValue >= 0) && (n.NumberValue < n.Mod)
    )

  [<Property>]
  let ``NumberValue = Unmap Map``(n : INum) =
    let nv = Some n.NumberValue
    let unmap = n.Unmap(n.Map n.NumberValue)
    sprintf "NumberValue=%A Unmap Map=%A" nv unmap @| (nv = unmap)

[<Properties(Arbitrary = [| typeof<Generators> |], MaxTest = 1000)>]
module IsoTests =
  let succNum0 = succDigit B10
  let succNum1 = succNum B6 (succNum B10 <| succDigit B8)
  let succNum2 = succNum B9 (succNum B5 (succNum B6 <| succDigit B7))

  [<Property>]
  let ``succ n = n + 1 mod B``(Num1 n) =
    let num, m = numberValue n, modValue n
    let succ = (succNum1 :> ISuccAddBuilder<_>).Succ
    let expected = (num + 1) % m
    let actual = numberValue (succ <<| n)
    sprintf "%A : %A = %A" num expected actual @| (expected = actual)

  [<Property>]
  let ``plusConst k n = n + k mod B: single digit``(Num0 n, k : int) =
    let num, m = numberValue n, modValue n
    let plusConst = (succNum0 :> ISuccAddBuilder<_>).PlusConst k
    let expected = (num + (k % m) + m) % m
    let actual = numberValue (plusConst <<| n)
    sprintf "%A : %A = %A" num expected actual @| (expected = actual)

  [<Property>]
  let ``plusConst k n = n + k mod B``(Num1 n, k : int) =
    let num, m = numberValue n, modValue n
    let plusConst = (succNum1 :> ISuccAddBuilder<_>).PlusConst k
    let expected = (num + (k % m) + m) % m
    let actual = numberValue (plusConst <<| n)
    sprintf "%A : %A = %A" num expected actual @| (expected = actual)

  [<Property>]
  let ``repeat k (succ n) = (n + k mod B, k)``(Num1 n, Num1 k) =
    let num = (n :> INum).NumberValue
    let sb = (succNum1 :> ISuccAddBuilder<_>)
    let repSucc = sb.Repeat(0, sb.SuccRest)
    let expected = (num + numberValue k) % modValue n, numberValue k
    let p, q = repSucc <<| (n, k)
    let actual = numberValue p, numberValue q
    sprintf "%A : %A = %A" num expected actual @| (expected = actual)

  [<Property>]
  let ``succRest 1 n = n + b0 mod B``(Num1 n) =
    let num = numberValue n
    let succ1 = (succNum1 :> ISuccAddBuilder<_>).SuccRest 1
    let succ2 = (succNum1 :> ISuccAddBuilder<_>).SuccRest 2
    let expected = ((num + 6) % modValue n, (num + 6 * 10) % modValue n)
    let actual = numberValue (succ1 <<| n), numberValue (succ2 <<| n)
    sprintf "%A : %A = %A" num expected actual @| (expected = actual)

  [<Property>]
  let ``pred n = n - 1 mod B``(Num1 n) =
    let num = numberValue n
    let pred = sym (succNum1 :> ISuccAddBuilder<_>).Succ
    let expected = (num + modValue n - 1) % modValue n
    let actual = numberValue (pred <<| n)
    sprintf "%A : %A = %A" num expected actual @| (expected = actual)

  [<Property>]
  let ``addMultiple k (m, n) = (m + k * n mod B, n)``(Num1 m, Num1 n, k : int) =
    let num1, num2, b = numberValue m, numberValue n, modValue m
    let add = (succNum1 :> ISuccAddBuilder<_>).AddMultiple k
    let expected = (num1 + ((k * num2 + b) % b) + b) % b, num2
    let actual1, actual2 = add <<| (m, n)
    let actual = numberValue actual1, numberValue actual2
    sprintf "%A : %A = %A" (num1, k, num2) expected actual @| (expected = actual)

  [<Property>]
  let ``addMultiple k (m, n) = (m + k * n mod B, n): different bases (B = base M)``(Num2 m, Num1 n, k : int) =
    let num1, num2, b = numberValue m, numberValue n, modValue m
    let add = (succNum1 :> ISuccAddBuilder<_>).AddMultiple'(succNum2, k)
    let expected = (num1 + ((k * num2 + b) % b) + b) % b, num2
    let actual1, actual2 = add <<| (m, n)
    let actual = numberValue actual1, numberValue actual2
    sprintf "%A : %A = %A" (num1, k, num2) expected actual @| (expected = actual)

  [<Property>]
  let ``add(m, n) = (m + n mod B, n)``(Num1 m, Num1 n) =
    let num1, num2 = numberValue m, numberValue n
    let add = (succNum1 :> ISuccAddBuilder<_>).Add
    let expected = (num1 + num2) % modValue n, num2
    let actual1, actual2 = add <<| (m, n)
    let actual = numberValue actual1, numberValue actual2
    sprintf "%A : %A = %A" (num1, num2) expected actual @| (expected = actual)

  [<Property>]
  let ``sub(m, n) = (m - n mod B, n)``(Num1 m, Num1 n) =
    let num1, num2, b = numberValue m, numberValue n, modValue m
    let add = sym (succNum1 :> ISuccAddBuilder<_>).Add
    let expected = (num1 - num2 + b) % b, num2
    let actual1, actual2 = add <<| (m, n)
    let actual = numberValue actual1, numberValue actual2
    sprintf "%A : %A = %A" (num1, num2) expected actual @| (expected = actual)

  [<Property>]
  let ``neg (neg n) = n``(Num1 n) =
    let neg = sym (succNum1 :> ISuccAddBuilder<_>).Neg
    let expected = numberValue n
    let actual = numberValue ((neg >>> neg) <<| n)
    sprintf "%A : %A = %A" num expected actual @| (expected = actual)

  [<Property>]
  let ``fst sub(m, n) = fst add(m, neg(n)): single digit``(Num0 m, Num0 n) =
    let num1, num2 = numberValue m, numberValue n
    let add = (succNum0 :> ISuccAddBuilder<_>).Add
    let sub = sym (succNum0 :> ISuccAddBuilder<_>).Add
    let neg = (succNum0 :> ISuccAddBuilder<_>).Neg
    let expected = sub <<| (m, n)
    let actual = ((id &&& neg) >>> add >>> (id &&& neg)) <<| (m, n)
    sprintf "%A : %A = %A" (num1, num2) expected actual @| (expected = actual)

  [<Property>]
  let ``fst sub(m, n) = fst add(m, neg(n))``(Num1 m, Num1 n) =
    let num1, num2 = numberValue m, numberValue n
    let add = (succNum1 :> ISuccAddBuilder<_>).Add
    let sub = sym (succNum1 :> ISuccAddBuilder<_>).Add
    let neg = (succNum1 :> ISuccAddBuilder<_>).Neg
    let expected = sub <<| (m, n)
    let actual = ((id &&& neg) >>> add >>> (id &&& neg)) <<| (m, n)
    sprintf "%A : %A = %A" (num1, num2) expected actual @| (expected = actual)

  [<Property>]
  let ``mult(a, m, n) = (a + m * n mod B, m, n)``(Num1 a, Num1 m, Num1 n) =
    let num0, num1, num2 = numberValue a, numberValue m, numberValue n
    let mult = (succNum1 :> ISuccAddBuilder<_>).Mult
    let expected = (num0 + num1 * num2) % modValue n, (num1, num2)
    let actual0, (actual1, actual2) = mult <<| (a, (m, n))
    let actual = numberValue actual0, (numberValue actual1, numberValue actual2)
    sprintf "%A : %A = %A" (num0, (num1, num2)) expected actual @| (expected = actual)

  [<Property>]
  let ``mult(a, m, n) = (a + m * n mod B, m, n): different bases``(Num1 a, Num1 m, Num2 n) =
    let num0, num1, num2 = numberValue a, numberValue m, numberValue n
    let mult = (succNum2 :> ISuccAddBuilder<_>).Mult'(succNum1)
    let expected = (num0 + num1 * num2) % modValue a, (num1, num2)
    let actual0, (actual1, actual2) = mult <<| (a, (m, n))
    let actual = numberValue actual0, (numberValue actual1, numberValue actual2)
    sprintf "%A : %A = %A" (num0, (num1, num2)) expected actual @| (expected = actual)

  [<Property>]
  let ``mult(a, m, n) = (a + m * n mod B, m, n): different bases 2``(Num1 a, Num2 m, Num2 n) =
    let num0, num1, num2 = numberValue a, numberValue m, numberValue n
    let mult = (succNum2 :> ISuccAddBuilder<_>).Mult''(succNum2, succNum1)
    let expected = (num0 + num1 * num2) % modValue a, (num1, num2)
    let actual0, (actual1, actual2) = mult <<| (a, (m, n))
    let actual = numberValue actual0, (numberValue actual1, numberValue actual2)
    sprintf "%A : %A = %A" (num0, (num1, num2)) expected actual @| (expected = actual)

