module Reversible.ReversibleArithTests

open ReversibleArith.Num
open FsCheck
open FsCheck.Xunit
open ReversibleArith.Iso
open ReversibleArith.Iso.Operators
open ReversibleArith.NumIso

type Bool = Bool of Digit<B2>
type Num0 = Num0 of Digit<B10>
type Num1 = Num1 of Num<B6, Num<B10, Digit<B8>>>
type Num2 = Num2 of Num<B9, Num<B5, Num<B6, Digit<B7>>>>

type SAB1 = SAB1 of ISuccAddBuilder * INum
type SAB2 = SAB2 of ISuccAddBuilder * INum * INum
type SAB3 = SAB3 of ISuccAddBuilder * INum * INum * INum

let genBase i =
  Gen.choose (2, max 2 i) 
  |> Gen.map mkBase

let genWithinBase b = Gen.choose (0, b - 1)

let rec genFromGens xs =
  gen {
    match xs with
    | [] -> return []
    | x :: xs ->
      let! x' = x
      let! xs' = genFromGens xs
      return x' :: xs'
  }

let rec genListWithProd n =
  gen {
    if n <= 2 then
      return [2]
    else
      let! a = Gen.choose (2, min n 32)
      let! xs = genListWithProd (n / a)
      return a :: xs
  }

let genSuccAddBuilder =
  Gen.sized <| fun s ->
    genListWithProd s
    |> Gen.filter (fun x -> 
      let n = List.length x
      n >= 1 && n <= 8
    )
    |> Gen.map (fun l -> l, succFromList l)

type Generators =
  static member Base() =
    Gen.sized genBase
    |> Arb.fromGen

  static member SuccAddBuilder() =
    genSuccAddBuilder
    |> Gen.map snd
    |> Arb.fromGen

  static member SAB1() =
    gen {
      let! bs, sab = genSuccAddBuilder
      let! ds = genFromGens (List.map genWithinBase bs)
      return SAB1(sab, sab.NumFromList(ds))
    }
    |> Arb.fromGen

  static member SAB2() =
    gen {
      let! bs, sab = genSuccAddBuilder
      let! ds1 = genFromGens (List.map genWithinBase bs)
      let! ds2 = genFromGens (List.map genWithinBase bs)
      return SAB2(sab, sab.NumFromList(ds1), sab.NumFromList(ds2))
    }
    |> Arb.fromGen

  static member SAB3() =
    gen {
      let! bs, sab = genSuccAddBuilder
      let! ds1 = genFromGens (List.map genWithinBase bs)
      let! ds2 = genFromGens (List.map genWithinBase bs)
      let! ds3 = genFromGens (List.map genWithinBase bs)
      return SAB3(sab, sab.NumFromList(ds1), sab.NumFromList(ds2), sab.NumFromList(ds3))
    }
    |> Arb.fromGen

  static member Bool() =
    gen {
      let! a = Gen.choose (0, 1)
      return Bool(Digit(a, B2))
    }
    |> Arb.fromGen

  static member Num0() =
    gen {
      let! a = Gen.choose (0, 9)
      return Num0(Digit(a, B10))
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
        let! bs' = genListWithProd n
        let bs = List.map mkBase bs'
        let! ds = genFromGens <| List.map (fun n -> Gen.choose (0, getBase n - 1)) bs
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
          ignore n.Mod
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

  [<Property>]
  let ``fromBools reverses toBools``(n : INum) =
    fromBools n (toBools n) = n.Digits

let inline (.=.) expected actual =
  sprintf "%A = %A" expected actual @| (expected = actual)

[<Properties(Arbitrary = [| typeof<Generators> |], MaxTest = 1000)>]
module IsoTests =
  let succBool = succDigit B2
  let succNum0 = succDigit B10
  let succNum1 = succNum B6 (succNum B10 <| succDigit B8)
  let succNum2 = succNum B9 (succNum B5 (succNum B6 <| succDigit B7))

  [<Property>]
  let ``succ n = n + 1 mod B``(Num1 n) =
    let num, m = numberValue n, modValue n
    let succ = (succNum1 :> ISuccAddBuilder<_>).Succ
    let expected = (num + 1) % m
    let actual = numberValue (succ <<| n)
    expected .=. actual

  [<Property>]
  let ``plusConst k n = n + k mod B: single digit``(Num0 n, k : int) =
    let num, m = numberValue n, modValue n
    let plusConst = (succNum0 :> ISuccAddBuilder<_>).PlusConst k
    let expected = (num + (k % m) + m) % m
    let actual = numberValue (plusConst <<| n)
    expected .=. actual

  [<Property>]
  let ``plusConst k n = n + k mod B``(Num1 n, k : int) =
    let num, m = numberValue n, modValue n
    let plusConst = (succNum1 :> ISuccAddBuilder<_>).PlusConst k
    let expected = (num + (k % m) + m) % m
    let actual = numberValue (plusConst <<| n)
    expected .=. actual

  [<Property>]
  let ``cond: compose property (same)``(Num0 n, Num0 k, Num0 i) =
    let i = numberValue i
    let sb = (succNum0 :> ISuccAddBuilder<_>)
    let f, g = sb.Neg, (sb.Succ >>> sb.Succ)
    let f1 = cond (Digit(i, B10)) f >>> cond (Digit(i, B10)) g
    let f2 = cond (Digit(i, B10)) (f >>> g)

    let expected = f1 <<| (n, k)
    let actual = f2 <<| (n, k)
    expected .=. actual

  [<Property>]
  let ``cond: compose property``(Num0 n, Num0 k, Num0 i, Num0 j) =
    let i, j = numberValue i, numberValue j
    if i = j then 
      false ==> false
    else
      let sb = (succNum0 :> ISuccAddBuilder<_>)
      let f, g = sb.Neg, (sb.Succ >>> sb.Succ)
      let f1 = cond (Digit(i, B10)) f >>> cond (Digit(j, B10)) g
      let f2 = cond (Digit(j, B10)) g >>> cond (Digit(i, B10)) f

      let expected = f1 <<| (n, k)
      let actual = f2 <<| (n, k)
      true ==> (expected .=. actual)

  [<Property>]
  let ``rep: doubling property``(Num0 n, Num0 k) =
    let sb = (succNum0 :> ISuccAddBuilder<_>)
    let f = sb.Succ >>> sb.Succ >>> sb.Neg >>> sb.Compl >>> ~~sb.Succ
    let f1 = rep B10 (f >>> f)
    let f2 = rep B10 f >>> rep B10 f

    let expected = f1 <<| (n, k)
    let actual = f2 <<| (n, k)
    true ==> (expected .=. actual)

  [<Property>]
  let ``rep: doubling property (more digits)``(Num1 n, Num1 m, Num0 k) =
    let sb = (succNum0 :> ISuccAddBuilder<_>)
    let sb1 = (succNum1 :> ISuccAddBuilder<_>)
    let f = sb1.AddMultiple 2
    let f1 = rep B10 (f >>> f)
    let f2 = rep B10 f >>> rep B10 f

    let expected = f1 <<| (k, (n, m))
    let actual = f2 <<| (k, (n, m))
    true ==> (expected .=. actual)

  [<Property>]
  let ``repeat k (succ n) = (n + k mod B, k)``(Num1 n, Num1 k) =
    let num = (n :> INum).NumberValue
    let sb = (succNum1 :> ISuccAddBuilder<_>)
    let repSucc = sb.Repeat(0, sb.SuccRest)
    let expected = (num + numberValue k) % modValue n, numberValue k
    let p, q = repSucc <<| (n, k)
    let actual = numberValue p, numberValue q
    expected .=. actual

  [<Property>]
  let ``succRest 1 n = n + b0 mod B``(Num1 n) =
    let num = numberValue n
    let succ1 = (succNum1 :> ISuccAddBuilder<_>).SuccRest 1
    let succ2 = (succNum1 :> ISuccAddBuilder<_>).SuccRest 2
    let expected = ((num + 6) % modValue n, (num + 6 * 10) % modValue n)
    let actual = numberValue (succ1 <<| n), numberValue (succ2 <<| n)
    expected .=. actual

  [<Property>]
  let ``pred n = n - 1 mod B``(Num1 n) =
    let num = numberValue n
    let pred = sym (succNum1 :> ISuccAddBuilder<_>).Succ
    let expected = (num + modValue n - 1) % modValue n
    let actual = numberValue (pred <<| n)
    expected .=. actual

  [<Property>]
  let ``addMultiple k (m, n) = (m + k * n mod B, n)``(Num1 m, Num1 n, k : int) =
    let num1, num2, b = numberValue m, numberValue n, modValue m
    let add = (succNum1 :> ISuccAddBuilder<_>).AddMultiple k
    let expected = (num1 + ((k * num2 + b) % b) + b) % b, num2
    let actual1, actual2 = add <<| (m, n)
    let actual = numberValue actual1, numberValue actual2
    expected .=. actual

  [<Property>]
  let ``addMultiple k (m, n) = (m + k * n mod B, n): different bases (B = base M)``(Num2 m, Num1 n, k : int) =
    let num1, num2, b = numberValue m, numberValue n, modValue m
    let add = (succNum1 :> ISuccAddBuilder<_>).AddMultipleB(succNum2, k)
    let expected = (num1 + ((k * num2 + b) % b) + b) % b, num2
    let actual1, actual2 = add <<| (m, n)
    let actual = numberValue actual1, numberValue actual2
    expected .=. actual

  [<Property>]
  let ``add(m, n) = (m + n mod B, n)``(Num1 m, Num1 n) =
    let num1, num2 = numberValue m, numberValue n
    let add = (succNum1 :> ISuccAddBuilder<_>).Add
    let expected = (num1 + num2) % modValue n, num2
    let actual1, actual2 = add <<| (m, n)
    let actual = numberValue actual1, numberValue actual2
    expected .=. actual

  [<Property>]
  let ``sub(m, n) = (m - n mod B, n)``(Num1 m, Num1 n) =
    let num1, num2, b = numberValue m, numberValue n, modValue m
    let add = sym (succNum1 :> ISuccAddBuilder<_>).Add
    let expected = (num1 - num2 + b) % b, num2
    let actual1, actual2 = add <<| (m, n)
    let actual = numberValue actual1, numberValue actual2
    expected .=. actual

  [<Property>]
  let ``neg n = -n mod B``(Num1 n) =
    let neg = sym (succNum1 :> ISuccAddBuilder<_>).Neg
    let expected = (modValue n - numberValue n) % modValue n
    let actual = numberValue (neg <<| n)
    expected .=. actual

  [<Property>]
  let ``neg (neg n) = n``(Num1 n) =
    let neg = sym (succNum1 :> ISuccAddBuilder<_>).Neg
    let expected = numberValue n
    let actual = numberValue ((neg >>> neg) <<| n)
    expected .=. actual

  [<Property>]
  let ``fst add(m, n) = fst add(n, m)``(Num1 m, Num1 n) =
    let num1, num2 = numberValue m, numberValue n
    let add = (succNum1 :> ISuccAddBuilder<_>).Add
    let expected = fst (add <<| (m, n))
    let actual = fst (add <<| (n, m))
    expected .=. actual

  [<Property>]
  let ``fst sub(m, n) = fst add(m, neg(n)): single digit``(Num0 m, Num0 n) =
    let num1, num2 = numberValue m, numberValue n
    let add = (succNum0 :> ISuccAddBuilder<_>).Add
    let sub = sym (succNum0 :> ISuccAddBuilder<_>).Add
    let neg = (succNum0 :> ISuccAddBuilder<_>).Neg
    let expected = sub <<| (m, n)
    let actual = ((id &&& neg) >>> add >>> (id &&& neg)) <<| (m, n)
    expected .=. actual

  [<Property>]
  let ``fst sub(m, n) = fst add(m, neg(n))``(Num1 m, Num1 n) =
    let num1, num2 = numberValue m, numberValue n
    let add = (succNum1 :> ISuccAddBuilder<_>).Add
    let sub = sym (succNum1 :> ISuccAddBuilder<_>).Add
    let neg = (succNum1 :> ISuccAddBuilder<_>).Neg
    let expected = sub <<| (m, n)
    let actual = ((id &&& neg) >>> add >>> (id &&& neg)) <<| (m, n)
    expected .=. actual

  [<Property>]
  let ``mult(a, m, n) = (a + m * n mod B, m, n)``(Num1 a, Num1 m, Num1 n) =
    let num0, num1, num2 = numberValue a, numberValue m, numberValue n
    let mult = (succNum1 :> ISuccAddBuilder<_>).Mult
    let expected = (num0 + num1 * num2) % modValue n, (num1, num2)
    let actual0, (actual1, actual2) = mult <<| (a, (m, n))
    let actual = numberValue actual0, (numberValue actual1, numberValue actual2)
    expected .=. actual

  [<Property>]
  let ``mult(a, m, n) = (a + m * n mod B, m, n): different bases``(Num1 a, Num1 m, Num2 n) =
    let num0, num1, num2 = numberValue a, numberValue m, numberValue n
    let mult = (succNum2 :> ISuccAddBuilder<_>).MultB(succNum1)
    let expected = (num0 + num1 * num2) % modValue a, (num1, num2)
    let actual0, (actual1, actual2) = mult <<| (a, (m, n))
    let actual = numberValue actual0, (numberValue actual1, numberValue actual2)
    expected .=. actual

  [<Property>]
  let ``mult(a, m, n) = (a + m * n mod B, m, n): different bases 2``(Num1 a, Num2 m, Num2 n) =
    let num0, num1, num2 = numberValue a, numberValue m, numberValue n
    let mult = (succNum2 :> ISuccAddBuilder<_>).MultB2(succNum2, succNum1)
    let expected = (num0 + num1 * num2) % modValue a, (num1, num2)
    let actual0, (actual1, actual2) = mult <<| (a, (m, n))
    let actual = numberValue actual0, (numberValue actual1, numberValue actual2)
    expected .=. actual

[<Properties(Arbitrary = [| typeof<Generators> |], MaxTest = 1000)>]
module IsoTestsSAB =
  [<Property>]
  let ``succ n = n + 1 mod B``(SAB1(sab, n)) =
    let num, m = numberValue n, modValue n
    let succ = sab.Succ'
    let expected = (num + 1) % m
    let actual = numberValue (succ <<| n)
    expected .=. actual

#if FALSE
  [<Property>]
  let ``plusConst k n = n + k mod B: single digit``(SAB1(sab, n), k : int) =
    let num, m = numberValue n, modValue n
    let plusConst = sab.PlusConst k
    let expected = (num + (k % m) + m) % m
    let actual = numberValue (plusConst <<| n)
    expected .=. actual

  [<Property>]
  let ``repeat k (succ n) = (n + k mod B, k)``(SAB2(sab, n, k)) =
    let num = numberValue n
    let sb = sab
    let repSucc = sb.Repeat(0, sb.SuccRest)
    let expected = (num + numberValue k) % modValue n, numberValue k
    let p, q = repSucc <<| (n, k)
    let actual = numberValue p, numberValue q
    expected .=. actual

  [<Property>]
  let ``succRest 1 n = n + b0 mod B``(SAB1(sab, n)) =
    let num = numberValue n
    let succ1 = sab.SuccRest 1
    let succ2 = sab.SuccRest 2
    let expected = ((num + 6) % modValue n, (num + 6 * 10) % modValue n)
    let actual = numberValue (succ1 <<| n), numberValue (succ2 <<| n)
    expected .=. actual
#endif

  [<Property>]
  let ``pred n = n - 1 mod B``(SAB1(sab, n)) =
    let num = numberValue n
    let pred = sym sab.Succ'
    let expected = (num + modValue n - 1) % modValue n
    let actual = numberValue (pred <<| n)
    expected .=. actual

#if FALSE
  [<Property>]
  let ``addMultiple k (m, n) = (m + k * n mod B, n)``(SAB2(sab, m, n), k : int) =
    let num1, num2, b = numberValue m, numberValue n, modValue m
    let add = sab.AddMultiple k
    let expected = (num1 + ((k * num2 + b) % b) + b) % b, num2
    let actual1, actual2 = add <<| (m, n)
    let actual = numberValue actual1, numberValue actual2
    expected .=. actual

  [<Property>]
  let ``addMultiple k (m, n) = (m + k * n mod B, n): different bases (B = base M)``(SAB1(sab1, m), SAB1(sab2, n), k : int) =
    let num1, num2, b = numberValue m, numberValue n, modValue m
    let add = sab1.AddMultiple'(sab2, k)
    let expected = (num1 + ((k * num2 + b) % b) + b) % b, num2
    let actual1, actual2 = add <<| (m, n)
    let actual = numberValue actual1, numberValue actual2
    expected .=. actual

  [<Property>]
  let ``add(m, n) = (m + n mod B, n)``(SAB2(sab, m, n)) =
    let num1, num2 = numberValue m, numberValue n
    let add = sab.Add
    let expected = (num1 + num2) % modValue n, num2
    let actual1, actual2 = add <<| (m, n)
    let actual = numberValue actual1, numberValue actual2
    expected .=. actual

  [<Property>]
  let ``sub(m, n) = (m - n mod B, n)``(SAB2(sab, m, n)) =
    let num1, num2, b = numberValue m, numberValue n, modValue m
    let add = sym sab.Add
    let expected = (num1 - num2 + b) % b, num2
    let actual1, actual2 = add <<| (m, n)
    let actual = numberValue actual1, numberValue actual2
    expected .=. actual

  [<Property>]
  let ``neg (neg n) = n``(SAB1(sab, n)) =
    let neg = sym sab.Neg
    let expected = numberValue n
    let actual = numberValue ((neg >>> neg) <<| n)
    expected .=. actual

  [<Property>]
  let ``fst sub(m, n) = fst add(m, neg(n)): single digit``(SAB2(sab, m, n)) =
    let num1, num2 = numberValue m, numberValue n
    let add = sab.Add
    let sub = sym sab.Add
    let neg = sab.Neg
    let expected = sub <<| (m, n)
    let actual = ((id &&& neg) >>> add >>> (id &&& neg)) <<| (m, n)
    expected .=. actual

  [<Property>]
  let ``fst sub(m, n) = fst add(m, neg(n))``(SAB2(sab, m, n)) =
    let num1, num2 = numberValue m, numberValue n
    let add = sab.Add
    let sub = sym sab.Add
    let neg = sab.Neg
    let expected = sub <<| (m, n)
    let actual = ((id &&& neg) >>> add >>> (id &&& neg)) <<| (m, n)
    expected .=. actual

  [<Property>]
  let ``mult(a, m, n) = (a + m * n mod B, m, n)``(SAB3(sab, a, m, n)) =
    let num0, num1, num2 = numberValue a, numberValue m, numberValue n
    let mult = sab.Mult
    let expected = (num0 + num1 * num2) % modValue n, (num1, num2)
    let actual0, (actual1, actual2) = mult <<| (a, (m, n))
    let actual = numberValue actual0, (numberValue actual1, numberValue actual2)
    expected .=. actual

  [<Property>]
  let ``mult(a, m, n) = (a + m * n mod B, m, n): different bases``(SAB2(sab1, a, m), SAB1(sab2, n)) =
    let num0, num1, num2 = numberValue a, numberValue m, numberValue n
    let mult = sab2.Mult'(sab1)
    let expected = (num0 + num1 * num2) % modValue a, (num1, num2)
    let actual0, (actual1, actual2) = mult <<| (a, (m, n))
    let actual = numberValue actual0, (numberValue actual1, numberValue actual2)
    expected .=. actual

  [<Property>]
  let ``mult(a, m, n) = (a + m * n mod B, m, n): different bases 2``(SAB1(sab1, a), SAB2(sab2, m, n)) =
    let num0, num1, num2 = numberValue a, numberValue m, numberValue n
    let mult = sab2.Mult''(succNum2, succNum1)
    let expected = (num0 + num1 * num2) % modValue a, (num1, num2)
    let actual0, (actual1, actual2) = mult <<| (a, (m, n))
    let actual = numberValue actual0, (numberValue actual1, numberValue actual2)
    expected .=. actual
#endif
