module Reversible.ReversibleNetworkTests

open ReversibleNetwork
open Builders
open Operators
open FsCheck
open FsCheck.Xunit
open ReversibleArith.Num

type ComposedNetwork = ComposedNetwork of Network
type SymmetricComposedNetwork = SCN of Network
type SymmetricComposedNetworkPair = SCNPair of Network * Network

type Size = Size of int

let genPerm n =
  gen {
    let a = Array.init n id
    let! a' = Gen.shuffle a
    return fromPerm a'
  }

let genComposePadded ({ Outputs = o } as f) ({ Inputs = i } as g) =
  let no, ni = o.Length, i.Length
  let d = abs (ni - no)
  gen {
    if ni = no then
      return f >>> g
    elif ni > no then
      let! f' = Gen.elements [
        f &&& identity d
        identity d &&& f
      ]
      return f' >>> g
    else
      let! g' = Gen.elements [
        g &&& identity d
        identity d &&& g
      ]
      return f >>> g'
  }

let rec genNetwork (n, m) =
  if n <= 1 then
    gen { return identity 1 }
  elif m <= 2 then
    genPerm n
  else
    gen {
      let! i = Gen.choose (0, 3)
      if i = 3 then
        return multiplex (max 1 (n / 2))
      elif i = 2 then
        let! a = Gen.choose (1, n)
        let! p = genNetwork (a, m)
        let! q = genNetwork (n - a, m)
        return p &&& q
      elif i = 1 then
        let! p = genNetwork (n, m - 1)
        return ~~p
      else
        let! f = genNetwork (n, m / 2)
        let! g = genNetwork (n, m / 2)
        return! genComposePadded f g
    }
  
let (.=.) a b =
  let ca = a |> Network.canonicalize
  let cb = b |> Network.canonicalize
  if ca = cb then
    "" @| true
  else
    $"%A{ca} .=. %A{cb}" @| false

type Generators() =
  static member ComposedNetwork() =
    Gen.sized (fun n -> 
      gen {
        let! p = Gen.choose (1, max 1 n)
        return! Gen.map ComposedNetwork <| genNetwork (p, n / p)
      }
    )
    |> Arb.fromGen

  static member SymmetricComposedNetwork() =
    Gen.sized (fun n -> 
      gen {
        let! p = Gen.choose (1, max 1 n)
        return! genNetwork (p, n / p)
      }
      |> Gen.filter (fun n -> n.Inputs.Length = n.Outputs.Length)
      |> Gen.map SCN
    )
    |> Arb.fromGen

  static member SymmetricComposedNetworkPair() =
    Gen.sized (fun n -> 
      gen {
        let! p1 = Gen.choose (1, max 1 n)
        let! p2 = Gen.choose (1, max 1 n)
        return! Gen.map2 (fun i j -> i, j) (genNetwork (p1, n / p1)) (genNetwork (p2, n / p2))
      }
      |> Gen.filter (fun (n1, n2) -> 
        n1.Inputs.Length = n1.Outputs.Length
        && n2.Inputs.Length = n2.Outputs.Length
        && n1.Inputs.Length = n2.Inputs.Length
      )
      |> Gen.map SCNPair
    )
    |> Arb.fromGen

  static member Size() =
    Gen.sized (fun n ->
      Gen.choose (1, max 1 <| min 10 n)
      |> Gen.map Size
    )
    |> Arb.fromGen

[<Properties(Arbitrary = [| typeof<Generators> |], MaxTest = 1000)>]
module ReversibleNetworkTests =
  [<Property>]
  let ``No broken refs``(ComposedNetwork n) =
    Network.brokenRefs n = (Set.empty, Set.empty)

  [<Property>]
  let ``No broken refs: canonicalize``(ComposedNetwork n) =
    Network.brokenRefs (Network.relabel n) = (Set.empty, Set.empty)

  [<Property>]
  let ``simplify: idempotent``(ComposedNetwork n) =
    Network.simplify (Network.simplify n) = Network.simplify n

  [<Property>]
  let ``relabel: idempotent``(ComposedNetwork n) =
    Network.relabel (Network.relabel n) .=. Network.relabel n

  [<Property>]
  let ``canonicalize: idempotent``(ComposedNetwork n) =
    Network.canonicalize (Network.canonicalize n) .=. Network.canonicalize n

  [<Property>]
  let ``inverse: double inverse``(ComposedNetwork n) =
    inverse (inverse n) .=. n

#if FALSE
  [<Property>]
  let ``inverse: composition = identity A``(ComposedNetwork n) =
    (n >>> (inverse n)) .=. identity n.Inputs.Length

  [<Property>]
  let ``inverse: composition = identity B``(ComposedNetwork n) =
    (inverse n >>> n) .=. identity n.Inputs.Length
#endif

  [<Property>]
  let ``reverse: self-inverse``(Size a) =
    reverse a .=. ~~(reverse a)

  [<Property>]
  let ``reverse: compose with its inverse``(Size a) =
    (reverse a >>> reverse a) .=. buffer a

  [<Property>]
  let ``comm: length``(Size a, Size b) =
    let c = comm a b
    c.Inputs.Length = a + b && c.Outputs.Length = a + b

  [<Property>]
  let ``comm: inverse``(Size a, Size b) =
    let a, b = 1 + int a, 1 + int b
    ~~(comm a b) .=. comm b a

  [<Property>]
  let ``comm: composed with its inverse``(Size a, Size b) =
    (comm a b >>> comm b a) .=. buffer (a + b)

  [<Property>]
  let ``rotate: inverse to substract``(Size a, Size b) =
    let n = a + b
    ~~(rotate n a) .=. rotate n (-a)

  [<Property>]
  let ``rotate: sum property``(Size a, Size b, Size c) =
    let n = a + b + c
    (rotate n a >>> rotate n b) .=. (buffer n >>> rotate n (a + b))

  [<Property>]
  let ``rotate: difference property``(Size a, Size b, Size c) =
    let n = a + b + c
    (rotate n a >>> rotate n (-b)) .=. compose (buffer n) (rotate n (a - b))

[<Properties(Arbitrary = [| typeof<Generators>; typeof<ReversibleArithTests.Generators> |], MaxTest = 100)>]
module ReversibleNetworkArithTests =
  open ReversibleArithTests
  // open ReversibleNetwork
  open ReversibleArith.Iso
  open ReversibleArith.NumIso

  let bIsoToNetwork biso =
    biso |> getSymIso |> FromIso.fromSymIso Network.simplify |> Network.canonicalize

  let eval n s num =
    Simulator.evaluate (Network.canonicalize n) (toBools num) 
    |> numFromBools s
    |> numberValue

  let eval2 n s (num, num') =
    let n = Network.canonicalize n
    let nbs, nbs' = toBools num, toBools num'
    let arr = Array.append nbs nbs'
    let res = Simulator.evaluate n arr
    intPairFromBools (s, s) res

  let eval2' n (s, s') (num, num') =
    let n = Network.canonicalize n
    let nbs, nbs' = toBools num, toBools num'
    let arr = Array.append nbs nbs'
    let res = Simulator.evaluate n arr
    intPairFromBools (s, s') res

  let succ = (IsoTests.succNum1 :> ISuccAddBuilder<_>).Succ
  let nSucc = bIsoToNetwork succ 
  let neg = (IsoTests.succNum1 :> ISuccAddBuilder<_>).Neg
  let nNeg = bIsoToNetwork neg 
  [<Property>]
  let ``succ n = n + 1 mod B``(Num1 n) =
    let num, m = numberValue n, modValue n
    let expected = (num + 1) % m
    let actual = eval nSucc IsoTests.succNum1 n
    expected = actual

  [<Property>]
  let ``repeat: n = succ^k(pred^k(n))``(Num1 n, Size k) =
    let num, m = numberValue n, modValue n
    let k = k % 5
    let expected = num % m
    let actual = eval (repeat k nSucc >>> ~~(repeat k nSucc)) IsoTests.succNum1 n
    expected = actual

  [<Property>]
  let ``repeat: n = compl^k(compl^-k(n))``(Num0 n, Size k) =
    let num, m = numberValue n, modValue n
    let k = k % 5
    let expected = num % m
    let nPerm = (IsoTests.succNum0 :> ISuccAddBuilder<_>).Compl |> bIsoToNetwork
    let actual = eval (repeat k nPerm >>> ~~(repeat k nPerm)) IsoTests.succNum1 n
    expected = actual

  [<Property>]
  let ``cond: compose property (same)``(Num0 a, Num0 b, Size i) =
    let n = modValue a
    let i = i % n
    let f = (IsoTests.succNum0 :> ISuccAddBuilder<_>).PlusConst 3 |> bIsoToNetwork
    let g = (IsoTests.succNum0 :> ISuccAddBuilder<_>).Neg |> bIsoToNetwork
    let cond, (>>>) = Builders.cond, Builders.Operators.(>>>)
    let ne, na = (cond n i f >>> cond n i g), (cond n i (f >>> g))
    let expected = eval2 ne IsoTests.succNum0 (a, b)
    let actual = eval2 na IsoTests.succNum0 (a, b)
    $"{expected} = {actual}" @| (expected = actual)

  [<Property>]
  let ``cond: compose property (identity)``(Num0 a, Num0 b, Size i, Size j) =
    let n = modValue a
    let i, j = i % n, j % n
    let f, g = identity n, identity n
    let cond, (>>>) = Builders.cond, Builders.Operators.(>>>)
    let ne, na = 
      if i = j then
        (cond n i f >>> cond n i g), (cond n i (f >>> g))
      else
        (cond n i f >>> cond n j g), (cond n j g >>> cond n i f)
    let expected = eval2 ne IsoTests.succNum0 (a, b)
    let actual = eval2 na IsoTests.succNum0 (a, b)
    true ==> ($"({numberValue a}, {numberValue b}) --> {expected} = {actual}" @| (expected = actual))

  [<Property>]
  let ``cond: compose property (effectively identity)``(Num0 a, Num0 b, Size i, Size j) =
    let n = modValue a
    let i, j = i % n, j % n
    let f, g = (rotate n 3 >>> rotate n (n - 3)), (reverse n >>> reverse n)
    let cond, (>>>) = Builders.cond, Builders.Operators.(>>>)
    let ne, na = 
      if i = j then
        (cond n i f >>> cond n i g), (cond n i (f >>> g))
      else
        (cond n i f >>> cond n j g), (cond n j g >>> cond n i f)
    let expected = eval2 ne IsoTests.succNum0 (a, b)
    let actual = eval2 na IsoTests.succNum0 (a, b)
    true ==> ($"({numberValue a}, {numberValue b}) --> {expected} = {actual}" @| (expected = actual))

  [<Property>]
  let ``cond: compose property (different)``(Num0 a, Num0 b, Size i, Size j) =
    let n = modValue a
    let i, j = i % n, j % n
    if i = j then
      false ==> false
    else
      let f = (IsoTests.succNum0 :> ISuccAddBuilder<_>).PlusConst 3 |> bIsoToNetwork
      let g = (IsoTests.succNum0 :> ISuccAddBuilder<_>).Neg |> bIsoToNetwork
      let cond, (>>>) = Builders.cond, Builders.Operators.(>>>)
      let ne, na = (cond n i f >>> cond n j g), (cond n j g >>> cond n i f)
      let expected = eval2 ne IsoTests.succNum0 (a, b)
      let actual = eval2 na IsoTests.succNum0 (a, b)
      true ==> ($"({numberValue a}, {numberValue b}) --> {expected} = {actual}" @| (expected = actual))

  let memo f =
    let d = System.Collections.Generic.Dictionary()
    fun args ->
      if d.ContainsKey(args) then
        d.[args]
      else
        let v = f args
        d.Add(args, v)
        v

  let private makeCij = memo <| fun (n, i, j) ->
    let s = (IsoTests.succNum1 :> ISuccAddBuilder<_>)
    let f = s.PlusConst 0 |> bIsoToNetwork
    let g = (ReversibleArith.Iso.Operators.(>>>) s.Neg s.Neg) |> bIsoToNetwork
    let cond, (>>>) = Builders.cond, Builders.Operators.(>>>)
    let s = Network.simplify
    (s (cond n i f) >>> s (cond n j g)), (s (cond n j g) >>> s (cond n i f))

  [<Property>]
  let ``cond: compose property (effectively identity 2)``(Num1 a, Num1 b, Size i, Size j) =
    let n = modValue a
    let i, j = i % n, j % n
    if i = j then
      false ==> false
    else
      let s = (IsoTests.succNum1 :> ISuccAddBuilder<_>)
      let neC1, naC1 = makeCij (n, i, j)
#if FALSE
      if Network.brokenRefs neC1 <> (Set.empty, Set.empty) then
        failwith "neC1"
      if Network.brokenRefs naC1 <> (Set.empty, Set.empty) then
        failwith "naC1"
#endif
      let expected = eval2 neC1 s (a, b)
      let actual = eval2 naC1 s (a, b)
      true ==> ($"({numberValue a}, {numberValue b}) --> {expected} = {actual}" @| (expected = actual))

  let private makeCC3 = memo <| fun (n, i, j, k) ->
    let f = (IsoTests.succNum0 :> ISuccAddBuilder<_>).PlusConst 3 |> bIsoToNetwork
    let g = (IsoTests.succNum0 :> ISuccAddBuilder<_>).Neg |> bIsoToNetwork
    let id = (IsoTests.succNum0 :> ISuccAddBuilder<_>).PlusConst 0 |> bIsoToNetwork
    let cond, (>>>) = Builders.cond, Builders.Operators.(>>>)
    (cond n i f >>> cond n k id >>> cond n j g), (cond n j g >>> cond n k id >>> cond n i f)

  [<Property>]
  let ``cond: compose property (different, intermediate identity)``(Num0 a, Num0 b, Size i, Size j, Size k) =
    let n = modValue a
    let i, j = i % n, j % n
    if i = j then
      false ==> false
    else
      let ne, na = makeCC3 (n, i, j, k)
#if FALSE
      if Network.brokenRefs ne <> (Set.empty, Set.empty) then
        failwith "ne"
      if Network.brokenRefs na <> (Set.empty, Set.empty) then
        failwith "na"
#endif
      let expected = eval2 ne IsoTests.succNum0 (a, b)
      let actual = eval2 na IsoTests.succNum0 (a, b)
      true ==> ($"({numberValue a}, {numberValue b}) --> {expected} = {actual}" @| (expected = actual))

  [<Property>]
  let ``cond: compose property (bool controlled, different)``(Bool a, Num0 b, Size i, Size j) =
    let n = modValue a
    let i, j = i % n, j % n
    if i = j then
      false ==> false
    else
      let f = (IsoTests.succNum0 :> ISuccAddBuilder<_>).PlusConst 4 |> bIsoToNetwork
      let g = (IsoTests.succNum0 :> ISuccAddBuilder<_>).Compl |> bIsoToNetwork
      let cond, (>>>) = Builders.cond, Builders.Operators.(>>>)
      let ne, na = (cond n i f >>> cond n j g), (cond n j g >>> cond n i f)
      let expected = eval2' ne (IsoTests.succBool, IsoTests.succNum0) (a, b)
      let actual = eval2' na (IsoTests.succBool, IsoTests.succNum0) (a, b)
      true ==> ($"({numberValue a}, {numberValue b}) --> {expected} = {actual}" @| (expected = actual))

  [<Property>]
  let ``neg n = -n mod B``(Num1 n) =
    let num, m = numberValue n, modValue n
    let expected = (m - num) % m
    let actual = eval nNeg IsoTests.succNum1 n
    expected = actual

  [<Property>]
  let ``plusK n = n + k mod B``(Num1 n, Size k) =
    let num, m = numberValue n, modValue n
    let expected = (num + k + m) % m
    let nPlusK = (IsoTests.succNum1 :> ISuccAddBuilder<_>).PlusConst k |> bIsoToNetwork
    let actual = eval nPlusK IsoTests.succNum1 n
    expected = actual

  [<Property>]
  let ``add mod B``(Num1 n, Num1 n') =
    let num, m = numberValue n, modValue n
    let num' = numberValue n'
    let expected = (num + (num' + m) % m + m) % m
    let nAdd = (IsoTests.succNum1 :> ISuccAddBuilder<_>).Add |> bIsoToNetwork
    let actual, actual' = eval2 nAdd IsoTests.succNum1 (n, n')
    (expected, num') .=. (actual, actual')

  [<Property>]
  let ``fst add(m, n) = fst add(n, m)``(Num1 n, Num1 n') =
    let nAdd = (IsoTests.succNum1 :> ISuccAddBuilder<_>).AddMultiple(1) |> bIsoToNetwork
    let expected, _ = eval2 nAdd IsoTests.succNum1 (n', n)
    let actual, _ = eval2 nAdd IsoTests.succNum1 (n, n')
    expected = actual

  [<Property>]
  let ``addMultiple mod B``(Num1 n, Num1 n', k : uint) =
    let k = int k
    let num, m = numberValue n, modValue n
    let num' = numberValue n'
    let k = k % m
    let expected = (num + (num' * k + m) % m + m) % m
    let nAdd = (IsoTests.succNum1 :> ISuccAddBuilder<_>).AddMultiple(k) |> bIsoToNetwork
    let actual, actual' = eval2 nAdd IsoTests.succNum1 (n, n')
    (expected, num') .=. (actual, actual')

