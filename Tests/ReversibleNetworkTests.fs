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
type BoolArray = BoolArray of bool[]
/// A Size: positive integer
type Size = Size of int
/// Two difference sizes
type SizeD = SizeD of int * int

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
  static member BoolArray() =
    Gen.sized (fun n ->
      Gen.arrayOfLength (n + 1) (Gen.elements [false; true])
      |> Gen.map BoolArray
    )
    |> Arb.fromGen

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

  static member SizeD() =
    Gen.sized (fun n ->
      gen {
        let! a = Gen.choose (1, max 2 <| min 10 n)
        let! b = Gen.choose (1, max 2 <| min 10 n)
        return SizeD(a, b)
      }
      |> Gen.filter (fun (SizeD(a, b)) -> a <> b)
    )
    |> Arb.fromGen

[<Properties(Arbitrary = [| typeof<Generators> |], MaxTest = 1000)>]
module ReversibleNetworkTests =
  [<Property>]
  let ``No broken refs``(ComposedNetwork n) =
    Network.brokenRefs n = (Set.empty, Set.empty)

  [<Property>]
  let ``identity 0: right compose``(ComposedNetwork n) =
    n .=. (n &&& identity 0)

  [<Property>]
  let ``identity 0: left compose``(ComposedNetwork n) =
    n .=. (identity 0 &&& n)

  [<Property>]
  let ``identity 0 equal to empty perm``(ComposedNetwork n) =
    identity 0 .=. fromPerm [||]

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
  let ``inverse: operator``(ComposedNetwork n) =
    inverse n .=. ~~n

  [<Property>]
  let ``inverse: double inverse``(ComposedNetwork n) =
    inverse (inverse n) .=. n

  [<Property>]
  let ``reverse: self-inverse``(Size a) =
    reverse a .=. ~~(reverse a)

  [<Property>]
  let ``reverse: compose with its inverse``(Size a) =
    (reverse a >>> reverse a) .=. identity a

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
    (comm a b >>> comm b a) .=. identity (a + b)

  [<Property>]
  let ``rotate: inverse to substract``(Size a, Size b) =
    let n = a + b
    ~~(rotate n a) .=. rotate n (-a)

  [<Property>]
  let ``rotate: sum property``(Size a, Size b, Size c) =
    let n = a + b + c
    (rotate n a >>> rotate n b) .=. rotate n (a + b)

  [<Property>]
  let ``rotate: difference property``(Size a, Size b, Size c) =
    let n = a + b + c
    (rotate n a >>> rotate n (-b)) .=. rotate n (a - b)

[<AutoOpen>]
module Memo =
  open System.Collections.Generic
  let private _memo = Dictionary<string * obj, Network>()
  let memoized (name, (x : 'a)) (f : 'a -> Network) =
    let p, value = _memo.TryGetValue((name, box x))
    if p then
      value
    else
      let res = f x |> Network.canonicalize
      _memo.Add((name, box x), res)
      unbox res

  let memoized2 (name, x) (f : 'a -> Network * Network) =
    memoized (name, (x, "fst")) (fst >> f >> fst),
    memoized (name, (x, "snd")) (fst >> f >> snd)

[<Properties(Arbitrary = [| typeof<Generators> |], MaxTest = 100)>]
module ReversibleNetworkMultiplexTests =
  [<Property>]
  let ``multiplex: no broken refs``(Size n) =
    Network.brokenRefs (multiplex n) = (Set.empty, Set.empty)

  let private eval n input = Simulator.evaluate (Network.canonicalize n) input

  [<Property>]
  let ``multiplex: plus output``(BoolArray xs) =
    let n = xs.Length
    let zs = Array.zeroCreate n
    let mpx = multiplex n
    let input = [| yield true; yield! xs |]
    let expected = [| yield true; yield! xs; yield! zs |]
    expected = eval mpx input

  [<Property>]
  let ``multiplex: minus output``(BoolArray xs) =
    let n = xs.Length
    let zs = Array.zeroCreate n
    let mpx = multiplex n
    let input = [| yield false; yield! xs |]
    let expected = [| yield false; yield! zs; yield! xs |]
    expected = eval mpx input

  [<Property>]
  let ``multiplex: compose with inverse``(BoolArray xs) =
    let n = xs.Length
    let md = multiplex n >>> demultiplex n
    let input = [| yield false; yield! xs |]
    input = eval md input

  [<Property>]
  let ``multiplex: double compose with inverse``(BoolArray xs) =
    let n = xs.Length
    let zs = Array.zeroCreate n
    let md = multiplex n >>> demultiplex n
    let f = md >>> md
    let input = [| yield false; yield! xs |]
    input = eval md input

  [<Property>]
  let ``multiplex: double compose with inverse (reverse, minus)``(BoolArray xs) =
    let n = xs.Length
    let md = multiplex n >>> (identity 1 &&& reverse n &&& identity n) >>> demultiplex n
    let f = md >>> md
    let input = [| yield false; yield! xs |]
    input = eval md input

  [<Property>]
  let ``multiplex: double compose with inverse (reverse, plus)``(BoolArray xs) =
    let n = xs.Length
    let md = multiplex n >>> (identity 1 &&& reverse n &&& identity n) >>> demultiplex n
    let input = [| yield true; yield! xs |]
    let output = [| yield true; yield! Array.rev xs |]
    output = eval md input

  [<Property>]
  let ``multiplex: double multiplex``(BoolArray xs, a, b) =
    let n = xs.Length
    let fp n p m = multiplex n >>> (identity 1 &&& p &&& m) >>> demultiplex n
    let md = fp (n + 1) (fp n (reverse n) (identity n)) (identity (n + 1))
    let f = md >>> md
    let input = [| yield a; yield b; yield! xs |]
    let output = [| yield a; yield b; yield! if a && b then Array.rev xs else xs |]
    output = eval md input

  [<Property>]
  let ``multiplex: double multiplex 2``(BoolArray xs, a, b) =
    let n = xs.Length
    let fp n p m = multiplex n >>> (identity 1 &&& p &&& m) >>> demultiplex n
    let fpn = fp n (reverse n) (identity n)
    let md = fp (n + 1) (fpn >>> fpn) (identity (n + 1))
    let input = [| yield a; yield b; yield! xs |]
    input = eval md input

  let tripleMultiplex n =
    let fp n p m = multiplex n >>> (identity 1 &&& p &&& m) >>> demultiplex n
    let fpn00 = fp n (identity n) (identity n)
    let fpn10 = fp n (reverse n) (identity n)
    let fpn01 = fp n (identity n) (reverse n)
    let fpn11 = fp n (reverse n) (reverse n)
    let upper = fp (n + 1) fpn10 fpn10 >>> fp (n + 1) fpn10 fpn01
    let lower = fp (n + 1) fpn00 fpn11
    fp (n + 2) upper lower

  [<Property>]
  let ``multiplex: triple multiplex``(BoolArray xs, a, b, c) =
    let n = xs.Length
    let md = memoized ("triple", n) tripleMultiplex
    let input = [| yield a; yield b; yield c; yield! xs |]
    let output = [| yield a; yield b; yield c;
                    yield! if (a && not b) || (not a && not b) then Array.rev xs else xs |]
    output = eval md input

  [<Property>]
  let ``multiplex: triple multiplex (double compose)``(BoolArray xs, a, b, c) =
    let n = xs.Length
    let md = memoized ("triple'", n) (fun n -> let x = tripleMultiplex n in x >>> x)
    let input = [| yield a; yield b; yield c; yield! xs |]
    input = eval (md >>> md) input

  [<Property>]
  let ``multiplex: triple multiplex (double compose, padded)``(BoolArray ps, BoolArray xs, a, b, c) =
    let m, n = ps.Length, xs.Length
    let md = memoized ("triple''", (m, n)) 
               (fun (m, n) -> let x = tripleMultiplex n in identity m &&& (x >>> x))
    let input = [| yield! ps; yield a; yield b; yield c; yield! xs |]
    input = eval (md >>> md) input

  [<Property>]
  let ``multiplex: triple multiplex (double compose, padded, reverse)``(BoolArray ps, BoolArray xs, a, b, c) =
    let m, n = ps.Length, xs.Length
    let md = memoized ("triple''", (m, n)) <| fun (m, n) -> 
                  let x = tripleMultiplex n
                  let pre = comm 3 m &&& identity n
                  pre >>> (identity m &&& (x >>> x)) >>> ~~pre
    let input = [| yield a; yield b; yield c; yield! ps; yield! xs |]
    input = eval (md >>> md) input

[<AutoOpen>]
module Helpers =
  open ReversibleArith.Iso

  let bIsoToNetwork biso =
    biso |> getSymIso |> FromIso.fromSymIso Network.simplify |> Network.canonicalize

  let eval n s num =
    Simulator.evaluate (Network.canonicalize n) (toBools num) 
    |> numFromBools s
    |> numberValue

  let eval2 n s (num, num') =
    let nbs, nbs' = toBools num, toBools num'
    let arr = Array.append nbs nbs'
    let res = Simulator.evaluate n arr
    intPairFromBools (s, s) res

  let eval2' n (s, s') (num, num') =
    let nbs, nbs' = toBools num, toBools num'
    let arr = Array.append nbs nbs'
    let res = Simulator.evaluate n arr
    intPairFromBools (s, s') res

  let eval' n arr =
    Simulator.evaluate (Network.canonicalize n) arr

[<Properties(Arbitrary = [| typeof<Generators>; typeof<ReversibleArithTests.Generators> |], MaxTest = 200)>]
module ReversibleNetworkArithCondTests =
  open ReversibleArithTests
  open ReversibleArith.NumIso

  [<Property>]
  let ``cond: compose property (same)``(Num0 a, Num0 b, Size i) =
    let n = modValue a
    let i = i % n
    let ne, na = memoized2 ("ccs", i) <| fun i ->
      let f = (IsoTests.succNum0 :> ISuccAddBuilder<_>).PlusConst 3 |> bIsoToNetwork
      let g = (IsoTests.succNum0 :> ISuccAddBuilder<_>).Neg |> bIsoToNetwork
      let cond, (>>>) = Builders.cond, Builders.Operators.(>>>)
      (cond n i f >>> cond n i g), (cond n i (f >>> g))
    let expected = eval2 ne IsoTests.succNum0 (a, b)
    let actual = eval2 na IsoTests.succNum0 (a, b)
    $"{expected} = {actual}" @| (expected = actual)

  [<Property>]
  let ``cond: compose property (identity)``(Num0 a, Num0 b, Size i, Size j) =
    let n = modValue a
    let i, j = i % n, j % n
    let ne, na = memoized2 ("cci", (n, i, j)) <| fun (n, i, j) ->
      let f, g = identity n, identity n
      let cond, (>>>) = Builders.cond, Builders.Operators.(>>>)
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
    let ne, na = memoized2 ("ccei", (n, i, j)) <| fun (n, i, j) ->
      let i, j = i % n, j % n
      let f, g = (rotate n 3 >>> rotate n (n - 3)), (reverse n >>> reverse n)
      let cond, (>>>) = Builders.cond, Builders.Operators.(>>>)
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
      let ne, na = memoized2 ("ccd", (n, i, j)) <| fun (n, i, j) ->
        let f = (IsoTests.succNum0 :> ISuccAddBuilder<_>).PlusConst 3 |> bIsoToNetwork
        let g = (IsoTests.succNum0 :> ISuccAddBuilder<_>).Neg |> bIsoToNetwork
        let cond, (>>>) = Builders.cond, Builders.Operators.(>>>)
        (cond n i f >>> cond n j g), (cond n j g >>> cond n i f)

      let expected = eval2 ne IsoTests.succNum0 (a, b)
      let actual = eval2 na IsoTests.succNum0 (a, b)
      true ==> ($"({numberValue a}, {numberValue b}) --> {expected} = {actual}" @| (expected = actual))

  [<Property>]
  let ``cond: compose property (different feedback)``(Num0 a, Num0 b, Size i, Size j) =
    let n = modValue a
    let i, j = i % n, j % n
    if i = j then
      false ==> false
    else
      let ni = memoized ("ccdf", (n, i, j)) <| fun (n, i, j) ->
        let f = (IsoTests.succNum0 :> ISuccAddBuilder<_>).PlusConst 3 |> bIsoToNetwork
        let g = (IsoTests.succNum0 :> ISuccAddBuilder<_>).Neg |> bIsoToNetwork
        let cond, (>>>) = Builders.cond, Builders.Operators.(>>>)
        let ne = (cond n i f >>> cond n j g)
        ne >>> ~~ne

      let expected = numberValue a, numberValue b
      let actual = eval2 ni IsoTests.succNum0 (a, b)
      true ==> ($"({numberValue a}, {numberValue b}) --> {expected} = {actual}" @| (expected = actual))

  [<Property>]
  let ``cond (different missing)``(Num0 a, Num0 b, Size i) =
    let n = modValue a
    let i = i % n
    (numberValue a <> i) ==> lazy (
      let expected = numberValue a, numberValue b
      let n = memoized ("cdm", (n, i)) <| fun (n, i) -> 
        let f = (IsoTests.succNum0 :> ISuccAddBuilder<_>).PlusConst 3 |> bIsoToNetwork
        Builders.cond n i f
      let actual = eval2 n IsoTests.succNum0 (a, b)
      ($"({numberValue a}, {numberValue b}, i={i}) --> {expected} = {actual}" @| (expected = actual))
    )

  [<Property>]
  let ``cond (different missing double eval)``(Num0 a, Num0 b, Size i) =
    let n = modValue a
    let i = i % n
    (numberValue a <> i) ==> lazy (
      let f = (IsoTests.succNum0 :> ISuccAddBuilder<_>).PlusConst 3 |> bIsoToNetwork
      let expected = numberValue a, numberValue b
      let n = Builders.cond n i f
      let actual = eval2 n IsoTests.succNum0 (a, b)
      ($"({numberValue a}, {numberValue b}, i={i}) --> {expected} = {actual}" @| (expected = actual))
    )

  [<Property>]
  let ``cond: compose property (different missing)``(Num0 a, Num0 b, Size i, Size j) =
    let n = modValue a
    let i, j = i % n, j % n
    if i = j then
      false ==> lazy("" @| false)
    else
      let numA = numberValue a
      (numA <> i && numA <> j) ==> lazy (
        let f = (IsoTests.succNum0 :> ISuccAddBuilder<_>).PlusConst 3 |> bIsoToNetwork
        let g = (IsoTests.succNum0 :> ISuccAddBuilder<_>).Neg |> bIsoToNetwork
        let expected = numberValue a, numberValue b
        let cond, (>>>) = Builders.cond, Builders.Operators.(>>>)
        let n = cond n i f >>> cond n j g
        let actual = eval2 n IsoTests.succNum0 (a, b)
        ($"({numberValue a}, {numberValue b}) --> {expected} = {actual}" @| (expected = actual))
      )

  let private makeCij = fun (n, i, j) ->
    let s = (IsoTests.succNum1 :> ISuccAddBuilder<_>)
    let f = s.PlusConst 0 |> bIsoToNetwork
    let g = (ReversibleArith.Iso.Operators.(>>>) s.Neg s.Neg) |> bIsoToNetwork
    let cond, (>>>) = Builders.cond, Builders.Operators.(>>>)
    let s = Network.simplify
    (s (cond n i f) >>> s (cond n j g)), (s (cond n j g) >>> s (cond n i f))

  let private makeCij1 = fun (n, i, j) ->
    let s = (IsoTests.succNum1 :> ISuccAddBuilder<_>)
    let f = s.Compl |> bIsoToNetwork
    let g = s.Compl |> bIsoToNetwork
    let cond, (>>>) = Builders.cond, Builders.Operators.(>>>)
    let s = Network.simplify
    (s (cond n i f) >>> s (cond n j g)), (s (cond n j g) >>> s (cond n i f))

  [<Property>]
  let ``cond: compose property (effectively permutations)``(Num1 a, Num1 b, Size i, Size j) =
    let n = List.sum (getBases a)
    let i, j = i % n, j % n
    if i = j then
      false ==> false
    else
      let s = (IsoTests.succNum1 :> ISuccAddBuilder<_>)
      let neC1, naC1 = memoized2 ("makeCij1", (n, i, j)) makeCij1
      let expected = eval2 neC1 s (a, b)
      let actual = eval2 naC1 s (a, b)
      true ==> ($"({numberValue a}, {numberValue b}) --> {expected} = {actual}" @| (expected = actual))

  [<Property>]
  let ``cond: compose property (effectively identity 2)``(Num1 a, Num1 b, Size i, Size j) =
    let n = List.sum (getBases a)
    let i, j = i % n, j % n
    if i = j then
      false ==> false
    else
      let s = (IsoTests.succNum1 :> ISuccAddBuilder<_>)
      let neC1, naC1 = memoized2 ("makeCij", (n, i, j)) makeCij
      let expected = eval2 neC1 s (a, b)
      let actual = eval2 naC1 s (a, b)
      true ==> ($"({numberValue a}, {numberValue b}) --> {expected} = {actual}" @| (expected = actual))

  let private makeCC3 = fun (n, i, j, k) ->
    let f = (IsoTests.succNum0 :> ISuccAddBuilder<_>).PlusConst 3 |> bIsoToNetwork
    let g = (IsoTests.succNum0 :> ISuccAddBuilder<_>).Neg |> bIsoToNetwork
    let id = (IsoTests.succNum0 :> ISuccAddBuilder<_>).PlusConst 0 |> bIsoToNetwork
    let cond, (>>>) = Builders.cond, Builders.Operators.(>>>)
    (cond n i f >>> cond n k id >>> cond n j g), (cond n j g >>> cond n k id >>> cond n i f)

  [<Property>]
  let ``cond: compose property (different, intermediate identity)``(Num0 a, Num0 b, SizeD(i, j), Size k) =
    let n = List.sum (getBases a)
    let i, j, k = i % n, j % n, k % n
    let ne, na = memoized2 ("makeCC3", (n, i, j, k)) makeCC3 
    let expected = eval2 ne IsoTests.succNum0 (a, b)
    let actual = eval2 na IsoTests.succNum0 (a, b)
    $"({numberValue a}, {numberValue b}) --> {expected} = {actual}" @| (expected = actual)

  [<Property>]
  let ``cond: compose property (double eval)``(Num0 a, Num0 b, SizeD (i, j)) =
    let n = modValue a
    let i, j = i % n, j % n
    let f = (IsoTests.succNum0 :> ISuccAddBuilder<_>).PlusConst 3 |> bIsoToNetwork
    let g = (IsoTests.succNum0 :> ISuccAddBuilder<_>).Neg |> bIsoToNetwork
    let cond, (>>>) = Builders.cond, Builders.Operators.(>>>)
    let lhs = cond n i f
    let rhs = cond n j g
    let expected = eval2 (lhs >>> rhs) IsoTests.succNum0 (a, b)
    let actual = 
      let x, y = eval2 rhs IsoTests.succNum0 (a, b)
      let x, y = Digit(x, B10), Digit(y, B10)
      eval2 lhs IsoTests.succNum0 (x, y)

    $"({numberValue a}, {numberValue b}) --> {expected} = {actual}" @| (expected = actual)

  [<Property>]
  let ``cond: compose property (bool controlled, different)``(Bool a, Num0 b, p) =
    let n = 2
    let i, j = if p then 1, 0 else 0, 1
    let f = (IsoTests.succNum0 :> ISuccAddBuilder<_>).PlusConst 4 |> bIsoToNetwork
    let g = (IsoTests.succNum0 :> ISuccAddBuilder<_>).Compl |> bIsoToNetwork
    let cond, (>>>) = Builders.cond, Builders.Operators.(>>>)
    let ne, na = (cond n i f >>> cond n j g), (cond n j g >>> cond n i f)
    let expected = eval2' ne (IsoTests.succBool, IsoTests.succNum0) (a, b)
    let actual = eval2' na (IsoTests.succBool, IsoTests.succNum0) (a, b)
    $"({numberValue a}, {numberValue b}) --> {expected} = {actual}" @| (expected = actual)

  [<Property>]
  let ``cond: compose property (bool controlled, feedback)``(Bool a, Num0 b, p) =
    let n = 2
    let i, j = if p then 1, 0 else 0, 1
    let f = (IsoTests.succNum0 :> ISuccAddBuilder<_>).PlusConst 4 |> bIsoToNetwork
    let g = (IsoTests.succNum0 :> ISuccAddBuilder<_>).Compl |> bIsoToNetwork
    let cond, (>>>) = Builders.cond, Builders.Operators.(>>>)
    let ne = (cond n i f >>> cond n j g)
    let ni = ne >>> ~~ne
    let expected = (numberValue a, numberValue b)
    let actual = eval2' ni (IsoTests.succBool, IsoTests.succNum0) (a, b)
    $"({numberValue a}, {numberValue b}) --> {expected} = {actual}" @| (expected = actual)

  [<Property>]
  let ``mcond: double cond``(Size i, Size j, Num1 a) =
    let n = modValue a
    let m1, m2 = 4, 6
    let i, j = i % m1, j % m2
    let f = (IsoTests.succNum1 :> ISuccAddBuilder<_>).PlusConst 4 |> bIsoToNetwork
    let g = (IsoTests.succNum1 :> ISuccAddBuilder<_>).Compl |> bIsoToNetwork
    let f = f >>> g
    let cond, (>>>) = Builders.cond, Builders.Operators.(>>>)
    let ne, na = (cond m1 i (cond m2 j f)), (mcond [i, m1; j, m2] f)
    let input = [|
      for i1 in 0 .. m1 - 1 -> i1 = i
      for j1 in 0 .. m2 - 1 -> j1 = j
      yield! toBools a
    |]
    let expected = eval' ne input
    let actual = eval' na input
    $"({i} {j} {numberValue a}) --> {expected} = {actual}" @| (expected = actual)

  [<Property>]
  let ``mcond: triple cond``(Size i, Size j, Size k, Num1 a) =
    let n = modValue a
    let m1, m2, m3 = 4, 6, 5
    let i, j, k = i % m1, j % m2, k % m3
    let f = (IsoTests.succNum1 :> ISuccAddBuilder<_>).PlusConst 17 |> bIsoToNetwork
    let g = (IsoTests.succNum1 :> ISuccAddBuilder<_>).Compl |> bIsoToNetwork
    let f = f >>> g
    let cond, (>>>) = Builders.cond, Builders.Operators.(>>>)
    let ne, na = (cond m1 i (cond m2 j (cond m3 k f))), (mcond [i, m1; j, m2; k, m3] f)
    let input = [|
      for i1 in 0 .. m1 - 1 -> i1 = i
      for j1 in 0 .. m2 - 1 -> j1 = j
      for k1 in 0 .. m3 - 1 -> k1 = k
      yield! toBools a
    |]
    let expected = eval' ne input
    let actual = eval' na input
    true ==> ($"({i} {j} {numberValue a}) --> {expected} = {actual}" @| (expected = actual))

  [<Property>]
  let ``mcond: 4x bool``(i, j, k, l, Num1 a) =
    let n = modValue a
    let i, j, k, l = (if i then 1 else 0), (if j then 1 else 0), (if k then 1 else 0), (if l then 1 else 0)
    let f = (IsoTests.succNum1 :> ISuccAddBuilder<_>).PlusConst 17 |> bIsoToNetwork
    let g = (IsoTests.succNum1 :> ISuccAddBuilder<_>).Compl |> bIsoToNetwork
    let f = f >>> g
    let cond, (>>>) = Builders.cond, Builders.Operators.(>>>)
    let ne, na = (cond 2 i (cond 2 j (cond 2 k (cond 2 l f)))), (mcond [i, 2; j, 2; k, 2; l, 2] f)
    let input = [|
      for i1 in 0 .. 1 -> i1 = i
      for j1 in 0 .. 1 -> j1 = j
      for k1 in 0 .. 1 -> k1 = k
      for l1 in 0 .. 1 -> l1 = l
      yield! toBools a
    |]
    let expected = eval' ne input
    let actual = eval' na input
    true ==> ($"({i} {j} {numberValue a}) --> {expected} = {actual}" @| (expected = actual))

[<Properties(Arbitrary = [| typeof<Generators>; typeof<ReversibleArithTests.Generators> |], MaxTest = 100)>]
module ReversibleNetworkArithTests =
  open ReversibleArithTests
  open ReversibleArith.NumIso

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
    let actual = eval (repeat k nPerm >>> ~~(repeat k nPerm)) IsoTests.succNum0 n
    expected = actual

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
    let nAdd = memoized ("add mod B", ()) 
                 (fun _ -> ((IsoTests.succNum1 :> ISuccAddBuilder<_>).Add |> bIsoToNetwork))
    let actual, actual' = eval2 nAdd IsoTests.succNum1 (n, n')
    (expected, num') .=. (actual, actual')

  [<Property>]
  let ``fst add(m, n) = fst add(n, m)``(Num1 n, Num1 n') =
    let nAdd = memoized ("fstAdd", ()) 
                 (fun _ -> ((IsoTests.succNum1 :> ISuccAddBuilder<_>).AddMultiple(1) |> bIsoToNetwork))
    let expected, _ = eval2 nAdd IsoTests.succNum1 (n', n)
    let actual, _ = eval2 nAdd IsoTests.succNum1 (n, n')
    expected = actual

  [<Property>]
  let ``addMultiple mod B``(Num1 n, Num1 n', Size k) =
    let k = 2 * (k % 5) + 1
    let num, m = numberValue n, modValue n
    let num' = numberValue n'
    let expected = (num + (num' * k + m) % m + m) % m
    let nAdd = memoized ("aM B", k) (fun k -> (IsoTests.succNum1 :> ISuccAddBuilder<_>).AddMultiple(k) |> bIsoToNetwork)
    let actual, actual' = eval2 nAdd IsoTests.succNum1 (n, n')
    (expected, num') .=. (actual, actual')

