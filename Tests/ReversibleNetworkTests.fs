module Reversible.ReversibleNetworkTests

open ReversibleNetwork
open Builders
open Operators
open FsCheck
open FsCheck.Xunit

type ComposedNetwork = ComposedNetwork of Network
type SymmetricComposedNetwork = SymmetricComposedNetwork of Network

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
  let cb = a |> Network.canonicalize
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
      |> Gen.map SymmetricComposedNetwork
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

  [<Property>]
  let ``inverse: composition = identity A``(ComposedNetwork n) =
    (n >>> (inverse n)) .=. identity n.Inputs.Length

  [<Property>]
  let ``inverse: composition = identity B``(ComposedNetwork n) =
    (inverse n >>> n) .=. identity n.Inputs.Length

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
    (rotate n a >>> rotate n b) .=. (rotate n (a + b))

  [<Property>]
  let ``rotate: difference property``(Size a, Size b, Size c) =
    let n = a + b + c
    (rotate n a >>> rotate n (-b)) .=. (rotate n (a + b))

  [<Property>]
  let ``cond: inverse property``(SymmetricComposedNetwork f, Size n, Size i) =
    let i = i % n
    cond n i (~~f) .=. ~~(cond n i f)

  [<Property>]
  let ``repeat: inverse property``(SymmetricComposedNetwork f, Size n) =
    repeat n (~~f) .=. ~~(repeat n f)

