module Reversible.Tests

open System
open Reversible
open Xunit
open FsCheck
open FsCheck.Xunit

type PermPair = PermPair of Perm * Perm
type ValidRType = ValidRType of RType
type SmallBinom = SmallBinom of RType
type ValidBlock = ValidBlock of Block
type ConformablePair = ConformablePair of Block * Block
type InitialMachineState = InitialMachineState of MachineState

type Generators =
  static member genPerm n =
    Array.init n id
    |> Gen.shuffle
    |> Gen.map Perm.create

  static member Perm() = 
    Gen.sized Generators.genPerm
    |> Arb.fromGen

  static member PermPair() =
    Gen.sized (fun n ->
      gen {
        let! a = Generators.genPerm n
        let! b = Generators.genPerm n
        return PermPair(a, b)
      }
    )
    |> Arb.fromGen

#if FALSE
  static member ValidRType() =
    Arb.from<RType>
    |> Arb.filter RType.isValid
    |> Arb.filter (RType.limit 3 2)
    |> Arb.convert ValidRType (fun (ValidRType r) -> r)
#endif
//#if FALSE
  static member ValidRType() =
    let rec generate depth =
      gen {
        match! Gen.choose(0, if depth <= 0 then 0 else 2) with
        | 0 -> 
          let! (SmallBinom t) = Arb.toGen (Generators.SmallBinom())
          return t
        | n ->
          let! n = Gen.choose (0, 5)
          let! children = Gen.arrayOfLength n (generate (depth - 1))
          let xs = children |> Array.toList
          return (if n % 2 = 0 then RType.TSum else RType.TProd) xs
      }

    Gen.sized (fun i -> generate (if i > 4 then 4 else i))
    |> Gen.filter RType.isValid
    |> Gen.map ValidRType
    |> Arb.fromGen
//#endif

  static member SmallBinom() =
    gen {
      let! n = Gen.choose (0, 5)
      let! k = Gen.choose (0, n)
      return SmallBinom (RType.TBinom(n, k))
    }
    |> Arb.fromGen

  static member genBlock width depth =
    let genElem n =
      Arb.from<Machine.Element> 
      |> Arb.toGen
      |> Gen.filter (function Machine.Identity n when n <= 0 -> false | Machine.TGateInv _ -> false | _ -> true)
      |> Gen.filter (fun e -> let s = Machine.elementInSize e in s > 0 && s <= n)
      |> Gen.map Machine.convertIdentityPerms

    let rec genFront width =
      gen {
        if width <= 0 then
          return []
        else
          let! e = genElem width
          let! es = genFront (width - Machine.elementInSize e)
          return e :: es
      }

    gen {
      if depth = 0 then
         return []
      else
         let! front = genFront width
         let! rest = Generators.genBlock (Machine.outSize (Block.Block [front])) (depth - 1)
         return front :: rest
    }

  static member ValidBlock() =
    Gen.sized (fun i -> Generators.genBlock (i + 1) (i + 1))
    |> Gen.map Block.Block
    |> Gen.scaleSize (min 8)
    |> Arb.fromGen

  static member ConformablePair() =
    Gen.sized (fun i -> 
      gen {
        let! lhs = Generators.genBlock (i + 1) (i + 1)
        let! rhs = Generators.genBlock (Machine.outSize <| Machine.Block lhs) (i + 1)
        return ConformablePair(Machine.Block lhs, Machine.Block rhs)
      }
    )
    |> Gen.scaleSize (min 8)
    |> Arb.fromGen

  static member InitialMachineState() =
    Gen.sized (fun i ->
      gen {
        let! xs = Generators.genBlock (i + 1) (i + 1)
        let block = Machine.Block xs
        let! init = Gen.arrayOfLength (Machine.inSize block) (Gen.elements [false; true])
        let ms = MachineState.MachineState(block)
        ms.State.[0] <- Array.copy init
        return InitialMachineState ms
      }
    )
    |> Gen.scaleSize (min 8)
    |> Arb.fromGen

[<Properties(Arbitrary = [| typeof<Generators> |], MaxTest = 1000)>]
module PermTests =
  [<Property>]
  let ``Perm double inverse: (f^-1)^-1 = f``(p : Perm) = 
    Perm.invert (Perm.invert p) = p

  [<Property>]
  let ``Perm double inverse: f^-1 (f x) = x``(p : Perm) = 
    let arr = [| 0 .. p.Length - 1 |]
    arr
    |> Array.copy
    |> Perm.apply p
    |> Perm.apply (Perm.invert p)
    |> (=) arr

  [<Property>]
  let ``Perm double inverse: f (f^-1 x) = x``(p : Perm) = 
    let arr = [| 0 .. p.Length - 1 |]
    arr
    |> Array.copy
    |> Perm.apply (Perm.invert p)
    |> Perm.apply p
    |> (=) arr

  [<Property>]
  let ``Perm compose: (f . g) x = f (g x)``(PermPair(f, g)) = 
    let arr = [| 0 .. f.Length - 1 |]
    let lhs =
      arr
      |> Perm.apply (Perm.compose f g)

    let rhs =
      arr
      |> Perm.apply g
      |> Perm.apply f

    lhs = rhs

  [<Property>]
  let ``Perm compose: (f . f^-1) = id``(p : Perm) = 
    Perm.compose p (Perm.invert p) = Perm.identity p.Length

  [<Property>]
  let ``Perm compose: (f^-1 . f) = id``(p : Perm) = 
    Perm.compose (Perm.invert p) p = Perm.identity p.Length

[<Properties(Arbitrary = [| typeof<Generators> |], MaxTest = 1000)>]
module BinomTests =
  [<Property>]
  let ``card = length of vals``(SmallBinom t) =
    RType.card t = Seq.length (RType.vals t)

  [<Property>]
  let ``collect preserves card``(SmallBinom t) =
    RType.card (RType.collect t) = RType.card t

  [<Property>]
  let ``collect preserves count``(SmallBinom t) =
    RType.count (RType.collect t) = RType.count t

  [<Property>]
  let ``collect preserves vals``(SmallBinom t) =
    Set.ofSeq (RType.vals (RType.collect t)) = Set.ofSeq (RType.vals t)

[<Properties(Arbitrary = [| typeof<Generators> |], MaxTest = 1000)>]
module RTypeTests =
  [<Property(Verbose = true)>]
  let ``no duplicates in vals``(ValidRType t) =
    let vals = RType.vals t
    (Set.ofSeq vals).Count = Seq.length vals

  [<Property(Verbose = true)>]
  let ``card = length of vals``(ValidRType t) =
    RType.card t = Seq.length (RType.vals t)

  [<Property(Verbose = true)>]
  let ``collect preserves card``(ValidRType t) =
    RType.card (RType.collect t) = RType.card t

  [<Property(Verbose = true)>]
  let ``collect preserves count``(ValidRType t) =
    RType.count (RType.collect t) = RType.count t

  [<Property(Verbose = true)>]
  let ``collect preserves vals``(ValidRType t) =
    Set.ofSeq (RType.vals (RType.collect t)) = Set.ofSeq (RType.vals t)

[<Properties(Arbitrary = [| typeof<Generators> |], MaxTest = 1000)>]
module MachineTests =
  [<Property>]
  let ``inverse is valid``(ValidBlock f) =
    Machine.isValid <| Machine.inverse f

  [<Property>]
  let ``double inverse``(ValidBlock f) =
    f = Machine.inverse (Machine.inverse f)

  [<Property>]
  let ``inSize inverse``(ValidBlock f) =
    Machine.inSize f = Machine.outSize (Machine.inverse f)

  [<Property>]
  let ``outSize inverse``(ValidBlock f) =
    Machine.outSize f = Machine.inSize (Machine.inverse f)

  [<Property>]
  let ``All generated blocks are valid``(ValidBlock f) =
    Machine.isValid f

  [<Property>]
  let ``hstack: inSize (f . g) = inSize f``(ConformablePair(f, g)) =
    Machine.inSize (Machine.hstack f g) = Machine.inSize f

  [<Property>]
  let ``hstack: outSize (f . g) = outSize g``(ConformablePair(f, g)) =
    Machine.outSize (Machine.hstack f g) = Machine.outSize g

  [<Property>]
  let ``hstack: depth (f . g) = depth f + depth g``(ConformablePair(f, g)) =
    Machine.depth (Machine.hstack f g) = Machine.depth f + Machine.depth g 

  [<Property>]
  let ``vstack: depth (f + g) = max(depth f, depth g)``(ValidBlock f, ValidBlock g) =
    Machine.depth (Machine.vstack f g) = max (Machine.depth f) (Machine.depth g)

  [<Property>]
  let ``vstack: inSize (f + g) = inSize f + inSize g``(ValidBlock f, ValidBlock g) =
    Machine.inSize (Machine.vstack f g) = Machine.inSize f + Machine.inSize g

  [<Property>]
  let ``vstack: outSize (f + g) = outSize f + outSize g``(ValidBlock f, ValidBlock g) =
    Machine.outSize (Machine.vstack f g) = Machine.outSize f + Machine.outSize g

[<Properties(Arbitrary = [| typeof<Generators> |], MaxTest = 1000)>]
module MachineStateTests =
  [<Property>]
  let ``run machine based on identity elements``(size : int, depth : int) =
    let size, depth = abs size, abs depth
    (size > 1 && depth > 1) ==> lazy (
      let input = Array.init size (fun i -> hash (size, depth, i) % 2 = 0)
      let expected = Array.copy input
      let block = Block.Block [
        for i in 1 .. depth -> [Machine.Identity size]
      ]
      let ms = MachineState.MachineState(block)
      ms.State.[0] <- input
      for i in 1 .. depth do
        ms.Step()
      expected = ms.State.[depth]
    )

  [<Property>]
  let ``run machine based on single permutation``(p : Perm) =
    not (Perm.isIdentity p) ==> lazy (
      let input = Array.init p.Length (fun i -> hash (p, i) % 2 = 0)
      let expected = Perm.apply p input
      let block = Block.Block [[Machine.Permute p]]
      let ms = MachineState.MachineState(block)
      ms.State.[0] <- input
      ms.Step()
      expected = ms.State.[1]
    )

  [<Property>]
  let ``run machine based on single permutation with padding``(p : Perm, pl : int, pr : int) =
    not (Perm.isIdentity p) ==> lazy (
      let input = Array.init p.Length (fun i -> hash (p, i) % 2 = 0)
      let expected = Perm.apply p input
      let block = Block.Block [
        for i in 1 .. pl -> [Machine.Identity p.Length]
        yield [Machine.Permute p]
        for i in 1 .. pr -> [Machine.Identity p.Length]
      ]
      let ms = MachineState.MachineState(block)
      ms.State.[0] <- input
      for j in 1 .. pl do ms.Step()
      ms.Step()
      for j in 1 .. pr do ms.Step()
      expected = ms.State.[ms.State.Length - 1]
    )

  [<Property>]
  let ``run machine based on composition of two permutations``(PermPair(p1, p2)) =
    (not (Perm.isIdentity p1) && not(Perm.isIdentity p2)) ==> lazy (
      let input = Array.init p1.Length (fun i -> hash (p1, p2, i) % 2 = 0)
      let expected = input |> Perm.apply p1 |> Perm.apply p2
      let block = Block.Block [
        [Machine.Permute p1]
        [Machine.Permute p2]
      ]
      let ms = MachineState.MachineState(block)
      ms.State.[0] <- input
      ms.Step()
      ms.Step()
      expected = ms.State.[2]
    )

  [<Property>]
  let ``composing a machine with its inverse performs identity``(InitialMachineState ms0) =
    let f = ms0.Block
    let input = Array.copy ms0.State.[0]
    let expected = Array.copy input
    let identity = Machine.hstack f (Machine.inverse f)
    //failwithf "%A" (ms0, identity)
    let ms = MachineState(identity)
    ms.State.[0] <- input
    ms.State.[0] <- input
    try
      for i in 1 .. Machine.depth identity do
        ms.Step()

      true ==> (expected = ms.State.[Machine.depth identity])
    with MachineState.TGateInvError _ -> 
      false ==> true

