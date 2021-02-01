module Reversible.BilliardMachineTests

open BilliardMachine
open Synthesis
open FsCheck
open FsCheck.Xunit

let genFieldCell = Gen.elements [FieldCell.CLeft; FieldCell.CRight]
let genBallCell = Gen.elements [BallCell.DirU; BallCell.DirD; BallCell.DirL; BallCell.DirR]

let keySet xs = Seq.map (fun (KeyValue(k, _)) -> k) xs |> Set.ofSeq

type Dist = Dist of int

type Steps = Steps of int

type Perm = Perm of int array

let forall f xs =
  let res =
    xs 
    |> Seq.fold (fun o x -> 
      match o with
      | None ->
        let s, b = f x
        if not b then Some (s : _ Lazy).Value
        else o
      | Some _ -> o
    ) None

  match res with
  | None -> "" @| true
  | Some(s) -> s @| false

type Generators() =
  static member Dist() =
    Gen.sized (fun n -> 
      Gen.choose (1, (min 10 n) + 1)
      |> Gen.map Dist
    )
    |> Arb.fromGen


  static member Perm() =
    Gen.sized (fun n -> 
      Array.init (max 2 (min 16 n)) id
      |> Gen.shuffle
      |> Gen.map Perm
    )
    |> Arb.fromGen

  static member Field() =
    Gen.sized (fun n ->
      gen {
        let! w = Gen.choose (3, min (2 * n + 3) 500)
        let! h = Gen.choose (3, min (2 * n + 3) 500)
        let genCoord = Gen.map2 (fun a b -> a, b) (Gen.choose (0, w - 1)) (Gen.choose (0, h - 1))
        let genCoord' = Gen.map2 (fun a b -> a, b) (Gen.choose (1, w - 2)) (Gen.choose (1, h - 2))
        let! nfc = Gen.choose(0, min (min (n / 3) 10) (1 + w * h / 12))
        let! nb = Gen.choose(0, min (min (n / 6) 5) (1 + w * h / 6))
        let! fc = Gen.listOfLength nfc (Gen.map2 (fun a b -> a, b) genCoord' genFieldCell)
        let! st = Gen.listOfLength nb (Gen.map2 (fun a b -> a, b) genCoord genBallCell)
        let initState = Map.ofSeq st
        let! steps = Gen.choose (0, 10 + 2 * n)
        return { Width = w
                 Height = h
                 FieldConfig = Map.ofSeq fc
                 InitState = initState }
               |> (fun f -> simulate f steps)
               |> snd
      }
    )
    |> Gen.scaleSize ((+) 2)
    |> Arb.fromGen

  static member Steps() =
    Gen.choose (0, 300)
    |> Gen.map Steps
    |> Arb.fromGen

[<Properties(Arbitrary = [| typeof<Generators> |], MaxTest = 1000, Verbose = false)>]
module BilliardMachineTests =
  [<Property>]
  let ``nonempty balls -> transpose f != f``(f : Field) =
    let s1 =
      f.InitState
      |> Seq.map (fun (KeyValue((x, y), _)) -> (x, y))
      |> Set.ofSeq
    let s2 =
      f.InitState
      |> Seq.map (fun (KeyValue((x, y), _)) -> (y, x))
      |> Set.ofSeq

    not (s1.Count > 0 && s2.Count > 0) || (not (s1 <> s2) || transpose f <> f)

  [<Property>]
  let ``nonempty -> reverse f != f``(f : Field) =
    f.InitState.Count = 0 || (reverse f <> f)

  [<Property>]
  let ``transpose (transpose f) = f``(f : Field) =
    transpose (transpose f) = f

  [<Property>]
  let ``reverse (reverse f) = f``(f : Field) =
    reverse (reverse f) = f

  [<Property>]
  let ``simulate f 0 = (false, f)``(f : Field) =
    simulate f 0 = (false, f)

  [<Property>]
  let ``width, height, fieldConfig unchanged``(f : Field, Steps n) =
    let conflict, f' = simulate f n
    conflict || (f.Width = f'.Width && f.Height = f'.Height && f.FieldConfig = f'.FieldConfig)

  [<Property>]
  let ``no conflicts -> count unchanged``(f : Field, Steps n) =
    let n = (int n) / 10
    let conflict, f' = simulate f n
    not conflict ==> (f.InitState.Count = f'.InitState.Count)

  [<Property>]
  let ``time reversal symmetry for 1 step (no conflicts)``(f : Field) =
    let conflict, f' = simulate f 1
    not conflict ==> lazy (
      let conflict', f'' = simulate (reverse f') 1
      not conflict' ==> (keySet f.FieldConfig = keySet f''.FieldConfig)
    )

  [<Property>]
  let ``time reversal symmetry (no conflicts)``(f : Field, Steps steps) =
    let conflict, f' = simulate f steps
    not conflict ==> lazy (
      let conflict', f'' = simulate (reverse f') steps
      not conflict' ==> (keySet f.FieldConfig = keySet f''.FieldConfig)
    )

  [<Property>]
  let ``simulating 1 step under transpose``(f : Field) =
    let conflict, f' = simulate f 1
    let conflict', f'' = simulate (transpose f) 1
    (not conflict && not conflict') ==> lazy (keySet (transpose f').FieldConfig = keySet f''.FieldConfig)

  [<Property>]
  let ``simulating 1 step under transpose: same conflict``(f : Field) =
    let conflict, f' = simulate f 1
    let conflict', f'' = simulate (transpose f) 1
    conflict = conflict'

[<Properties(Arbitrary = [| typeof<Generators> |], MaxTest = 1000, Verbose = false)>]
module SynthesisTests =
  let testPaths pps =
    let fc, ls = fieldConfigFromPaths pps
    let field = toField pps fc
    Seq.zip pps ls
    |> forall (fun (path : Coord list, l) ->
      let field' = { field with InitState = Map.ofList [path.[0], BallCell.DirR] }
      let c', field'' = simulate field' l
      let (KeyValue(p', d0)) = Seq.head field''.InitState
      (lazy ($"l=%A{l} c'=%A{c'}, d0=%A{d0} p'=%A{p'} p=%A{path} field'=%A{field'}\n\n%s{display field'}\n\n%s{display field''}"), 
       not c' && p' = List.last path)
    )

  [<Property>]
  let ``No errors for permPaths results for fieldConfigFromPaths``(Perm p) =
    try
      permPaths p |> fieldConfigFromPaths |> ignore
      "" @| true
    with e -> sprintf "%A" e @| false

  [<Property>]
  let ``horizontal line paths``(Dist x, Dist y, Dist d) =
    testPaths [
      [
        x, y
        x + d, y
        x + d + d, y
      ]
    ]

  [<Property>]
  let ``vertical line paths``(Dist x, Dist y, Dist d) =
    testPaths [
      [
        0, y
        x, y
        x, y + d
      ]
    ]

  [<Property>]
  let ``single bend paths``(Dist a, Dist b, Dist dy) =
    testPaths [
      [
        1, 1
        1 + a, 1
        1 + a, 1 + dy
      ]
    ]

  [<Property>]
  let ``double bend paths``(Dist a, Dist b, Dist dy) =
    testPaths [
      [
        1, 1
        1 + a, 1
        1 + a, 1 + dy
        1 + a + b, 1 + dy
      ]
    ]

  [<Property>]
  let ``Simulate permutation paths``(Perm p) =
    testPaths <| permPaths p

