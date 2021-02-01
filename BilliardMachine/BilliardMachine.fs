module BilliardMachine
open System.Collections.Generic
open System.Text

(* 
Balls are placed on (x, y), and mirrors are placed on (x + 1/2, y + 1/2),
where x, y are integers.
Balls have diameter of sqrt(2) and speed of 1.


      0    1
      | \  |
      |  \ |
0 ----+----+----
      |  / |
      | /  |
1 ----+----+----
      | \  |  /
      |  \ | /
2 ----+----+----

*)

type Coord = int * int

type FieldCell = 
| CNone = 0uy
| CLeft = 1uy
| CRight = 2uy

type BallCell =
| DirU = 0uy
| DirD = 1uy
| DirL = 2uy
| DirR = 3uy

type FieldConfig = Map<Coord, FieldCell>

type FieldState = Map<Coord, BallCell>

type Field = { FieldConfig : FieldConfig
               InitState : FieldState
               Width : int 
               Height : int }

let mapFromKV = Seq.map (function KeyValue(k, v) -> k, v) >> Map.ofSeq

let opp = 
  function
  | BallCell.DirU -> BallCell.DirD
  | BallCell.DirD -> BallCell.DirU
  | BallCell.DirL -> BallCell.DirR
  | BallCell.DirR -> BallCell.DirL
  | x -> x

let trans = 
  function
  | BallCell.DirR -> BallCell.DirD
  | BallCell.DirD -> BallCell.DirR
  | BallCell.DirU -> BallCell.DirL
  | BallCell.DirL -> BallCell.DirU
  | x -> x

let reverse field =
  { field with 
      FieldConfig = field.FieldConfig
      InitState = Map.ofSeq <| seq { for KeyValue(xy, v) in field.InitState -> xy, opp v } }

let transpose { Width = w; Height = h; FieldConfig = fc; InitState = st } =
  { Width = h
    Height = w
    FieldConfig = Map.ofSeq <| seq { for KeyValue((x, y), d) in fc -> (y, x), d }
    InitState = Map.ofSeq <| seq { for KeyValue((x, y), d) in st -> (y, x), trans d } }

type Simulation(field) =
  let { FieldConfig = fieldConfig; InitState = initState
        Width = width; Height = height } = field
  let mutable state = Dictionary(initState)

  let du, dd, dl, dr = ((BallCell.DirU, 0, -1), (BallCell.DirD, 0, 1), 
                        (BallCell.DirL, -1, 0), (BallCell.DirR, 1, 0))

  let du', dd', dl', dr' = ((BallCell.DirU, 0, 0), (BallCell.DirD, 0, 0), 
                            (BallCell.DirL, 0, 0), (BallCell.DirR, 0, 0))

  let chkCR xy =
    fieldConfig.ContainsKey(xy) && fieldConfig.[xy] = FieldCell.CRight

  let chkCL xy =
    fieldConfig.ContainsKey(xy) && fieldConfig.[xy] = FieldCell.CLeft

  let nL xy =
    state.ContainsKey(xy) && state.[xy] <> BallCell.DirL

  let nR xy =
    state.ContainsKey(xy) && state.[xy] <> BallCell.DirR

  let nU xy =
    state.ContainsKey(xy) && state.[xy] <> BallCell.DirU

  let nD xy =
    state.ContainsKey(xy) && state.[xy] <> BallCell.DirD

  let cL xy =
    state.ContainsKey(xy) && state.[xy] = BallCell.DirL

  let cR xy =
    state.ContainsKey(xy) && state.[xy] = BallCell.DirR

  let cU xy =
    state.ContainsKey(xy) && state.[xy] = BallCell.DirU

  let cD xy =
    state.ContainsKey(xy) && state.[xy] = BallCell.DirD

  let reverse() =
    let state' = Dictionary()
    for KeyValue(xy, c) in state do
      state'.[xy] <- 
        match c with
        | BallCell.DirU -> BallCell.DirD
        | BallCell.DirD -> BallCell.DirU
        | BallCell.DirL -> BallCell.DirR
        | BallCell.DirR -> BallCell.DirL
        | _ -> c

    state <- state'

  let step() =
    let state' = Dictionary()
    let mutable conflict = false
    for KeyValue((x, y) as xy, c) in state do
      let c', dx, dy =
        match c with
        | BallCell.DirU -> 
          if y = 0 || nU (x, y - 1) then dd
          elif chkCL (x - 1, y - 1) || cR (x - 1, y - 1) then dr
          elif chkCR (x, y - 1) || cL (x + 1, y - 1) then dl
          else du
        | BallCell.DirD -> 
          if y = height - 1 || nD (x, y + 1) then du
          elif chkCL xy || cL (x + 1, y + 1) then dl
          elif chkCR (x - 1, y) || cR (x - 1, y + 1) then dr
          else dd
        | BallCell.DirL -> 
          if x = 0 || nL (x - 1, y) then dr
          elif chkCL (x - 1, y - 1) || cD (x - 1, y - 1) then dd
          elif chkCR (x - 1, y) || cU (x - 1, y + 1) then du
          else dl
        | BallCell.DirR -> 
          if x = width - 1 || nR (x + 1, y) then dl
          elif chkCR (x, y - 1) || cD (x + 1, y - 1) then dd
          elif chkCL xy || cU (x + 1, y + 1) then du
          else dr
        | _ -> failwithf "Invalid BallCell: %A" c
      let xy' = x + dx, y + dy
      if state'.ContainsKey(xy') then
        conflict <- true
      else
        state'.[xy'] <- c'
    state <- state'
    conflict

  member s.Step() = step()
  member s.Reverse() = reverse()

  member s.UpdatedField =
    { field with InitState = mapFromKV state; FieldConfig = fieldConfig }
  
  member s.State = Dictionary(state)
  member s.Field = field
  member s.Count = state.Count

  member s.Display() =
    let sb = StringBuilder()
    let xs = Seq.append (fieldConfig |> Seq.map (fun kv -> fst kv.Key))
                        (state |> Seq.map (fun kv -> fst kv.Key))
    let ys = Seq.append (fieldConfig |> Seq.map (fun kv -> snd kv.Key))
                        (state |> Seq.map (fun kv -> snd kv.Key))

    // let minx, maxx = -1 + Seq.min xs, 1 + Seq.max xs
    // let miny, maxy = -1 + Seq.min ys, 1 + Seq.max ys
    let minx, maxx = 0, width - 1
    let miny, maxy = 0, height - 1

    let hr = new string([| 
      yield '+'
      for x in minx .. maxx do yield '-'; yield '-'
      yield '+' 
    |])
    sb.AppendLine(hr) |> ignore

    for y in miny .. maxy do
      sb.Append('|') |> ignore
      for x in minx .. maxx do
        let c =
          if state.ContainsKey((x, y)) then
            match state.[x, y] with
            | BallCell.DirU -> '^'
            | BallCell.DirD -> 'v'
            | BallCell.DirL -> '<'
            | BallCell.DirR -> '>'
            | _ -> ' '
          else ' '
        sb.Append([| c; ' ' |]) |> ignore

      sb.Append('|').AppendLine().Append('|') |> ignore
      for x in minx .. maxx do
        let c =
          if fieldConfig.ContainsKey((x, y)) then
            match fieldConfig.[x, y] with
            | FieldCell.CLeft -> '/'
            | FieldCell.CRight -> '\\'
            | _ -> '.'
          else '.'
        sb.Append([| ' '; c; |]) |> ignore
      sb.Append('|').AppendLine() |> ignore

    sb.AppendLine(hr) |> ignore
    sb.ToString()


let simulate field steps =
  let sim = Simulation field
  let mutable conflict = false
  for i in 1 .. steps do
    let r = sim.Step()
    conflict <- conflict || r

  conflict, sim.UpdatedField

let display field =
  Simulation(field).Display()
