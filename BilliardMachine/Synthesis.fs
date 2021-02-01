module Synthesis
open BilliardMachine
open System.Collections.Generic

exception PathException of Coord * Coord
exception DirException of BallCell * BallCell
exception OverlapMirrorException

let private kvToP (KeyValue(k, v)) = k, v

let private trans (x0, y0) (a, b) (x, y) = x0 + a * x, y0 + b * y

let private pathLength path =
  let mutable l = 0
  let mutable p0 = Seq.head path
  for p in Seq.tail path do
    let x0, y0 = p0
    let x1, y1 = p
    l <- l + abs (x1 - x0) + abs (y1 - y0)
    p0 <- p

  l

let fieldConfigFromPaths (paths : #seq<#seq<Coord>>) =
  let fc = Dictionary()

  let add p d =
    if fc.ContainsKey(p) then
      if fc.[p] <> d then
        raise OverlapMirrorException
    else
      fc.Add(p, d)

  let lens =
    [|
      for path in paths ->
        let mutable p0 = Seq.head path
        let mutable d0 = BallCell.DirR
        let mutable l = 0
        for p in Seq.tail path do
          let x0, y0 = p0
          let x1, y1 = p
          let dx = x1 - x0
          let dy = y1 - y0
          l <- l + abs dx + abs dy
          let d1 =
            if dx > 0 && dy = 0 then 
              BallCell.DirR
            elif dx = 0 && dy > 0 then 
              BallCell.DirD
            elif dx = 0 && dy < 0 then 
              BallCell.DirU
            else
              raise <| PathException((x0, y0), (x1, y1))

          if d1 = d0 then
            p0 <- p
          else
            if d0 = BallCell.DirD && d1 = BallCell.DirR then
              add (x0 - 1, y0) FieldCell.CRight
            elif d0 = BallCell.DirU && d1 = BallCell.DirR then
              add (x0 - 1, y0 - 1) FieldCell.CLeft
            elif d0 = BallCell.DirR && d1 = BallCell.DirU then
              add (x0, y0) FieldCell.CLeft
            elif d0 = BallCell.DirR && d1 = BallCell.DirD then
              add (x0, y0 - 1) FieldCell.CRight
            else
              raise <| DirException(d0, d1)

            d0 <- d1
            p0 <- p

        let x, y = p0
        if d0 = BallCell.DirD then
          add (x - 1, y) FieldCell.CRight
        elif d0 = BallCell.DirU then
          add (x, y) FieldCell.CLeft

        l
    |]

  (fc
   |> Seq.map kvToP
   |> Map.ofSeq : FieldConfig), lens

let permPaths (perm : int[]) =
  [
    let n = perm.Length
    for i in 0 .. perm.Length - 1 do
      [ 
        0, i  + 1
        perm.[i] + 1, i + 1
        perm.[i] + 1, n + perm.[i] + 2
        n + 1, n + perm.[i] + 2
      ]
      |> List.map (trans (0, 1) (2, 4))
  ]

let sync (paths : #seq<#seq<Coord>>) =
  let lasts = Seq.map Seq.last paths
  let lxs = Seq.map fst lasts |> Set.ofSeq
  if Set.count lxs > 1 then
    failwith "sync: failed: mismatched x"

  let x0 = Set.minElement lxs
  let lengths = Seq.map pathLength paths
  let maxLen = Seq.max lengths
  let minLen = Seq.min lengths
  let mutable maxX = 0
  let addls =
    [
      for path, (x, y), l in Seq.zip3 paths lasts lengths ->
        let mutable lRemain = maxLen - l
        let mutable x1 = x + 1
        maxX <- max maxX x1
        let mutable ps = []
        while lRemain > 0 do
          if lRemain = 1 then
            failwith "sync: failed: lRemain odd"

          ps <- ps @ [
            x1 + 1, y
            x1 + 1, y + 1
            x1 + 3, y + 1
            x1 + 3, y
          ]
          x1 <- x1 + 5
          maxX <- max maxX (x1 + 3)
          lRemain <- lRemain - 2
        ps
    ]

  if maxX % 2 = 1 then maxX <- maxX + 1

  [
    for path, addl, (_, y1) in Seq.zip3 paths addls lasts ->
      List.concat [List.ofSeq path; List.ofSeq addl; [maxX, y1]]
  ]

let toField (ps : #seq<_>) (fc : FieldConfig) =
  let w, h =
    fc 
    |> Seq.map (kvToP >> fst)
    |> Seq.append (Seq.concat ps) 
    |> Seq.append (Seq.singleton (0, 0))
    |> Seq.reduce (fun (w, h) (x, y) -> max w (x + 2), max h (y + 2))

  { Width = w
    Height = h
    InitState = Map.empty
    FieldConfig = fc }

