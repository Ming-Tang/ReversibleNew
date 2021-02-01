open System
open System.Diagnostics
open BilliardMachine
open Synthesis

let main' _ =
  let field = { FieldConfig = Map.ofList [ (1, 0), FieldCell.CLeft
                                           (5, 0), FieldCell.CRight
                                           (5, 6), FieldCell.CLeft
                                           (1, 6), FieldCell.CRight ]
                InitState = Map.ofList [ (3, 1), BallCell.DirR 
                                         (2, 5), BallCell.DirR
                                         (6, 7), BallCell.DirU ]
                Width = 10
                Height = 10 }
  let w, h = 24, 12
  let r = Random(32)
  let field' = 
    let fc = 
      Map.ofList [ 
        for i in 1 .. r.Next(0, 0) ->
          (r.Next(0, w), r.Next(0, h)),
          (if r.Next() % 2 = 0 then FieldCell.CRight else FieldCell.CLeft)
      ]
    { 
      FieldConfig = fc 
      InitState = Map.ofList [ 
        for i in 1 .. r.Next(5, 6) do
          let xy = r.Next(0, w) / 4 * 4, r.Next(0, h) / 4 * 4
          if not <| fc.ContainsKey(xy) then
            xy, match r.Next(0, 4) with
                | 0 -> BallCell.DirU
                | 1 -> BallCell.DirD
                | 2 -> BallCell.DirL
                | _ -> BallCell.DirR
      ]
      Width = w
      Height = h }
  let sim = Simulation(field)
  let mutable c = false
  for i in 0 .. 1000 do
    Console.Clear()
    printfn "%d %d %A" i sim.Count c
    printfn "%s" <| sim.Display()
    for j in 0 .. 100 do 
      let r = sim.Step()
      c <- c || r   
    Threading.Thread.Sleep(50)

    // if i % 47 = 46 then sim.Reverse()

  0 // return an integer exit code

[<EntryPoint>]
let main _ =
  // let ps = permPaths [| 1; 2; 3; 4; 0 |]
  let ps = permPaths [| 4; 3; 2; 1; 0 |]
  let ps = sync ps
  printfn "%A" ps
  ps
  |> fieldConfigFromPaths
  |> printfn "%A"
  let fc, ts = fieldConfigFromPaths ps
  let field = toField ps fc
  for p, l in Seq.zip ps ts do
    let field' = { field with InitState = Map.ofList [p.[0], BallCell.DirR] }
    printfn "%s" (display <| field')
    let c', field'' = simulate field' l
    printfn "%s" (display <| field'')
  0

