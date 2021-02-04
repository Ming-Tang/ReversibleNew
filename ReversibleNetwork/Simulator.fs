module ReversibleNetwork.Simulator
open ReversibleNetwork
open ReversibleNetwork.Network
open System.Collections.Generic

type Op<'a> = 
| OpMov of 'a * 'a 
| OpCMov of ins: ('a * 'a) * outs: ('a * 'a * 'a)
| OpCUnmov of ins: ('a * 'a * 'a) * outs: ('a * 'a)

let getDepths ({ Inputs = ins; Outputs = outs; Vertices = vs } as n) =
  let getAdjacents = makeGetAdjacents n
  let ds = Dictionary(seq { for v in vs -> KeyValuePair(v, 0) })
  let visited = HashSet()
  let stk = Stack(seq { for v in ins -> v, 0 })
  while stk.Count > 0 do
    let v, dist = stk.Pop()
    visited.Add(v) |> ignore
    ds.[v] <- max ds.[v] dist
    let dist = ds.[v]
    match getAdjacents v with
    | None -> ()
    | Some (AdjVertex, vs) ->
      for v' in vs do
        stk.Push(v', 1 + dist)
    | Some (AdjSplit s, _) ->
      let ins, outs = Split.insOuts s
      for v' in ins do
        ds.[v'] <- max ds.[v] dist

      if Seq.forall visited.Contains ins then
        for v' in outs do
          stk.Push(v', 1 + dist)

  let maxOut = Seq.map (fun v -> ds.[v]) outs |> Seq.max
  for v in outs do 
    ds.[v] <- maxOut

  ds

type Simulator(n) =
  let { Vertices = vs; Edges = es; Splits = ss; Inputs = is; Outputs = os } = n
  let depths = getDepths n
  let maxDepth = Seq.max depths.Values
  
  let ops = List()
  let mutable storages = Dictionary()
  do
    for v in vs do
      let d0 = depths.[v]
      storages.Add((v, d0), false)
      if es.ContainsKey(v) then
        let v' = es.[v]
        let d1 = depths.[v']
        for d in d0 + 1 .. d1 - 1 do
          storages.Add((v', d), false)
          ops.Add(OpMov((v', d), (v', d + 1)))

        ops.Add(OpMov((v, d0), (v', d0 + 1)))

    for s in ss do
      let is, os = Split.insOuts s
      let d0 = seq { for i in is -> depths.[i] } |> Seq.max
      match s.Dir with
      | SplitDir.SDForward -> 
        OpCMov(((s.CIn, d0), (s.XIn, d0)), 
               ((s.COut, d0 + 1), (s.XOutPlus, d0 + 1), (s.XOutMinus, d0 + 1)))
        |> ops.Add
      | SplitDir.SDBackward ->
        OpCUnmov(((s.COut, d0), (s.XOutPlus, d0), (s.XOutMinus, d0)),
                 ((s.CIn, d0 + 1), (s.XIn, d0 + 1)))
        |> ops.Add

      for o in os do
        let d1 = depths.[o]
        for d in d0 + 1 .. d1 - 1 do
          storages.Add((o, d), false)
          ops.Add(OpMov((o, d), (o, d + 1)))

    if Set.ofSeq (Seq.map fst storages.Keys) <> Set.ofSeq vs then
      failwith "Some vertices are missing from initial storages"

  let ops = ops.AsReadOnly()

  let checkOps() =
    for op in ops do
      match op with
      | OpMov(v, v') -> storages.[v] |> ignore
      | OpCMov((vc, vx), (vc', vp, vm)) 
      | OpCUnmov((vc', vp, vm), (vc, vx)) -> 
        for v in [ vc; vx; vc'; vp; vm ] do
          storages.[v] |> ignore

  let step() =
    // checkOps()
    let storages' = Dictionary()
    for op in ops do
      match op with
      | OpMov(v, v') -> storages'.Add((v' : Vertex * int), storages.[v])
      | OpCMov((vc, vx), (vc', vp, vm)) -> 
        let c = storages.[vc]
        storages'.Add(vc', c)
        storages'.Add((if c then vp else vm), storages.[vx])
        storages'.Add((if c then vm else vp), false)

      | OpCUnmov((vc', vp, vm), (vc, vx)) -> 
        let c = storages.[vc']
        storages'.Add(vc, c)
        let xp, xm = storages.[vp], storages.[vm]
        if (xp && xm) || (c && xm) || (not c && xp) then
          failwith "step: invalid inputs for OpCUnmov"
        storages'.Add(vx, xp || xm)

    for v in is do
      storages'.Add((v, 0), false)

    if storages'.Count <> storages.Count then
      failwith $"Different number of keys: ${(storages'.Count, storages.Count)}"

    storages <- storages'

  let setInput (xs : #seq<bool>) =
    for x, v in Seq.zip xs is do
      storages.[(v, 0)] <- x

  let getOutput() =
    [| for v in os -> storages.[(v, depths.[v])] |]

  member s.Step() = step()
  member s.Input xs = setInput xs
  member s.Output = getOutput()

  member s.Evaluate xs =
    setInput xs
    for i in 1 .. maxDepth do
      step()

    getOutput()

let evaluate n xs =
  Simulator(n).Evaluate xs

