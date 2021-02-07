module ReversibleNetwork.Simulator
open ReversibleNetwork
open ReversibleNetwork.Network
open System.Collections.Generic

type Op<'a> = 
| OpMov of 'a * 'a 
| OpCMov of ins: ('a * 'a) * outs: ('a * 'a * 'a)
| OpCUnmov of ins: ('a * 'a * 'a) * outs: ('a * 'a)

type Simulator(n) =
  let { Vertices = vs; Edges = es; Gates = ss; Inputs = is; Outputs = os } = n
  let depths = getDepths n
  let maxDepth = Seq.max depths.Values
  
  let ops = List()
  let vsPart() =
    seq {
      for v in vs do
        let d0 = depths.[v]
        yield v, d0
        if es.ContainsKey(v) then
          let v' = es.[v]
          let d1 = depths.[v']
          for d in d0 + 1 .. d1 - 1 do
            yield v', d
            ops.Add(OpMov((v', d), (v', d + 1)))

          ops.Add(OpMov((v, d0), (v', d0 + 1)))
    }

  let ssPart() =
    seq {
      for s in ss do
        let is, os = Gate.insOuts s
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
            yield (o, d)
            ops.Add(OpMov((o, d), (o, d + 1)))
    }

  let storageVertices =
    Seq.append (vsPart()) (ssPart())
#if CHECKS
    |> Set.ofSeq
#endif
    |> Array.ofSeq

  let indexByStorageVertex = 
    seq { for i, v in Seq.indexed storageVertices -> v, i }
    |> dict
  let n = storageVertices.Length

  let ops = 
    [|
      let iv = indexByStorageVertex
      for op in ops ->
        match op with
        | OpMov(v, v') -> OpMov(iv.[v], iv.[v'])
        | OpCMov((c, x), (c', p, m)) -> 
          OpCMov((iv.[c], iv.[x]), (iv.[c'], iv.[p], iv.[m]))
        | OpCUnmov((c', p, m), (c, x)) -> 
          OpCUnmov((iv.[c'], iv.[p], iv.[m]), (iv.[c], iv.[x]))
    |]

  let mutable storages = Array.zeroCreate<bool> n

  let checkOps() =
#if CHECKS
    for op in ops do
      match op with
      | OpMov(v, v') -> storages.[v] |> ignore
      | OpCMov((vc, vx), (vc', vp, vm)) 
      | OpCUnmov((vc', vp, vm), (vc, vx)) -> 
        for v in [ vc; vx; vc'; vp; vm ] do
          storages.[v] |> ignore
#else
    ()
#endif

  let step() =
    checkOps()
    let storages' = Array.zeroCreate<bool> n
    for op in ops do
      match op with
      | OpMov(v, v') -> storages'.[v'] <- storages.[v]
      | OpCMov((vc, vx), (vc', vp, vm)) -> 
        let c = storages.[vc]
        storages'.[vc'] <- c
        storages'.[if c then vp else vm] <- storages.[vx]
        storages'.[if c then vm else vp] <- false

      | OpCUnmov((vc', vp, vm), (vc, vx)) -> 
        let c = storages.[vc']
        storages'.[vc] <- c
        let xp, xm = storages.[vp], storages.[vm]
#if CHECKS
        if (xp && xm) || (c && xm) || (not c && xp) then
          failwith "step: invalid inputs for OpCUnmov"
#endif
        storages'.[vx] <- xp || xm

    storages <- storages'

  let setInput (xs : #seq<bool>) =
    for x, v in Seq.zip xs is do
      storages.[indexByStorageVertex.[(v, 0)]] <- x

  let getOutput() =
    [| for v in os -> storages.[indexByStorageVertex.[(v, depths.[v])]] |]

  member s.Step() = step()
  member s.Input xs = setInput xs
  member s.Output = getOutput()

  member s.Evaluate xs =
    setInput xs
    for i in 1 .. maxDepth do
      step()

    getOutput()

let evaluate' n xs =
  Simulator(n).Evaluate xs

open Propagator
let evaluate n xs =
  Propagator(n, boolForward, boolBackward).Evaluate xs

