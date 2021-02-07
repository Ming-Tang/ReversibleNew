module ReversibleNetwork.Propagator
open ReversibleNetwork
open System.Collections.Generic

let boolForward(c, x) = c, (if c then x else false), (if c then false else x)
let boolBackward(c, p, m) = 
#if CHECKS
  if c && p && m then
    failwith $"boolBackward: c = {c}, p = m = {p}"
  if (c && m) || (not c && p) then
    failwith $"boolBackward: bad dir: c, p, m = {c}, {p}, {m}"
#endif
  c, p || m

type Propagator<'v>(n, forward, backward) =
  let { Vertices = vs; Edges = es; Splits = ss; Inputs = is; Outputs = os } = n
  let ss =
    seq {
      for s in ss do
        let is, os = Split.insOuts s
        for i in is ->
          i, (is, os, s.Dir)
    }
    |> dict

  let mutable states = new Dictionary<_, 'v option>()
  let q = Queue()

  let push = q.Enqueue
  
  let reset() =
    q.Clear()
    states <- Dictionary(seq { for v in vs -> KeyValuePair(v, None) })
    Seq.iter push is

  let getOut() =
    [| for o in os -> states.[o].Value |]

  let filled v = Option.isSome states.[v]

  let fill i v =
    if Option.isSome states.[i] then
      failwith $"already filled: states.[{i}] = {states.[i]}"
    states.[i] <- Some v

  let step() =
    let v = q.Dequeue()
    if es.ContainsKey v then
      let v' = es.[v]
      fill v' states.[v].Value
      push v'
    elif ss.ContainsKey(v) then
      let is, os, dir = ss.[v]
      if Seq.forall filled is && not (Seq.forall filled os) then
        match dir, is, os with
        | SplitDir.SDForward, [vc; vx], [vc'; vp; vm] ->
          let c', p, m = forward (states.[vc].Value, states.[vx].Value)
          fill vc' c'
          fill vp p
          fill vm m

        | SplitDir.SDBackward, [vc'; vp; vm], [vc; vx] ->
          let c, x = backward (states.[vc'].Value, states.[vp].Value, states.[vm].Value) 
          fill vc c
          fill vx x
        
        | _ -> failwith "Not possible"

        Seq.iter push os

  do reset()

  let run input =
    reset()
    for i, v in Seq.zip is input do
      fill i v

    while q.Count > 0 do 
      step()

    getOut()

  member p.Evaluate(input : #seq<_>) = run input

