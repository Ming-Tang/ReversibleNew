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
  let { Vertices = vs; Edges = es; Gates = ss; Inputs = is; Outputs = os } = n
  let getSS() =
    seq {
      for s in ss do
        let is, os = Gate.insOuts s
        let counter = (ref 0, is.Length)
        for i in is ->
          i, (counter, (is, os, s.Dir))
    }
    |> dict

  let mutable states = new Dictionary<_, 'v option>()

  let mutable ss = if false then getSS() else dict []

#if A
  let q = Queue()
  let push, pop = q.Enqueue, q.Dequeue
#else
  let q = Stack()
  let push, pop = q.Push, q.Pop
#endif
  
  let reset() =
    q.Clear()
    states <- Dictionary(seq { for v in vs -> KeyValuePair(v, None) })
    ss <- getSS()
    Seq.iter push is

  let getOut() =
    [| for o in os -> states.[o].Value |]

  let filled v = Option.isSome states.[v]

  let VISITED = -1
  let fill v value =
    if List.head v = "v159" then
      let x = 1
      ()

    if filled v then
      failwith $"already filled: states.[{v}] = {states.[v]}"
    if ss.ContainsKey(v) then
      let (rc, m), _ = ss.[v]
      if !rc = VISITED then
        failwith $"fill: buffer already visited v={v}"
      if !rc >= m then
        failwith $"fill: buffer already filled: {!rc} >= {m}, v={v}"
      rc := !rc + 1
      // printfn $"inc: v={v} : {!rc} {m} stk=%A{List.ofSeq q}"
    states.[v] <- Some value

  let step() =
    let v = pop()
    if es.ContainsKey v then
      let v' = es.[v]
      fill v' states.[v].Value
      push v'
    elif ss.ContainsKey(v) then
      let (rc, m), (is, os, dir) = ss.[v]
      if !rc > m then
        failwith $"step: !rc > m: {!rc} > {m}"
      elif !rc = m then
        // printfn $":: v={v} (%A{dir}, %A{is}, %A{os}) os=%A{os} stk=%A{List.ofSeq q}"
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
        
        | SplitDir.SDBuffer, _, _ ->
          for v, v' in Seq.zip is os do
            fill v' states.[v].Value

        | _ -> failwith $"Not possible: dir={dir} is={is} os={os}"

        Seq.iter push os
        rc := VISITED

  do reset()

  let run input =
    reset()
    for i, v in Seq.zip is input do
      fill i v

    while q.Count > 0 do 
      step()

    getOut()

  member p.Evaluate(input : #seq<_>) = run input

