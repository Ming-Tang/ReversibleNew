module Reversible.MachineState
open Reversible
open Reversible.Machine

exception TGateInvError of p : bool * m : bool * c: bool

type MachineState(block : Block) = 
  do
    if not (isValid block) then
      failwith "Cannot create MachineState from invalid block"

  let (Block xs) = block
  let fronts = [| for x in xs -> Array.ofList x |]
  let n = fronts.Length
  let zeroState() =
    [| 
      yield Array.zeroCreate (inSize block)
      for front in xs ->
        Array.zeroCreate (outSize <| Block [front])
    |]

  let mutable state: bool[][] = zeroState()

  member s.Block with get() = block
  member s.State with get() = state

  member s.Clear() = state <- zeroState()
  member s.Step() =
    let newState = Array.map Array.copy state
    newState.[0] <- Array.zeroCreate newState.[0].Length
    for i in 0 .. n - 1 do
      let i1 = i + 1
      let mutable j = 0
      let mutable j1 = 0
      let front = fronts.[i]
      for e in front do
        match e with
        | Identity m ->
          Array.blit state.[i] j newState.[i1] j1 m
          j <- j + m
          j1 <- j1 + m

        | Permute p ->
          let p1 = Perm.apply p state.[i].[j .. j + p.Length - 1]
          Array.blit p1 0 newState.[i1] j1 p.Length
          j <- j + p.Length
          j1 <- j1 + p.Length

        | TGate d ->
          let jx, jc = j, j + 1
          let jm, jp, jc' =
             match d with
             | MinusPlus -> j1, j1 + 1, j1 + 2
             | PlusMinus -> j1 + 1, j1, j1 + 2

          let c = state.[i].[jc]
          newState.[i1].[jc'] <- c 
          newState.[i1].[if c then jp else jm] <- state.[i].[jx]
          newState.[i1].[if c then jm else jp] <- false
          j <- j + 2
          j1 <- j1 + 3

        | TGateInv d ->
          let jm, jp, jc' =
             match d with
             | MinusPlus -> j, j + 1, j + 2
             | PlusMinus -> j + 1, j, j + 2
          let jx, jc = j1, j1 + 1

          let c = state.[i].[jc']
          let from = state.[i].[if c then jp else jm]
          let other = state.[i].[if c then jm else jp]
          let operands = (state.[i].[jp], state.[i].[jm], c)
          if (state.[i].[jp] && state.[i].[jm]) || (not from && other) then
            raise <| TGateInvError operands

          newState.[i1].[jc] <- c 
          newState.[i1].[jx] <- from
          j <- j + 3
          j1 <- j1 + 2

    state <- newState

  override ms.ToString() =
    let f (ba : bool[]) =
      new string(Array.map (fun b -> if b then '1' else '0') ba)

    sprintf "MachineState %A" (block, state |> Array.map f)

