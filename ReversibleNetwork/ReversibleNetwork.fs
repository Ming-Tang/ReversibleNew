﻿namespace ReversibleNetwork

[<AutoOpen>]
module Types =
  type Vertex = string list
  type Prefix = string list
  type SplitDir = SDForward | SDBackward 

  let inverseDir =
    function
    | SDForward -> SDBackward
    | SDBackward -> SDForward

  type Split =
    {
      CIn : Vertex
      COut : Vertex
      XIn : Vertex
      XOutPlus : Vertex
      XOutMinus : Vertex
      Dir : SplitDir
    }

  type Network =
    {
      Vertices : Set<Vertex>
      Edges : Map<Vertex, Vertex>
      Splits : Set<Split>
      Inputs : Vertex list
      Outputs : Vertex list
    }

  let inline split ((cIn, cOut, xIn, xOutPlus, xOutMinus), sd) =
    { CIn = cIn; COut = cOut; XIn = xIn; XOutPlus = xOutPlus; XOutMinus = xOutMinus; Dir = sd }

  let inline splitToTuple { CIn = cIn; COut = cOut; XIn = xIn; XOutPlus = xOutPlus; XOutMinus = xOutMinus; Dir = sd } =
    (cIn, cOut, xIn, xOutPlus, xOutMinus), sd

  let inline (|Split|) s = splitToTuple s

  let inline splitToList s = 
    let (a, b, c, d, e), sd = splitToTuple s
    [a; b; c; d; e], sd

  let inline (|SplitList|) s = splitToList s

[<RequireQualifiedAccess>]
module Split =
  let inline create ((cIn, cOut, xIn, xOutPlus, xOutMinus), sd) = 
    { CIn = cIn; COut = cOut; XIn = xIn; XOutPlus = xOutPlus; XOutMinus = xOutMinus; Dir = sd }

  let inline map f (Split((a, b, c, d, e), sd)) = create((f a, f b, f c, f d, f e), sd)
  let inline mapIn f (Split((a, b, c, d, e), sd)) = create((f a, b, f c, d, e), sd)
  let inline mapOut f (Split((a, b, c, d, e), sd)) = create((a, f b, c, f d, f e), sd)
  let inline inverse (Split(tup, sd)) = create(tup, inverseDir sd)

  let inline ins s = [s.CIn; s.XIn]
  let inline outs s = [s.COut; s.XOutPlus; s.XOutMinus]

  let inline insOuts ({ Dir = d } as s) =
    match d with
    | SplitDir.SDForward -> (ins s, outs s)
    | SplitDir.SDBackward -> (outs s, ins s)

  let inline fromList sd x =
    match x with 
    | [a; b; c; d; e] -> create ((a, b, c, d, e), sd)
    | _ -> failwith "Split.fromList: length != 5"

  let inline toList (Split((a, b, c, d, e), sd)) = [a; b; c; d; e]

