namespace ReversibleNetwork

[<AutoOpen>]
module Types =
  type Vertex = string list
  type Prefix = string list
  type SplitDir = SDForward | SDBackward 

  let inverseDir =
    function
    | SDForward -> SDBackward
    | SDBackward -> SDForward

  type Gate =
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
      Gates : Set<Gate>
      Inputs : Vertex list
      Outputs : Vertex list
    }

  let inline split ((cIn, cOut, xIn, xOutPlus, xOutMinus), sd) =
    { CIn = cIn; COut = cOut; XIn = xIn; XOutPlus = xOutPlus; XOutMinus = xOutMinus; Dir = sd }

  let inline splitToTuple { CIn = cIn; COut = cOut; XIn = xIn; XOutPlus = xOutPlus; XOutMinus = xOutMinus; Dir = sd } =
    (cIn, cOut, xIn, xOutPlus, xOutMinus), sd

  let inline (|Split|) s = splitToTuple s

  let inline Split ((cIn, cOut, xIn, xOutPlus, xOutMinus), sd) = 
    { CIn = cIn; COut = cOut; XIn = xIn; XOutPlus = xOutPlus; XOutMinus = xOutMinus; Dir = sd }

[<RequireQualifiedAccess>]
module Gate =
  let inline map f (Split((a, b, c, d, e), sd)) = Split((f a, f b, f c, f d, f e), sd)
  let inline mapInConns f (Split((a, b, c, d, e), sd)) = Split((f a, b, f c, d, e), sd)
  let inline mapOutConns f (Split((a, b, c, d, e), sd)) = Split((a, f b, c, f d, f e), sd)
  let inline inverse (Split(tup, sd)) = Split(tup, inverseDir sd)

  let inline private inConns s = [s.CIn; s.XIn]
  let inline private outConns s = [s.COut; s.XOutPlus; s.XOutMinus]

  let inline insOuts ({ Dir = d } as s) =
    match d with
    | SDForward -> inConns s, outConns s
    | SDBackward -> outConns s, inConns s

  let inline mapOuts f s =
    match s.Dir with
    | SDForward -> mapOutConns f s
    | SDBackward -> mapInConns f s

  let inline fromList sd x =
    match x with 
    | [a; b; c; d; e] -> Split((a, b, c, d, e), sd)
    | _ -> failwith "Split.fromList: length != 5"

  let inline toList (Split((a, b, c, d, e), _)) = [a; b; c; d; e]

