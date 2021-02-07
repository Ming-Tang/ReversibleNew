namespace ReversibleNetwork

[<AutoOpen>]
module Types =
  type Vertex = string list
  type Prefix = string list
  type SplitDir = SDBuffer | SDForward | SDBackward 

  let inverseDir =
    function
    | SDBuffer -> SDBuffer
    | SDForward -> SDBackward
    | SDBackward -> SDForward

  type Gate =
    {
      CIn : Vertex
      COut : Vertex
      XIn : Vertex
      XOutPlus : Vertex
      XOutMinus : Vertex
      Buffer : (Vertex * Vertex) list
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

  let empty =
    let ev = []
    { CIn = ev; COut = ev; XIn = ev; XOutPlus = ev; XOutMinus = ev; Buffer = []
      Dir = SplitDir.SDBuffer }

  let inline splitToTuple { CIn = cIn; COut = cOut; XIn = xIn; XOutPlus = xOutPlus; XOutMinus = xOutMinus; Dir = sd } =
    (cIn, cOut, xIn, xOutPlus, xOutMinus), sd

  let inline getBuffer { Buffer = b } = b

  let inline (|Split|Buffer|) (s : Gate) = 
    match s.Dir with
    | SDBuffer -> Buffer(getBuffer s)
    | SDForward | SDBackward -> Split(splitToTuple s)

  let inline Buffer b = { empty with Dir = SplitDir.SDBuffer; Buffer = b }

  let inline Split ((cIn, cOut, xIn, xOutPlus, xOutMinus), sd) = 
    { CIn = cIn; COut = cOut; XIn = xIn; XOutPlus = xOutPlus; XOutMinus = xOutMinus; Dir = sd; Buffer = [] }

[<RequireQualifiedAccess>]
module Gate =
  let inline map f s =
    match s with
    | Buffer bs -> Buffer(List.map (fun (a, b) -> f a, f b) bs)
    | Split((a, b, c, d, e), sd) -> Split((f a, f b, f c, f d, f e), sd)

  let inline mapInConns f s =
    match s with
    | Buffer bs -> Buffer(List.map (fun (a, b) -> f a, b) bs)
    | Split((a, b, c, d, e), sd) -> Split((f a, b, f c, d, e), sd)

  let inline mapOutConns f s =
    match s with
    | Buffer bs -> Buffer(List.map (fun (a, b) -> a, f b) bs)
    | Split((a, b, c, d, e), sd) -> Split((a, f b, c, f d, f e), sd)

  let inline inverse s = 
    match s with 
    | Buffer bs -> Buffer(List.map (fun (a, b) -> b, a) bs)
    | Split(tup, sd) -> Split(tup, inverseDir sd)

  let inline private inConns s = [s.CIn; s.XIn]
  let inline private outConns s = [s.COut; s.XOutPlus; s.XOutMinus]

  let inline insOuts ({ Dir = d; Buffer = bs } as s) =
    match d with
    | SDBuffer -> List.unzip bs
    | SDForward -> inConns s, outConns s
    | SDBackward -> outConns s, inConns s

  let inline mapOuts f s =
    match s.Dir with
    | SDBuffer -> mapOutConns f s
    | SDForward -> mapOutConns f s
    | SDBackward -> mapInConns f s

  let inline fromList sd xs =
    match sd with
    | SplitDir.SDBuffer -> invalidArg "sd" "Gate.fromList: cannot be SDBuffer"
    | _ ->
      match xs with 
      | [a; b; c; d; e] -> Split((a, b, c, d, e), sd)
      | _ -> invalidArg "xs" "Split.fromList: length != 5"

  let inline toList s =
    match s with
    | Buffer bs -> let a, b = List.unzip bs in a @ b
    | Split((a, b, c, d, e), _) -> [a; b; c; d; e]

