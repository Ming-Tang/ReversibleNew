module Reversible.Perm

[<AutoOpen>]
type Perm = private Perm of int array with
  member perm.ToArray() =
    let (Perm p) = perm
    Array.copy p

  member perm.Length
    with get() =
      let (Perm p) = perm
      p.Length

let identity n = Perm [| 0 .. n - 1 |]

let reverse n = Perm (Array.rev [| 0 .. n - 1 |])

let isIdentity p = p = identity p.Length

let create (xs: int seq) : Perm =
  let arr: int array = Array.ofSeq xs
  if (Set.ofSeq xs).Count < arr.Length then
    failwith "perm: repeat elements"
  if arr |> Seq.filter (fun x -> x < 0 || x >= arr.Length)
         |> Seq.isEmpty |> not then
    failwith "perm: invalid index"
  Perm(arr)

let expand (ws: int seq) (Perm p) =
  seq {
    let ws = Array.ofSeq ws
    let offs = Seq.scan (fun x y -> x + y) 0 ws |> Array.ofSeq
    for i in p do
      yield! seq { offs.[i] .. offs.[i + 1] - 1 }
  }
  |> create

let invert (Perm p) : Perm =
  let arr = Array.init p.Length (fun _ -> 0)
  for i in 0 .. p.Length - 1 do
    arr.[p.[i]] <- i

  create arr

let apply' (Perm p) (arr : _ array) =
  seq { for i in p -> arr.[i] }

let apply p arr =
  apply' p arr |> Array.ofSeq

let compose g (Perm f) =
  Perm (apply g f)

