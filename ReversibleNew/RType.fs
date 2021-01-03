module Reversible.RType
open System.Collections.Generic

type Wires = bool list

let showWires (x : Wires) =
  new string(
    x
    |> Seq.map (fun x -> if x then '1' else '0')
    |> Array.ofSeq
  )

type RType =
| TBinom of int * int
| TSum of RType list
| TProd of RType list

let inline B n k = TBinom(n, k)
let inline C n = TBinom(n, 1)
let Bit = TBinom(2, 1)
let Zero = TBinom(0, 0)
let One = TBinom(1, 1)

let rec isValid = function
  | TBinom(n, k) -> n > 0 && k > 0 && n >= k
  | TProd [] | TSum [] -> false
  | TProd xs | TSum xs -> Seq.forall isValid xs

let rec limit x d = function
  | TBinom(n, _) -> n <= x
  | TProd _ | TSum _ when d <= 0 -> false
  | TProd xs | TSum xs when xs.Length < x -> Seq.forall (limit x (d - 1)) xs
  | TProd _ | TSum _ -> false

let choose n k =
  if k > n || n < 0 || k < 0 then
    0
  else
    let mutable n1 = n
    let mutable r = 1
    for d in 1 .. k do
      r <- r * n1
      n1 <- n1 - 1
      r <- r / d

    r

let rec card = function
  | TBinom(n, k) -> choose n k
  | TSum(xs) -> xs |> Seq.sumBy card
  | TProd(xs) -> xs |> Seq.map card |> Seq.fold (*) 1

let rec width = function
  | TBinom(n, _) when n < 0 -> n
  | TBinom(n, _) -> n
  | TSum(xs) | TProd(xs) -> xs |> Seq.sumBy width

let rec count = function
  | TBinom(_, k) -> Set.singleton k
  | TSum(xs) -> Set.unionMany (Seq.map count xs)
  | TProd([]) -> Set.singleton 0
  | TProd(x :: xs) ->
    seq {
      for a in count x do
        for b in count (TProd xs) do
        a + b
    }
    |> Set.ofSeq

let private combsMemo = new Dictionary<int * int, Wires[]>(128)
let rec combs n k =
  if k > n || n < 0 || k < 0 then
    Seq.empty : Wires seq
  elif n = k then
    Seq.singleton [for i in 1 .. n -> true]
  elif k = 1 then
    seq { for i in 1 .. n -> [for j in 1 .. n -> i = j] }
  else
    if combsMemo.ContainsKey((n, k)) then
      Seq.ofArray combsMemo.[(n, k)]
    else
      lock combsMemo <| fun () ->
        let res = 
          [|
            for c1 in combs (n - 1) k ->
              c1 @ [false]
            for c1 in combs (n - 1) (k - 1) ->
              c1 @ [true]
          |]

        if n <= 8 then combsMemo.Add((n, k), res)
        Seq.ofArray res

do combs 5 5 |> ignore

let empty t = List.init (width t) (fun _ -> false) : Wires

let rec vals = function
  | TBinom(n, k) -> combs n k
  | TSum(xs) ->
    seq {
      let es = xs |> Seq.mapi (fun i t -> i, empty t)
      for i, vss in xs |> Seq.mapi (fun i x -> i, vals x) do
        for vs in vss ->
          [ for j, e in es do yield! if i = j then vs else e ]
    }
  | TProd([]) -> Seq.singleton []
  | TProd(t :: ts) ->
    seq {
      for a in vals t do
        for b in vals (TProd ts) do
          yield a @ b
    }

let rec collect = function
  | TSum([]) -> Zero
  | TProd([]) -> One
  | TSum([x]) | TProd([x]) -> x
  | TSum(x1 :: xs) ->
    let xs' = List.map collect xs
    let x1', x2' = collect x1, collect (TSum xs')

    match x1', x2' with
    | TSum x1s, TSum x2s -> TSum(x1s @ x2s)
    | TSum x1s, x2 -> TSum(x1s @ [x2])
    | x1, TSum x2s -> TSum(x1 :: x2s)
    | x1, x2 -> TSum([x1; x2])

  | TProd(x1 :: xs) ->
    let xs' = List.map collect xs
    let x1', x2' = collect x1, collect (TProd xs')

    match x1', x2' with
    | TProd x1s, TProd x2s -> TProd(x1s @ x2s)
    | TProd x1s, x2 -> TProd(x1s @ [x2])
    | x1, TProd x2s -> TProd(x1 :: x2s)
    | x1, x2 -> TProd([x1; x2])

  | b -> b

