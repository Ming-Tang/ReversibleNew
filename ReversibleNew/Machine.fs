module Reversible.Machine
open Reversible

type TDir =
| PlusMinus
| MinusPlus

type Element =
| Identity of int
| Permute of Perm.Perm
| TGate of TDir // 2 -> 3
| TGateInv of TDir // 3 -> 2

let convertIdentityPerms = function
  | Permute p when Perm.isIdentity p -> Identity p.Length
  | e -> e

let elementInSize = function
  | Identity n when n <= 0 -> 0
  | Identity n -> n
  | Permute p -> p.Length
  | TGate _ -> 2
  | TGateInv _ -> 3
  
let elementOutSize = function
  | Identity n when n <= 0 -> 0
  | Identity n -> n
  | Permute p -> p.Length
  | TGate _ -> 3
  | TGateInv _ -> 2

let isTGate = function
  | TGate _ | TGateInv _ -> true
  | _ -> false

let inverseElement =
  function
  | Identity n -> Identity n
  | Permute p -> Permute (Perm.invert p)
  | TGate d -> TGateInv d
  | TGateInv d -> TGate d

type Block = Block of Element list list

let elem x = Block [[x]]

let depth (Block es) = es.Length

let inSize (Block es) =
  match es with
  | [] -> 0
  | xs :: _ -> Seq.sumBy elementInSize xs
  
let outSize (Block es) =
  match List.rev es with
  | [] -> 0
  | xs :: _ -> Seq.sumBy elementOutSize xs

// let rec mergeIdentities =
//   function
//   | Identity a :: Identity b :: Identity c :: xs' -> Identity (a + b + c) :: xs'
//   | Identity a :: Identity b :: xs' -> Identity (a + b) :: xs'
//   | x :: xs' -> x :: mergeIdentities xs'
//   | [] -> []

let normalize (Block xs) =
  xs 
  |> List.filter (List.isEmpty >> not)
  |> List.map (List.filter (elementInSize >> (<>) 0) >> List.map convertIdentityPerms)
  |> Block

let rec private checkFronts prev =
  function
  | [] -> true
  | [x] ->
    let sa = inSize (Block [x])
    Option.isNone prev || (Some sa = prev)
  | x :: xs ->
    let sa = inSize (Block [x])
    let sb = outSize (Block [x])
    (Option.isNone prev || (Some sa = prev)) && (
      checkFronts (Some sb) xs
    )

let isValid = 
  function
  | Block [] -> false
  | Block xs ->
    ((Block xs) = normalize (Block xs)) && checkFronts None xs

let hstack (Block a) (Block b) =
  if a = [] then Block b
  elif b = [] then Block a
  else
    let sa, sb = outSize (Block a), inSize (Block b)
    if sa <> sb then
      failwithf "hstack: Different sizes: %d %d" sa sb
    Block (a @ b)

let vstack (Block xs) (Block ys) =
  let rec vstk (a0, b0) (xs, ys) =
    match xs, ys with
    | x :: xs', y :: ys' -> 
      vstk (outSize (Block [x]), outSize (Block [y])) (xs', ys')
      |> hstack (Block [x @ y])
    | [], _ -> Block [ for y in ys -> Identity a0 :: y ]
    | _, [] -> Block [ for x in xs -> x @ [Identity b0] ]
  
  match xs, ys with
  | zs, [] | [], zs -> Block xs
  | _, _ -> vstk (0, 0) (xs, ys)

let inverse (Block xs) =
  xs
  |> List.rev
  |> List.map (List.map inverseElement)
  |> Block

