module Reversible.MachineBuilder
open Reversible.Machine

let T dir = elem (TGate dir)

let I n = elem (Identity n)

let vert = List.reduce vstack

let horiz = List.reduce hstack

let matrix = List.map vert >> horiz 

let P p =
  Permute p |> elem

let R n =
  Perm.reverse n |> P

let S a b =
  Perm.reverse 2
  |> Perm.expand [a; b] 
  |> Permute
  |> elem

let rec Tn dir = function
  | 1 -> elem (TGate dir)
  | n' -> 
    let n = n' - 1
    matrix [
      [ T dir; I n ]
      [ I 2; Tn dir n ]
      [ I 1; S 1 n; I (n + 1) ]
    ]

let rec cperm (p : Perm.Perm) =
  let n = p.Length
  let n2 = 2 * n
  matrix [
    [ I 1; Tn PlusMinus n ]
    [ I 1; S n2 1 ]
    [ I 2; P p; I n ]
    [ R 2; S n2 n2 ]
    [ I 1; inverse (Tn MinusPlus n) ]
    [ I 1; S n 1 ]
    [ R 2; I n ]
  ]

