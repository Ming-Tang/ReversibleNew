module ReversibleNetwork.FromIso
open ReversibleNetwork.Network
open ReversibleArith.Iso
open Builders
open Builders.Operators

let fromFunc x =
  match x with
  | FId (Some n) -> identity n
  | FNum bs -> identity (List.sum bs)
  | FSucc n -> rotate n 1
  | FAddDigit(k, n) -> rotate n k
  | FComm(Some(a, b)) -> comm a b
  | FAssoc(Some(a, b, c)) -> identity (a + b + c)
  | FId _ | FComm _ | FAssoc _ -> failwith $"fromSymIsoFunc: Missing size: %A{x}"

let fromPFunc x f =
  match x with
  | PFRep n -> condRepeat n f
  | PFCond(i, n) -> cond n i f
  | PFCondLast n  -> cond n (n - 1) f

let fromSymIso simplify f =
  let rec recurse f =
    match f with
    | SGroup(n, g) -> recurse g |> prefix [n]
    | SFunc f -> fromFunc f
    | SPFunc(p, [f]) -> fromPFunc p (recurse f)
    | SSym f -> ~~(recurse f)
    | SPair(a, b) -> recurse a &&& recurse b
    | SCompose([]) -> failwith "fromSymIso: empty compose"
    | SCompose xs -> List.map recurse xs |> List.reduce (>>>)
    | SPFunc(_, _) as f -> failwith $"fromSymIso: invalid SPFunc: %A{f}"
    |> simplify

  recurse f
