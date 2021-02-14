module ReversibleNetwork.FromIso
open ReversibleArith.Iso
open Builders
open Builders.Operators

let fromFunc x =
  match x with
  | FId (Some n) -> identity n
  | FNum bs -> identity (List.sum bs)
  | FSucc n -> rotate n 1
  | FCompl n -> reverse n
  | FAddDigit(k, n) -> rotate n k
  | FComm(Some(a, b)) -> comm a b
  | FAssoc(Some(a, b, c)) -> identity (a + b + c)
  | FId _ | FComm _ | FAssoc _ -> failwith $"fromSymIsoFunc: Missing size: %A{x}"

let isIdentity f =
  match f with
  | SFunc (FId _) | SSym (SFunc (FId _)) -> true
  | _ -> false

let rec (|MultiCond|_|) f =
  match f with
  | SPFunc(PFCond(i, n), [f]) -> Some ([n, i, None], f)
  | SPFunc(PFCond(i0, n0), [MultiCond(ns, f)]) -> Some ((n0, i0, None) :: ns, f)
  | _ -> None

let fromPFunc x f =
  match x with
  | PFRep n -> condRepeat n f
  | PFCond(i, n) -> cond n i f
  | PFCondLast n -> cond n (n - 1) f

let rec preSimplify f =
  match f with
  | SSym f -> SSym (preSimplify f)
  | SPair(a, b) -> preSimplify (SPair(a, b))
  | SCompose [] -> SCompose []
  | SCompose [a] -> preSimplify a
  | SCompose ((x :: _) as xs) -> 
    let c' = SCompose (List.filter (isIdentity >> not) xs) 
    match c' with
    | SCompose [] -> x
    | _ -> c'
  | SGroup(_, g) -> preSimplify g
  | SFunc _ -> f
  | SPFunc(p, fs) -> SPFunc(p, List.map preSimplify fs)

let fromSymIso simplify f =
  let rec recurse f =
    match f with
    | MultiCond(ps & (_ :: _ :: _), f) -> mcond ps (recurse f)
    | SGroup(_, g) -> recurse g
    | SFunc f -> fromFunc f
    | SPFunc(PFRep n, [SFunc (FSucc n')]) when n = n' -> 
      seq {
        for i in 0 .. n - 1 ->
          cond n i (rotate n i)
      }
      |> Seq.rev
      |> Seq.reduce (>>>)
    | SPFunc(p, [f]) -> fromPFunc p (recurse f)
    | SSym (SFunc (FNum bs)) -> identity (List.sum bs)
    | SSym (SFunc (FAssoc(Some(a, b, c)))) -> identity (a + b + c)
    | SSym (SFunc (FId (Some n))) -> identity n 
    | SSym (SFunc (FSucc n)) -> rotate n (-1)
    | SSym (SFunc (FCompl n)) -> reverse n
    | SSym (SFunc (FAddDigit(k, n))) -> rotate n (-k)
    | SSym f -> ~~(recurse f)
    | SPair(a, b) -> recurse a &&& recurse b
    | SCompose [x; y] -> recurse x >>> recurse y
    | SCompose [x] -> recurse x
    | SCompose [] -> failwith "fromSymIso: empty compose"
    | SCompose xs -> List.map recurse xs |> List.reduce (>>>)
    | SPFunc(_, _) as f -> failwith $"fromSymIso: invalid SPFunc: %A{f}"

  recurse (preSimplify f)

