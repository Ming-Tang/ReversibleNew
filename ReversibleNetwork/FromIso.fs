module ReversibleNetwork.FromIso
open ReversibleArith.Iso
open Builders
open Builders.Operators

let (|FEffId|_|) f =
  match f with
  | FId (Some n) -> Some n
  | FAddDigit(0, b) -> Some b
  | FNum bs -> Some (List.sum bs)
  | FAssoc (Some(a, b, c)) -> Some (a + b + c)
  | _ -> None

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

let rec (|EffId|_|) f =
  match f with
  | SCompose [] -> None
  | SFunc (FEffId n) -> Some n
  | SSym (EffId n) -> Some n
  | SPair(EffId a, EffId b) -> Some (a + b)
  | SCompose [x] -> (|EffId|_|) x
  | SCompose [EffId a; EffId b] when a = b -> Some a
  | SCompose [EffId a; EffId b] -> failwith $"EffId: non-conformable compose {a} {b}"
  | SCompose ((EffId n) :: xs) when List.forall ((|EffId|_|) >> Option.isSome) xs -> Some n
  | _ -> None

let rec (|Cond'|_|) f =
  match f with
  | PFRep 2 -> Some(1, 2)
  | PFCond(i, n) -> Some(i, n)
  | PFCondLast n -> Some(n - 1, n)
  | _ -> None

let rec (|MultiCond|_|) f =
  match f with
  | SCompose [SPFunc(Cond'(i0, n0), [MultiCond(ns, f)]); SPair(g, EffId _)] -> 
    Some((i0, n0, Some g) :: ns, f)
  | SCompose [SPFunc(Cond'(i0, n0), [f]); SPair(g, EffId _)] -> 
    Some([i0, n0, Some g], f)
  | SPFunc(Cond'(i, n), [f]) -> Some([n, i, None], f)
  | SPFunc(Cond'(i0, n0), [MultiCond(ns, f)]) ->
    Some((i0, n0, None) :: ns, f)
  | _ -> None

let fromPFunc x f =
  match x with
  | PFRep n -> condRepeat n f
  | PFCond(i, n) -> cond n i f
  | PFCondLast n -> cond n (n - 1) f

let rec preSimplify f =
  match f with
  | SSym f -> SSym (preSimplify f)
  | SPair(a, b) -> SPair(preSimplify a, preSimplify b)
  | SCompose [] -> SCompose []
  | SCompose [a] -> preSimplify a
  | SCompose [EffId _; b] -> preSimplify b
  | SCompose [a; EffId _] -> preSimplify a
  | SCompose [a; b] -> SCompose [preSimplify a; preSimplify b]
  | SCompose ((x0 :: _) as xs) -> 
    let filtered = List.filter ((|EffId|_|) >> Option.isNone) xs
    match filtered with
    | [] -> preSimplify x0
    | [x] -> x
    | xs -> SCompose (List.map preSimplify xs)
  | SGroup(_, g) -> preSimplify g
  | SFunc _ -> f
  | SPFunc(p, fs) -> SPFunc(p, List.map preSimplify fs)

let fromSymIso simplify f =
  let rec recurse f =
    match f with
    | MultiCond(ps & (_ :: _ :: _), f) -> 
      let ps' = ps |> List.map (fun (a, b, c) -> a, b, Option.map recurse c)
      mcond ps' (recurse f)
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

  recurse (preSimplify (preSimplify f))

