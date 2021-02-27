module ReversibleNetwork.FromIso
open ReversibleArith.Iso
open Builders
open Builders.Operators

let rec flattenCompose xs =
  [
    for x in xs do
      match x with
      | SCompose xs' ->
        for x' in flattenCompose xs' -> x'
      | SGroup(_, x) -> yield! flattenCompose [x]
      | _ -> yield x
  ]

let (|Composition|) = flattenCompose

let Composition =
  function
  | [] -> SCompose []
  | [x] -> x
  | xs -> xs |> List.reduce (fun x y -> SCompose [x; y])

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
  | SFunc (FEffId n) -> Some n
  | SSym (EffId n) -> Some n
  | SPair(EffId a, EffId b) -> Some (a + b)
  | SCompose [] -> None
  | SCompose [x] -> (|EffId|_|) x
  | SCompose (Composition xs) -> 
    if List.forall isEffId xs then (|EffId|_|) xs.[0] else None
  | _ -> None

and isEffId = (|EffId|_|) >> Option.isSome

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

let simplifyCompose pair xs =
  let rec recurse xs =
    match xs with
    | [_] | [] -> false, xs
    | x :: y :: zs ->
      match pair x y with
      | Some z -> true, snd (recurse (z :: zs))
      | None ->
        let c', yzs = recurse (y :: zs)
        c', (x :: yzs)

  let rec loop xs =
    match recurse xs with
    | true, xs' -> loop xs'
    | false, xs' -> xs'

  loop xs

let EffId n = SFunc (FId (Some n))

let rec preSimplify f =
  let preSimplifyPair a b =
    match a, b with
    | SFunc (FComm(Some(a, b))), SFunc (FComm(Some(b', a'))) when a = a' && b = b' -> 
      Some (EffId (a + b))
    | SFunc (FComm(Some(a, b))), SSym (SFunc(FComm(Some(a', b')))) when a = a' && b = b' -> 
      Some (EffId (a + b))
    | SSym (SFunc (FComm(Some(a, b)))), SFunc(FComm(Some(a', b'))) when a = a' && b = b' -> 
      Some (EffId (a + b))
    | SPair(a, EffId n), SPair(b, EffId n') when n = n' -> 
      Some (SPair(SCompose [a; b], EffId n))
    | EffId _, c | c, EffId _ -> Some c
    | _ -> None

  match f with
  | SSym f -> SSym (preSimplify f)
  | SPair(EffId a, EffId b) -> EffId(a + b)
  | SPair(EffId a, SPair(EffId b, c)) ->
    SPair(EffId(a + b), preSimplify c) |> preSimplify
  | SPair(a, b) -> 
    SPair(preSimplify a, preSimplify b)
  | SCompose [x] -> preSimplify x
  | SCompose [] -> SCompose []
  | SCompose (Composition xs) -> 
    simplifyCompose preSimplifyPair xs
    |> List.map preSimplify
    |> Composition
  | SGroup(_, g) -> preSimplify g
  | SFunc (FEffId n) -> EffId n
  | SFunc _ -> f
  | SPFunc(p, fs) -> SPFunc(p, List.map preSimplify fs)

let rec repeatPreSimplify e =
  let e' = preSimplify e
  let he, he' = hash e, hash e'
  if he <> he' || (he = he' && e <> e') then
    repeatPreSimplify e'
  else
    e'

let fromSymIso simplify f =
  let rec recurse f =
    match f with
    | MultiCond(ps & (_ :: _ :: _), f) -> makeMultiCond ps f
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
    | SCompose [a; SCompose [b; c] as r] ->
      match SCompose [a; b] with
      | MultiCond (ps & (_ :: _ :: __), f) ->
        makeMultiCond ps f >>> recurse c
      | _ -> recurse a >>> recurse r

    | SCompose [x; y] -> recurse x >>> recurse y
    | SCompose [x] -> recurse x
    | SCompose [] -> failwith "fromSymIso: empty compose"
    | SCompose xs -> List.map recurse xs |> List.reduce (>>>)
    | SPFunc(_, _) as f -> failwith $"fromSymIso: invalid SPFunc: %A{f}"

  and makeMultiCond ps f =
    let ps' = ps |> List.map (fun (a, b, c) -> a, b, Option.map recurse c)
    mcond ps' (recurse f)

  f 
  |> repeatPreSimplify
  |> recurse

