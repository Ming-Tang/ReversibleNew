module ReversibleArith.Iso
open System.Text.RegularExpressions

module Widths =
  open System
  open System.Collections.Generic
  let widths : Dictionary<Type, int> = Dictionary()
  let add t i = widths.[t] <- i
  let rec get (t : Type) = 
    if widths.ContainsKey(t) then
      Some widths.[t]
    elif t.IsGenericType && t.GetGenericTypeDefinition() = typedefof<unit * unit> then
        match t.GetGenericArguments() with
        | [| a; b |] -> Option.map2 (+) (get a) (get b)
        | _ -> None
    else
      None

  let addToWidths t x = widths.[t] <- x

  let inline getFrom<'t>() = 
    let t = typeof<'t>
    let res = get t 
    if not <| widths.ContainsKey(t) then
      if Option.isNone res then
        eprintfn "failed: %O" t
      res |> Option.iter (addToWidths t)
    res

type SymIsoType =
| TNum of int list
| TDigit of int
| TPair of SymIsoType * SymIsoType

type SymIsoFunc =
| FId of int option
| FNum of _bases : int list
| FSucc of _base : int
| FAddDigit of n : int * _base : int
| FComm of (int * int) option
| FAssoc of (int * int * int) option

type SymIsoPFunc =
| PFRep of _base : int
| PFCond of value : int * _base : int
| PFCondLast of _base : int

let private patSub = new Regex(@"_\{.+\}$")
let funcNameLaTeX' =
  function
  | FId None -> sprintf "I"
  | FId (Some n) -> sprintf "I_{%d}" n
  | FNum [b] ->
    sprintf "N_{%d}" b
  | FNum (b :: bs) ->
    Seq.map string bs
    |> String.concat ", "
    |> sprintf "N_{%d,(%s)}" b
  | FNum bs ->
    Seq.map string bs
    |> String.concat ", "
    |> sprintf "N_{%s}"
  | FAddDigit(i, b) -> sprintf "A(%d)_{%d}" i b
  | FSucc b -> sprintf "S_{%d}" b
  | FComm None -> "C"
  | FComm (Some(a, b)) -> sprintf "C_{%d,%d}" a b
  | FAssoc None -> "A"
  | FAssoc (Some(a, b, c)) -> sprintf "A_{(%d,%d),%d}" a b c

let funcNameLaTeX x = patSub.Replace(funcNameLaTeX' x, "")
  
let pFuncNameLaTeX' =
  function
  | PFRep b -> sprintf "R_{%d}" b
  | PFCond (i, b) -> sprintf "C_{%d,%d}" i b
  | PFCondLast b -> sprintf "CL_{%d}" b

let pFuncNameLaTeX x = patSub.Replace(pFuncNameLaTeX' x, "")

type SymIso =
| SGroup of string * SymIso
| SFunc of SymIsoFunc
| SPFunc of SymIsoPFunc * SymIso list
| SSym of SymIso
| SPair of SymIso * SymIso
| SCompose of SymIso list

let rec symIsoToObj si : obj =
  let compose (fs : obj) (gs : obj) : obj list =
    match fs, gs with
    | (:? list<obj> as fs'), (:? list<obj> as gs') -> fs' @ gs'
    | (:? list<obj> as fs'), _ -> fs' @ [gs]
    | _, (:? list<obj> as gs') -> [fs] @ gs'
    | _ -> [fs; gs]
  match si with
  | SGroup(_, g) -> symIsoToObj g
  | SSym s -> box ("$sym", symIsoToObj s)
  | SFunc f -> box f
  | SPFunc(s, xs) -> box (s, List.map symIsoToObj xs)
  | SPair(a, b) -> box (symIsoToObj a, symIsoToObj b)
  | SCompose [] -> box "id"
  | SCompose [x] -> symIsoToObj x
  | SCompose xs -> 
    xs 
    |> List.map symIsoToObj 
    |> List.reduce (fun a b -> box (compose a b)) 
    |> box

let rec symIsoToLaTeX depth si : string =
  let rec flattenCompose xs =
    let expandCompose = function SCompose xs -> xs | x -> [x]
    xs 
    |> List.map expandCompose
    |> List.concat

  let up s = sprintf "\\mathrm{%s}" s
  let op s = sprintf "\\operatorname{%s}" s
  let recurse = symIsoToLaTeX depth
  match si with
  | SGroup(n, g) -> 
    match depth with
    | None -> symIsoToLaTeX None g
    | Some 0 -> " \\ldots "
    | Some i -> symIsoToLaTeX (Some (i - 1)) g
    |> sprintf " \\stackrel{\\rm %s}{\\boxed{%s}} " n
  | SSym(SFunc s) -> sprintf "!%s" (up <| funcNameLaTeX s)
  | SSym s -> sprintf "!\\left[ %s \\right]" (recurse s)
  | SFunc f -> up (funcNameLaTeX f)
  | SPFunc(s, xs) -> 
    sprintf "\\stackrel{\\large\\langle %s \\rangle}{\\boxed{%s}}" 
      (op <| pFuncNameLaTeX s) 
      (List.map recurse xs |> String.concat " , ")
  | SPair(a, b) -> sprintf "\\begin{pmatrix} %s \\\\ %s \\end{pmatrix}" (recurse a) (recurse b)
  | SCompose [] -> "I"
  | SCompose [x] -> recurse x
  | SCompose xs -> 
    xs 
    |> flattenCompose
    |> List.map recurse
    |> String.concat " " // " \\cdot "
    |> sprintf " %s "

type Iso<'a, 'b> = Iso of f : ('a -> 'b) * g : ('b -> 'a) * si : SymIso Lazy

type BIso<'a, 'b> = unit -> Iso<'a, 'b>
let inline LIso(f, g, s) : BIso<_, _> = fun () -> Iso(f, g, s)
let inline BIso(f, g, s) : BIso<_, _> = fun () -> Iso(f, g, s)
let inline (|BIso|) (x : BIso<_, _>) = match x() with Iso(f, g, s) -> f, g, s

let group n (BIso(a, b, s)) = BIso(a, b, lazy SGroup(n, s.Value))

// let showBIso (BIso(_, _, s)) = (sprintf "%A" <| symIsoToObj s).Replace("\"", "")
let showBIso n (BIso(_, _, s)) = sprintf "%s" <| symIsoToLaTeX n s.Value
let showBIso' (BIso(_, _, s)) = sprintf "%A" s.Value

let (<<|) (BIso(f, _, _)) x = f x
let (>>>) (BIso(f, f', fs)) (BIso(g, g', gs)) = 
  BIso(f >> g, g' >> f', lazy SCompose [fs.Value; gs.Value])

let (&&&) (BIso(f, f', fs)) (BIso(g, g', gs)) =
  BIso((fun (x, y) -> (f x, g y)), (fun (x, y) -> (f' x, g' y)), lazy SPair(fs.Value, gs.Value))

let sym (BIso(a, b, s)) =
  BIso(b, a, lazy SSym s.Value)

let inline (~~) x = sym x

let id : BIso<'a, 'a> = fun _ ->
  Iso((fun x -> x), (fun x -> x), lazy SFunc(FId <| Widths.getFrom<'a>()))

let comm : BIso<'a * 'b, 'b * 'a> = fun _ ->
  Iso((fun (x, y) -> y, x), (fun (x, y) -> y, x), 
      lazy (let wa, wb = Widths.getFrom<'a>(), Widths.getFrom<'b>()
            in SFunc(FComm <| Option.map2 (fun a b -> a, b) wa wb)))

let assoc : BIso<('a * 'b) * 'c, _> = fun _ ->
  Iso((fun ((x, y), z) -> x, (y, z)), (fun (x, (y, z)) -> (x, y), z), 
      lazy (let wa, wb, wc = Widths.getFrom<'a>(), Widths.getFrom<'b>(), Widths.getFrom<'c>()
            SFunc (FAssoc <| Option.map3 (fun a b c -> a, b, c) wa wb wc)))

let repConst n f =
  let rec repConst' = 
    function
    | 0 -> id
    | i -> f >>> (repConst' (i - 1))

  repConst' n
  |> group (sprintf "repConst(%d, \\ldots)" n)
