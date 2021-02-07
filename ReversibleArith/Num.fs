module ReversibleArith.Num
open System.Collections.Generic

type IBases =
  abstract member Bases : int list

let inline getBases (x : #IBases) = x.Bases
let inline (|Bases|) (x : #IBases) = getBases x

type IMapUnmap =
  abstract member Map : int -> int list
  abstract member Unmap : int list -> int option

type INum =
  abstract member NumberValue : int
  abstract member Digits : int list
  abstract member Base : int
  abstract member Mod : int
  inherit IBases
  inherit IMapUnmap

type IFromDigits<'a when 'a :> INum> =
  abstract member FromDigits : int list -> 'a

type INum<'a when 'a :> INum> =
  inherit INum
  inherit IFromDigits<'a>

let inline modValue x = (x :> INum).Mod
let inline numberValue (x : #INum) = x.NumberValue
let inline baseValue (x : #INum) = x.Base

type IBase =
  abstract member Base : int

let inline getBase (b : #IBase) = b.Base

let inline (|Base|) x = getBase x

type MkBase = MkBase of int with
  interface IBase with
    member x.Base = match x with MkBase i -> i

type B2 = B2 with
  interface IBase with member b.Base = 2

type B3 = B3 with
  interface IBase with member b.Base = 3

type B4 = B4 with
  interface IBase with member b.Base = 4

type B5 = B5 with
  interface IBase with member b.Base = 5

type B6 = B6 with
  interface IBase with member b.Base = 6

type B7 = B7 with
  interface IBase with member b.Base = 7

type B8 = B8 with
  interface IBase with member b.Base = 8

type B9 = B9 with
  interface IBase with member b.Base = 9

type B10 = B10 with
  interface IBase with member b.Base = 10
  
let inline mkBase x = 
  match x with
  | 2 -> B2 :> IBase
  | 3 -> B3 :> IBase
  | 4 -> B4 :> IBase
  | 5 -> B5 :> IBase
  | 6 -> B6 :> IBase
  | 7 -> B7 :> IBase
  | 8 -> B8 :> IBase
  | 9 -> B9 :> IBase
  | 10 -> B10 :> IBase
  | x when x <= 1 -> failwithf "mkBase: invalid base: %d" x
  | _ -> MkBase x :> IBase

type Digit<'b when 'b :> IBase> = Digit of digit : int * _base : 'b with
  member inline d.DecomposeDigit() =
    match d with Digit(d, b) -> d, b

  interface IFromDigits<Digit<'b>> with
    member d.FromDigits ds =
      match d with Digit(_, b) -> Digit(ds.[0] % getBase b, b)

  interface INum with
    member d.NumberValue =
      match d with Digit(d, _) -> d

    member d.Digits =
      match d with Digit(d, _) -> [d]

    member d.Base =
      match d with Digit(_, b) -> getBase b

    member d.Bases =
      match d with Digit(_, b) -> [getBase b]

    member d.Mod = (d :> INum).Base

    member d.Map i = [i % (d :> INum).Base]

    member d.Unmap xs = 
      let m = (d :> INum).Mod
      match xs with
      | [i] when i >= 0 && i < m -> Some i
      | _ -> None

let succDigit (Digit(d, (Base b as b'))) = Digit((d + 1) % b, b')
let predDigit (Digit(d, (Base b as b'))) = Digit((d + b - 1) % b, b')

let addDigit k (Digit(d, (Base b as b'))) = Digit((d + k) % b, b')
let subDigit k (Digit(d, (Base b as b'))) = Digit((d + b - (k % b)) % b, b')

let complDigit (Digit(d, (Base b as b'))) = Digit((b - d - 1) % b, b')

let inline checkedPM a b c = Checked.(+) a (Checked.(*) b c)

type Num<'b, 'n when 'b :> IBase and 'n :> INum> = Num of Digit<'b> * 'n with
  member inline d.DecomposeNum() =
    match d with Num(d, b) -> d, b

  interface IFromDigits<Num<'b, 'n>> with
    member n.FromDigits ds =
      match n, ds with 
      | Num(x, y), i :: ds -> 
        Num((x :> IFromDigits<_>).FromDigits([i]), (unbox (box y) :> IFromDigits<'n>).FromDigits ds)
      | _ -> failwith "Num.FromDigits: not enough digits"

  interface INum with
    member n.Bases =
      match n with
      | Num(d, Bases ns) -> [baseValue d] @ ns

    member n.Digits =
      match n with
      | Num(d, ds) -> [numberValue d] @ (ds :> INum).Digits

    member n.NumberValue =
      match n with 
      | Num(x, y) -> checkedPM (numberValue x) (baseValue x) (numberValue y)

    member n.Base =
      (n :> INum).Mod

    member n.Mod = 
      match n with Num(d, r) -> Checked.(*) (baseValue d) r.Mod

    member n.Map i =
      match n with 
      | Num(x, y) -> (i % baseValue x) :: y.Map(i / baseValue x)

    member n.Unmap xs = 
      match xs with
      | [] -> None
      | x :: xs ->
        match n with
        | Num(d, y) -> 
          let b = baseValue d
          (d :> INum).Unmap [x]
          |> Option.bind (fun i ->
            ((y :> INum).Unmap xs)
            |> Option.map (fun l -> checkedPM i l b)
          )

let unNum (Num(a, b)) = a, b
let mkNum (a, b) = Num(a, b)

let toBools (d : #INum) =
  [|
    for i, b in Seq.zip d.Digits d.Bases do
      for j in 0 .. b - 1 -> j = i
  |]

let fromBools (d : 'a when 'a :> IBases) (arr : bool[]) =
  let mutable digits = []
  let mutable i0 = 0
  [
    for b in d.Bases do
      let slice = arr.[i0 .. i0 + b - 1]
      i0 <- i0 + b
      (
        try 
          Array.findIndex id slice
        with
        | :? KeyNotFoundException -> invalidArg "arr" "Invalid format: all false"
      )
  ]

let inline fromDigits (d : #IFromDigits<_>) ds = d.FromDigits ds

let numFromBools d x = fromBools d x |> fromDigits d

let intFromBools d x = numberValue <| numFromBools d x

let intToBools (s : #IBases) n1 =
  let bs = getBases s
  let m = List.reduce (*) bs
  [| 
    let mutable q = 1
    for b in bs do
      for i in 0 .. b - 1 ->
        i = (n1 / q) % b
      q <- q * b
  |]

let boolsFromIntPair (s1, s2) (n1, n2) =
  Array.append (intToBools s1 n1) (intToBools s2 n2)

let numPairFromBools (s1: #IBases, s2: #IBases) (bs : bool[]) : 'n1 * 'n2 =
  let m = List.sum <| getBases s1
  numFromBools s1 bs.[0 .. m - 1],
  numFromBools s2 bs.[m .. bs.Length]

let intPairFromBools (s1, s2) bs =
  let a, b = numPairFromBools (s1, s2) bs
  numberValue a, numberValue b

