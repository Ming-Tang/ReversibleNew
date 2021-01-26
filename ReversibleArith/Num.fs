module ReversibleArith.Num

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

let inline modValue x = (x :> INum).Mod
let inline numberValue (x : #INum) = x.NumberValue
let inline baseValue (x : #INum) = x.Base

type IBase =
  abstract member Base : int

type MkBase = MkBase of int with
  interface IBase with
    member x.Base = match x with MkBase i -> i
  
let mkBase x = MkBase x

type B2 = B2 with
  interface IBase with member b.Base = 2

type B3 = B3 with
  interface IBase with member b.Base = 3

type B5 = B5 with
  interface IBase with member b.Base = 5

type B6 = B6 with
  interface IBase with member b.Base = 6

type B8 = B8 with
  interface IBase with member b.Base = 8

type B10 = B10 with
  interface IBase with member b.Base = 10

let inline getBase (x : #IBase) =
  (x :> IBase).Base

let inline (|Base|) x = getBase x

type Digit<'b when 'b :> IBase> = Digit of digit : int * _base : 'b with
  member inline d.DecomposeDigit() =
    match d with Digit(d, b) -> d, b

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

let complDigit (Digit(d, (Base b as b'))) = Digit((b - d - 1) % b, b')

let inline checkedPM a b c = Checked.(+) a (Checked.(*) b c)

type Num<'b, 'n when 'b :> IBase and 'n :> INum> = Num of Digit<'b> * 'n with
  member inline d.DecomposeNum() =
    match d with Num(d, b) -> d, b

  interface INum with
    member n.Bases =
      match n with
      | Num(d, Bases ns) -> [baseValue d] @ ns

    member n.Digits =
      match n with
      | Num(d, ds) -> [baseValue d] @ (ds :> INum).Digits

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

