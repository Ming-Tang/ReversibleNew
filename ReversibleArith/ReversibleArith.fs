module ReversibleArith
open Iso

type IBases =
  abstract member Bases : int list

let inline getBases (x : #IBases) = x.Bases
let inline (|Bases|) (x : #IBases) = getBases x

type INum =
  abstract member NumberValue : int
  abstract member Base : int
  inherit IBases

let inline numberValue (x : #INum) = x.NumberValue
let inline baseValue (x : #INum) = x.Base

type IBase =
  abstract member Base : int

let mkBase x = { new IBase with member b.Base = x }

type B2 = B2 with
  interface IBase with member b.Base = 2

type B10 = B10 with
  interface IBase with member b.Base = 10

let inline getBase (x : #IBase) =
  (x :> IBase).Base

let inline (|Base|) x = getBase x

type Digit<'b when 'b :> IBase> = Digit of digit : int * _base : 'b with
  interface INum with
    member d.NumberValue =
      match d with Digit(d, _) -> d

    member d.Base =
      match d with Digit(_, b) -> getBase b

    member d.Bases =
      match d with Digit(d, _) -> [d]

let succDigit (Digit(d, (Base b as b'))) = Digit((d + 1) % b, b')
let predDigit (Digit(d, (Base b as b'))) = Digit((d + b - 1) % b, b')

type Num<'b, 'n when 'b :> IBase and 'n :> INum> = Num of Digit<'b> * 'n with
  interface INum with
    member n.Bases =
      match n with
      | Num(d, Bases ns) -> [(d :> INum).Base] @ ns

    member n.NumberValue =
      match n with 
      | Num(x, y) -> (numberValue x) + (x :> INum).Base * (numberValue y)

    member n.Base =
      match n with Num(x, y) -> (x :> INum).Base * y.Base

let succ b = BIso(succDigit, predDigit, SFunc (FSucc (b :> IBase).Base))
let unNum (Num(a, b)) = a, b
let mkNum (a, b) = Num(a, b)

let num (Bases bs) = BIso(mkNum, unNum, SFunc (FNum bs))

let cond (Digit(a, b) as i) (BIso(f, g, s)) =
  BIso((fun (v, x) -> (v, (if i = v then f x else x))),
       (fun (v, x) -> (v, (if i = v then g x else x))), SPFunc(PFCond(a, b.Base), [s]))

let condLast (b0 : 'b when 'b :> IBase) (BIso(f, g, s)) =
  BIso((fun ((Digit(n, (Base b) : 'b) as v), x) -> (v, (if n + 1 = b then f x else x))),
       (fun ((Digit(n, Base b) as v), x) -> (v, (if n + 1 = b then g x else x))),
       SPFunc(PFCondLast b0.Base, [s]))

let rep (Base b) (BIso(f, g, s)) =
  let rec rep i f x =
    if i <= 0 then x else rep (i - 1) f (f x)
  BIso((fun ((v : Digit<_>), x) -> (v, rep (numberValue v) f x)),
       (fun (v, x) -> (v, rep (numberValue v) g x)),
       SPFunc(PFRep b, [s]))

let rep' b bi = (comm >>> rep b bi >>> comm)

[<AutoOpen>]
module Builders =
  type SuccBuilder<'b when 'b :> INum> =
    abstract member Succ : BIso<'b, 'b>

  type AddBuilder<'b when 'b :> INum> =
    abstract member Add : BIso<'b * 'b, 'b * 'b>

  type SuccAddBuilder<'b when 'b :> INum> =
    inherit SuccBuilder<'b>
    inherit AddBuilder<'b>
    inherit IBases
    
  let private basesName (x : #SuccAddBuilder<_>) =
    x.Bases
    |> Seq.map string
    |> String.concat ","

  type SuccDigit<'b when 'b :> IBase> = private SuccDigit of 'b with
    interface SuccAddBuilder<Digit<'b>> with
      member d.Succ = match d with SuccDigit b -> succ b
      member d.Add = match d with SuccDigit b -> rep' b (succ b)
      member d.Bases = match d with SuccDigit b -> [b.Base] 
    
  type SuccNum<'b, 'n when 'b :> IBase and 'n :> INum> = private SuccNum of 'b * SuccAddBuilder<'n> with
    interface SuccAddBuilder<Num<'b, 'n>> with
      member s.Succ = 
        let (SuccNum (b, s')) = s
        let num = num (s :> SuccAddBuilder<_>)
        sym num >>> condLast b s'.Succ >>> (succ b &&& id) >>> num
        |> group (sprintf "succ(%s)" <| basesName s)

      member s.Add = 
        let (SuccNum (b, s')) = s
        let num, num' = num (s :> SuccAddBuilder<_>), num (s' :> SuccAddBuilder<_>)
        let succ = (s :> SuccAddBuilder<_>).Succ
        let splitDigits = assoc >>> (id &&& (sym assoc >>> (comm &&& id) >>> assoc)) >>> sym assoc
        let joinA = (id &&& (sym assoc >>> (num' &&& id))) >>> sym assoc
        let addB = ((rep b succ >>> comm) &&& id)
        let join = assoc >>> joinA >>> addB >>> assoc
        ((sym num &&& sym num) >>> splitDigits >>> (comm &&& s'.Add) >>> join >>> (id &&& num))
        |> group (sprintf "add(%s)" <| basesName s)

      member s.Bases = 
        let (SuccNum (b, s')) = s
        [b.Base] @ s'.Bases

  let succDigit (b : 't when 't :> IBase) = 
    let sd = SuccDigit b
    Widths.add typeof<Digit<'t>> (getBase b)
    sd

  let succNum (b : 'b when 'b :> IBase) (n : SuccAddBuilder<'n>) = 
    let sn = SuccNum(b, n)
    Widths.add typeof<Digit<'b>> (getBase b)
    Widths.add (typeof<Num<'b, 'n>>) (getBases sn |> List.sum)
    sn

let add b = rep' b (succ b) |> group (sprintf "add(%d)" b.Base)
let mult b = rep' b (add b) |> group (sprintf "mult(%d)" b.Base)

[<EntryPoint>]
let main argv =
  let s = succNum B10 (succNum B10 (succNum B10 (succDigit B10)))
  let sn = (s :> SuccBuilder<_>).Succ
  let addn = (s :> AddBuilder<_>).Add
  printfn "%A" <| numberValue (Num(Digit(2, B10), Num(Digit(3, B10), Digit(4, B10))))
  printfn "%A" <| (add B10 <<| (Digit(7, B10), Digit(6, B10)))
  printfn "%A" <| (mult B10 <<| ((Digit(2, B10), Digit(3, B10)), Digit(4, B10)))

  let d5499 = Num(Digit(9, B10), Num(Digit(9, B10), Num(Digit(4, B10), Digit(5, B10))))
  let d1237 = Num(Digit(7, B10), Num(Digit(3, B10), Num(Digit(2, B10), Digit(1, B10))))
  printfn "%A" <| (sn <<| d5499)
  printfn "%A" <| (addn <<| (d5499, d1237))
  printfn "%A" <| (addn <<| (d1237, d5499))

  printfn ""
  printfn ""
  printfn "%s" (showBIso None sn)
  printfn "\\\\"
  printfn "%s" (showBIso None addn)

  // printfn ""
  // printfn ""
  // printfn "%s" (showBIso' sn)
  // printfn "%s" (showBIso' addn)
  0 // return an integer exit code

