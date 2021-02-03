module ReversibleArith.NumIso
open Iso
open Iso.Operators
open Num

/// Digit complement
let compl b = BIso(complDigit, complDigit, lazy SFunc (FSucc (b :> IBase).Base))

/// Digit successor
let succ b = BIso(succDigit, predDigit, lazy SFunc (FSucc (b :> IBase).Base))

/// Digit plus constant
let plusConst k b = BIso(addDigit k, subDigit k, lazy SFunc (FAddDigit(k, (b :> IBase).Base)))

/// Decompose a Num into first and rest digits
let num (Bases bs) = BIso(mkNum, unNum, lazy SFunc (FNum bs))

/// Conditionally apply f when c = i
let cond (Digit(a, b) as i) (BIso(f, g, s)) =
  BIso((fun (v, x) -> (v, (if i = v then f x else x))),
       (fun (v, x) -> (v, (if i = v then g x else x))), 
       lazy SPFunc(PFCond(a, b.Base), [s.Value]))

/// Conditionally apply f when c = base - 1
let condLast (b0 : 'b when 'b :> IBase) (BIso(f, g, s)) =
  BIso((fun ((Digit(n, (Base b) : 'b) as v), x) -> (v, (if n + 1 = b then f x else x))),
       (fun ((Digit(n, Base b) as v), x) -> (v, (if n + 1 = b then g x else x))),
       lazy SPFunc(PFCondLast b0.Base, [s.Value]))

/// Repeat f i times
let rep (Base b) (BIso(f, g, s)) =
  let rec rep i f x =
    if i <= 0 then x else rep (i - 1) f (f x)

  BIso((fun ((v : Digit<_>), x) -> (v, rep (numberValue v) f x)),
       (fun (v, x) -> (v, rep (numberValue v) g x)),
       lazy SPFunc(PFRep b, [s.Value]))

/// Repeat f i times, with reversed arguments
let rep' b bi = comm >>> rep b bi >>> comm

[<AutoOpen>]
module Builders =
  type INumFromList =
    abstract member NumFromList : int list -> INum

  type INumFromList<'b when 'b :> INum> =
    inherit INumFromList
    abstract member NumFromList : int list -> 'b

  type SuccBuilder<'b when 'b :> INum> =
    abstract member Succ : BIso<'b, 'b>
    abstract member SuccRest : int -> BIso<'b, 'b>

  type AddBuilder<'b when 'b :> INum> =
    abstract member Add : BIso<'b * 'b, 'b * 'b>

  type ComplBuilder<'b when 'b :> INum> =
    abstract member Compl : BIso<'b, 'b>

  type FoldBuilder<'b when 'b :> INum> =
    abstract member Fold : 's * (IBase -> 's -> 's * BIso<'a, 'a>) -> BIso<'a * 'b, 'a * 'b>

  type PlusConstBuilder<'b when 'b :> INum> =
    abstract member PlusConst : int -> BIso<'b, 'b>

  type ISuccAddBuilder =
    inherit IBases
    inherit INumFromList
    abstract member Succ' : BIso<INum, INum>
    abstract member SuccRest' : int -> BIso<INum, INum>

  type ISuccAddBuilder<'b when 'b :> INum> =
    inherit IFromDigits<'b>
    inherit SuccBuilder<'b>
    inherit AddBuilder<'b>
    inherit ComplBuilder<'b>
    inherit FoldBuilder<'b>
    inherit PlusConstBuilder<'b>
    inherit INumFromList<'b>
    inherit ISuccAddBuilder

  let private basesName (x : #ISuccAddBuilder<_>) =
    x.Bases
    |> Seq.map string
    |> String.concat ","

  [<AutoOpen>]
  module Extensions =
    type ISuccAddBuilder<'b when 'b :> INum> with
      member b.Repeat(i, makeIso) = 
        b.Fold(0, fun _ i -> (i + 1, makeIso i))
        |> group (sprintf "repeat(%A)" <| basesName b)

      member b.Neg =
        (b.Compl >>> b.Succ)
        |> group (sprintf "neg(%s)" <| basesName b)

      /// a, b -> a + k * b, b
      member b.AddMultiple k =
        if k < 0 then
          sym <| b.Fold(-k, fun (Base _b) s -> (s * _b, b.PlusConst(s)))
        else
          b.Fold(k, fun (Base _b) s -> (s * _b, b.PlusConst(s)))
        |> group (sprintf "addMultiple(%d; %s)" k <| basesName b)

      /// a, b -> a + k * b, b
      member b.AddMultiple'(b' : #ISuccAddBuilder<'a>, k) =
        if k < 0 then
          sym <| b.Fold(-k, fun (Base _b) s -> (s * _b, b'.PlusConst(s)))
        else
          b.Fold(k, fun (Base _b) s -> (s * _b, b'.PlusConst(s)))
        |> group (sprintf "addMultiple(%d; %s; %s)" k (basesName b') (basesName b))

      /// (a, (b, c)) -> (a + b*c, (b, c))
      member b.Mult =
        (sym assoc >>> b.Fold(1, fun (Base _b) s -> (s * _b, b.AddMultiple(s))) >>> assoc)
        |> group (sprintf "mult(%s)" <| basesName b)

      /// (a, (b, c)) -> (a + b*c, (b, c))
      member b.Mult'(b' : #ISuccAddBuilder<'c>) =
        (sym assoc >>> b.Fold(1, fun (Base _b) s -> (s * _b, b'.AddMultiple(s))) >>> assoc)
        |> group (sprintf "mult(%s; %s)" (basesName b') <| basesName b)

      /// (a, (b, c)) -> (a + b*c, (b, c))
      member b.Mult''(b' : #ISuccAddBuilder<'c>, b'' : #ISuccAddBuilder<'a>) =
        (sym assoc >>> b.Fold(1, fun (Base _b) s -> (s * _b, b'.AddMultiple'(b'', s))) >>> assoc)
        |> group (sprintf "mult(%s; %s; %s)" (basesName b'') (basesName b') <| basesName b)

  type SuccDigit<'b when 'b :> IBase> = SuccDigit of 'b with
    interface ISuccAddBuilder<Digit<'b>> with
      member d.FromDigits ds = match d with SuccDigit b -> (Digit(0, b) :> IFromDigits<_>).FromDigits ds

      member d.Succ = match d with SuccDigit b -> succ b
      member d.SuccRest n = let d = d :> ISuccAddBuilder<_> in if n <= 0 then d.Succ else id
      member d.Add = match d with SuccDigit b -> rep' b (succ b)
      member d.Compl = match d with SuccDigit b -> compl b
      member d.Fold(s, makeFunc) = 
        let (SuccDigit b), d = d, d :> ISuccAddBuilder<_>
        rep' b (snd <| makeFunc b s)

      member d.PlusConst c =
        match d with SuccDigit ((Base b') as b) -> plusConst (((c % b') + b') % b') b

      member d.NumFromList xs =
        let (SuccDigit b) = d
        let m = b.Base
        match xs with
        | [x] -> Digit(((x % m) + m) % m, b)
        | _ -> failwith "NumFromList: must have length of 1"

    interface ISuccAddBuilder with
      member d.Bases = match d with SuccDigit b -> [b.Base] 
      member d.Succ' = cast >>> (d :> ISuccAddBuilder<_>).Succ >>> cast
      member d.SuccRest' i = cast >>> (d :> ISuccAddBuilder<_>).SuccRest(i) >>> cast

    interface INumFromList with
      member d.NumFromList xs = (d :> ISuccAddBuilder<_>).NumFromList xs :> _

  type SuccNum<'b, 'n when 'b :> IBase and 'n :> INum> = SuccNum of 'b * ISuccAddBuilder<'n> with
    interface ISuccAddBuilder<Num<'b, 'n>> with
      member d.FromDigits ds = 
        let (SuccNum(b, x)) = d
        match ds with
        | [] -> failwith "FromDigits: not enough digits"
        | d0 :: ds' ->
          let d1 = (Digit(0, b) :> IFromDigits<_>).FromDigits [d0]
          Num(d1, (x :> IFromDigits<_>).FromDigits(ds'))

      member s.Succ = 
        let (SuccNum (b, s')) = s
        let num = num (s :> ISuccAddBuilder<_>)
        (sym num >>> condLast b s'.Succ >>> (succ b &&& id) >>> num)
        |> group (sprintf "succ(%s)" <| basesName s)

      member s.SuccRest n =
        let (SuccNum (b, s')) = s
        let s = (s :> ISuccAddBuilder<_>)
        let num = num (s :> ISuccAddBuilder<_>)
        if n <= 0 then
          s.Succ
        else
          (sym num >>> (id &&& s'.SuccRest (n - 1)) >>> num)
          |> group (sprintf "succRest(%d; %s)" n <| basesName s)

      member s.Add = 
        let (SuccNum (b, s')) = s
        let num, num' = num (s :> ISuccAddBuilder<_>), num (s' :> ISuccAddBuilder<_>)
        let succ = (s :> ISuccAddBuilder<_>).Succ
        let splitDigits = assoc >>> (id &&& (sym assoc >>> (comm &&& id) >>> assoc)) >>> sym assoc
        let joinA = (id &&& (sym assoc >>> (num' &&& id))) >>> sym assoc
        let addB = ((rep b succ >>> comm) &&& id)
        let join = assoc >>> joinA >>> addB >>> assoc
        ((sym num &&& sym num) >>> splitDigits >>> (comm &&& s'.Add) >>> join >>> (id &&& num))
        |> group (sprintf "add(%s)" <| basesName s)

      member s.Fold (state, makeIso) =
        let (SuccNum (b, s')) = s
        let s = s :> ISuccAddBuilder<_>
        let state', iso = makeIso b state
        let num, repeat' = num s, s'.Fold(state', makeIso)
        let unpack = (id &&& sym num) >>> sym assoc
        let rep1 = ((rep' b iso >>> comm) &&& id) >>> assoc
        let repack = sym assoc >>> (comm &&& id) >>> assoc >>> (id &&& num)
        (unpack >>> rep1 >>> (id &&& repeat') >>> repack)
        |> group (sprintf "fold(%A; %s)" state <| basesName s)

      member s.Compl =
        let (SuccNum (b, s')) = s
        let num = num (s :> ISuccAddBuilder<_>)
        (sym num >>> (compl b &&& s'.Compl) >>> num)
        |> group (sprintf "compl(%s)" <| basesName s)

      member s.PlusConst c =
        let (SuccNum ((Base b' as b), s')) = s
        let s = s :> ISuccAddBuilder<_>
        if c < 0 then
          sym (s.PlusConst(-c))
        else
          let d, q = ((c % b') + b') % b', c / b'
          let num, succ = num s, s.Succ
          (repConst d succ >>> sym num >>> (id &&& s'.PlusConst q) >>> num)
          |> group (sprintf "plusConst(%d; %s)" c <| basesName s)

      member s.NumFromList xs =
        let (SuccNum (b, s')) = s
        match xs with
        | [] -> failwith "NumFromList: must be nonempty"
        | x :: xs -> 
          let m = b.Base
          Num(Digit(((x % m) + m) % m, b),
              s'.NumFromList xs)

    interface ISuccAddBuilder with

      member s.Bases = 
        let (SuccNum (b, s')) = s
        [b.Base] @ s'.Bases

      member s.Succ' = cast >>> (s :> ISuccAddBuilder<_>).Succ >>> cast
      member s.SuccRest' i = cast >>> (s :> ISuccAddBuilder<_>).SuccRest(i) >>> cast

    interface INumFromList with
      member d.NumFromList xs = (d :> ISuccAddBuilder<_>).NumFromList xs :> _


  let succDigit (b : 't when 't :> IBase) = 
    let sd = SuccDigit b
    Widths.add typeof<Digit<'t>> (getBase b)
    sd

  let succNum (b : 'b when 'b :> IBase) (n : ISuccAddBuilder<'n>) = 
    let sn = SuccNum(b, n)
    Widths.add typeof<Digit<'b>> (getBase b)
    Widths.add (typeof<Num<'b, 'n>>) (getBases sn |> List.sum)
    sn

  open System.Reflection
  let private succNumCtor tb tn = 
    let td = typedefof<SuccNum<B10, Digit<B2>>>.MakeGenericType(tb, tn)
    fun a b -> 
      td.InvokeMember(
        "NewSuccNum", BindingFlags.Public ||| BindingFlags.Static ||| BindingFlags.InvokeMethod, 
        null, null, [| a; b |])

  let rec succFromList xs : ISuccAddBuilder =
    match xs with
    | [] -> failwith "succFromList: empty"
    | [x] -> SuccDigit(mkBase x) :> _
    | x :: xs -> 
      let res = succFromList xs
      let args = res.GetType().GetInterface(typedefof<ISuccAddBuilder<INum>>.Name).GetGenericArguments()
      let b = mkBase x
      let ctor = succNumCtor (b.GetType()) args.[0]
      downcast (ctor b res)

let add b = rep' b (succ b) |> group (sprintf "add(%d)" b.Base)
let mult b = rep' b (add b) |> group (sprintf "mult(%d)" b.Base)

