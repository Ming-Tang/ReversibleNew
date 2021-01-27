module ReversibleArith.NumIso
open Iso
open Num

/// Digit complement
let compl b = BIso(complDigit, complDigit, lazy SFunc (FSucc (b :> IBase).Base))

/// Digit successor
let succ b = BIso(succDigit, predDigit, lazy SFunc (FSucc (b :> IBase).Base))

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
let rep' b bi = (comm >>> rep b bi >>> comm)

[<AutoOpen>]
module Builders =
  type SuccBuilder<'b when 'b :> INum> =
    abstract member Succ : BIso<'b, 'b>
    abstract member SuccRest : int -> BIso<'b, 'b>

  type AddBuilder<'b when 'b :> INum> =
    abstract member Add : BIso<'b * 'b, 'b * 'b>

  type ComplBuilder<'b when 'b :> INum> =
    abstract member Compl : BIso<'b, 'b>

  type FoldBuilder<'b when 'b :> INum> =
    abstract member Fold : 's * ('s -> 's * BIso<'a, 'a>) -> BIso<'a * 'b, 'a * 'b>

  type ISuccAddBuilder<'b when 'b :> INum> =
    inherit SuccBuilder<'b>
    inherit AddBuilder<'b>
    inherit ComplBuilder<'b>
    inherit FoldBuilder<'b>
    inherit IBases

  let private basesName (x : #ISuccAddBuilder<_>) =
    x.Bases
    |> Seq.map string
    |> String.concat ","

  [<AutoOpen>]
  module Extensions =
    type ISuccAddBuilder<'b when 'b :> INum> with
      member b.Repeat(i, makeIso) = 
        b.Fold(0, fun i -> (i + 1, makeIso i))
        |> group (sprintf "repeat(%A)" <| basesName b)

      member b.Neg =
        (b.Compl >>> b.Succ)
        |> group (sprintf "neg(%s)" <| basesName b)
    

  type SuccDigit<'b when 'b :> IBase> = SuccDigit of 'b with
    interface ISuccAddBuilder<Digit<'b>> with
      member d.Succ = match d with SuccDigit b -> succ b
      member d.SuccRest n = let d = d :> ISuccAddBuilder<_> in if n <= 0 then d.Succ else id
      member d.Add = match d with SuccDigit b -> rep' b (succ b)
      member d.Compl = match d with SuccDigit b -> compl b
      member d.Fold(s, makeFunc) = 
        let (SuccDigit b), d = d, d :> ISuccAddBuilder<_>
        rep' b (snd <| makeFunc s)

      member d.Bases = match d with SuccDigit b -> [b.Base] 
    
  type SuccNum<'b, 'n when 'b :> IBase and 'n :> INum> = SuccNum of 'b * ISuccAddBuilder<'n> with
    interface ISuccAddBuilder<Num<'b, 'n>> with
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
          |> group (sprintf "succRest(%d, %s)" n <| basesName s)

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
        let s = (s :> ISuccAddBuilder<_>)
        let state', iso = makeIso state
        let num, repeat' = num s, s'.Fold(state', makeIso)
        let unpack = (id &&& sym num) >>> sym assoc
        let rep1 = ((rep' b iso >>> comm) &&& id) >>> assoc
        let repack = sym assoc >>> (comm &&& id) >>> assoc >>> (id &&& num)
        (unpack >>> rep1 >>> (id &&& repeat') >>> repack)
        |> group (sprintf "fold(%A, %s)" state <| basesName s)

      member s.Compl =
        let (SuccNum (b, s')) = s
        let num = num (s :> ISuccAddBuilder<_>)
        (sym num >>> (compl b &&& s'.Compl) >>> num)
        |> group (sprintf "compl(%s)" <| basesName s)

      member s.Bases = 
        let (SuccNum (b, s')) = s
        [b.Base] @ s'.Bases

  let succDigit (b : 't when 't :> IBase) = 
    let sd = SuccDigit b
    Widths.add typeof<Digit<'t>> (getBase b)
    sd

  let succNum (b : 'b when 'b :> IBase) (n : ISuccAddBuilder<'n>) = 
    let sn = SuccNum(b, n)
    Widths.add typeof<Digit<'b>> (getBase b)
    Widths.add (typeof<Num<'b, 'n>>) (getBases sn |> List.sum)
    sn

  type Builder() =
    static member inline Build< ^b when ^b :> IBase>(d : Digit< ^b>) : SuccDigit< ^b> =
      SuccDigit (snd <| d.DecomposeDigit())

    static member inline Build< ^t, ^n, ^b, ^r 
        when ^b :> IBase and ^n :> INum and ^t : (static member Build : ^n -> ^r) and ^r :> ISuccAddBuilder< ^n>
      >(n : Num< ^b, ^n>) =
      let d, rest = n.DecomposeNum()
      let res = (( ^t) : (static member Build : ^n -> ^r ) rest)
      SuccNum(snd (d.DecomposeDigit()), res)

  let inline build'< ^t, ^d, ^r when ^t : (static member Build : ^d -> ^r)> (d : ^d) : ^r =
    ( ^t : (static member Build : ^d -> ^r) d)

  //let test1 = build'<Builder, _, _> (Digit(3, B10))
  //let test2 = build'<Builder, _, _> (Num(Digit(5, B10), Digit(3, B10)))
  // build'<Builder, _, _> (succNum B10 (succNum B2 (succDigit B10)))

  let rec fromList xs : ISuccAddBuilder<INum> =
    match xs with
    | [] -> failwith "succFromList: empty"
    | [x] -> SuccDigit(mkBase x) |> box |> unbox
    | x :: xs -> SuccNum(mkBase x, fromList xs) |> box |> unbox

let add b = rep' b (succ b) |> group (sprintf "add(%d)" b.Base)
let mult b = rep' b (add b) |> group (sprintf "mult(%d)" b.Base)

