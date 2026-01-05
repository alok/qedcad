import Std

open Std

namespace CadLean

-- Basic helpers for Rat

def ratAbs (r : Rat) : Rat :=
  if r < 0 then -r else r


def ratOfNat (n : Nat) : Rat :=
  Rat.ofInt (Int.ofNat n)


def ratPow (r : Rat) (n : Nat) : Rat :=
  r ^ n


def arraySet {α : Type} (xs : Array α) (i : Nat) (v : α) : Array α :=
  if h : i < xs.size then xs.set i v h else xs


def listInsert {α : Type} (cmp : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if cmp x y then x :: y :: ys else y :: listInsert cmp x ys


def listSort {α : Type} (cmp : α → α → Bool) (xs : List α) : List α :=
  xs.foldl (fun acc x => listInsert cmp x acc) []


def listGetD {α : Type} (xs : List α) (i : Nat) (default : α) : α :=
  match xs, i with
  | [], _ => default
  | x :: _, 0 => x
  | _ :: xs, i + 1 => listGetD xs i default


def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)


-- Univariate polynomials over Rat (coeffs low -> high)
structure URatPoly where
  coeffs : Array Rat
  deriving Repr

instance : Inhabited URatPoly where
  default := { coeffs := #[] }

namespace URatPoly


def zero : URatPoly :=
  { coeffs := #[] }


def const (c : Rat) : URatPoly :=
  if c = 0 then zero else { coeffs := #[c] }


def monomial (k : Nat) (c : Rat) : URatPoly :=
  if c = 0 then zero
  else
    Id.run do
      let mut coeffs := Array.replicate (k + 1) (0 : Rat)
      coeffs := arraySet coeffs k c
      return { coeffs := coeffs }


def trim (p : URatPoly) : URatPoly :=
  Id.run do
    let mut n := p.coeffs.size
    while n > 0 && p.coeffs[n - 1]! = 0 do
      n := n - 1
    return { coeffs := p.coeffs.extract 0 n }


def isZero (p : URatPoly) : Bool :=
  p.coeffs.size == 0


def degree (p : URatPoly) : Nat :=
  if isZero p then 0 else p.coeffs.size - 1


def leadingCoeff (p : URatPoly) : Rat :=
  if isZero p then 0 else p.coeffs[p.coeffs.size - 1]!


def add (p q : URatPoly) : URatPoly :=
  let n := max p.coeffs.size q.coeffs.size
  Id.run do
    let mut res := Array.replicate n (0 : Rat)
    for i in [:n] do
      let a := if i < p.coeffs.size then p.coeffs[i]! else 0
      let b := if i < q.coeffs.size then q.coeffs[i]! else 0
      res := arraySet res i (a + b)
    return trim { coeffs := res }


def neg (p : URatPoly) : URatPoly :=
  { coeffs := p.coeffs.map (fun c => -c) }


def sub (p q : URatPoly) : URatPoly :=
  add p (neg q)


def scale (p : URatPoly) (c : Rat) : URatPoly :=
  if c = 0 then zero else { coeffs := p.coeffs.map (fun x => c * x) } |> trim


def mul (p q : URatPoly) : URatPoly :=
  if isZero p || isZero q then
    zero
  else
    let n := p.coeffs.size + q.coeffs.size - 1
    Id.run do
      let mut res := Array.replicate n (0 : Rat)
      for i in [:p.coeffs.size] do
        for j in [:q.coeffs.size] do
          let curr := res[i + j]!
          res := arraySet res (i + j) (curr + p.coeffs[i]! * q.coeffs[j]!)
      return trim { coeffs := res }


def pow (p : URatPoly) (n : Nat) : URatPoly :=
  match n with
  | 0 => const 1
  | n + 1 => mul (pow p n) p


def derivative (p : URatPoly) : URatPoly :=
  if p.coeffs.size <= 1 then
    zero
  else
    Id.run do
      let mut res := Array.replicate (p.coeffs.size - 1) (0 : Rat)
      for i in [1:p.coeffs.size] do
        let coeff := p.coeffs[i]!
        res := arraySet res (i - 1) (coeff * ratOfNat i)
      return trim { coeffs := res }


def eval (p : URatPoly) (x : Rat) : Rat :=
  Id.run do
    let mut acc : Rat := 0
    for c in p.coeffs.reverse do
      acc := acc * x + c
    return acc


def divRem (p q : URatPoly) : URatPoly × URatPoly :=
  if isZero q then
    (zero, p)
  else
    let qdeg := degree q
    let qlc := leadingCoeff q
    Id.run do
      let mut r := p
      let mut qout := zero
      while !isZero r && degree r >= qdeg do
        let rdeg := degree r
        let rlc := leadingCoeff r
        let shift := rdeg - qdeg
        let coeff := rlc / qlc
        let mut termCoeffs := Array.replicate (shift + 1) (0 : Rat)
        termCoeffs := arraySet termCoeffs shift coeff
        let term : URatPoly := { coeffs := termCoeffs }
        qout := add qout term
        r := sub r (mul term q)
      return (trim qout, trim r)


def sturmSequence (p : URatPoly) : List URatPoly :=
  if isZero p then
    []
  else
    Id.run do
      let mut seq : List URatPoly := [p, derivative p]
      let mut done := false
      while !done do
        match seq with
        | [] | [_] =>
            done := true
        | _ =>
            let a := listGetD seq (seq.length - 2) zero
            let b := listGetD seq (seq.length - 1) zero
            if isZero b then
              done := true
            else
              let (_, r) := divRem a b
              if isZero r then
                done := true
              else
                seq := seq.concat (neg r)
      return seq


def signAt (p : URatPoly) (x : Rat) : Int :=
  let v := eval p x
  if v > 0 then 1 else if v < 0 then -1 else 0


def signVariations (signs : List Int) : Int :=
  let filtered := signs.filter (fun s => s != 0)
  let rec loop (lst : List Int) (prev : Int) (count : Int) : Int :=
    match lst with
    | [] => count
    | s :: rest =>
        let count' := if prev != 0 && s != 0 && prev * s < 0 then count + 1 else count
        loop rest s count'
  match filtered with
  | [] => 0
  | s :: rest => loop rest s 0


def rootCount (p : URatPoly) (a b : Rat) : Int :=
  let seq := sturmSequence p
  let va := signVariations (seq.map (fun q => signAt q a))
  let vb := signVariations (seq.map (fun q => signAt q b))
  va - vb


def rootBound (p : URatPoly) : Rat :=
  if isZero p then
    0
  else
    Id.run do
      let n := degree p
      let an := leadingCoeff p
      let mut m : Rat := 0
      for i in [:n] do
        let ai := p.coeffs[i]!
        let v := ratAbs (ai / an)
        if v > m then
          m := v
      return 1 + m


def isolateAux (p : URatPoly) (a b : Rat) : Nat → List (Rat × Rat)
  | 0 =>
      let c := rootCount p a b
      if c == 0 then [] else [(a, b)]
  | depth + 1 =>
      let c := rootCount p a b
      if c == 0 then
        []
      else
        let m := (a + b) / 2
        isolateAux p a m depth ++ isolateAux p m b depth


def isolate (p : URatPoly) (a b : Rat) (depth : Nat) : List (Rat × Rat) :=
  isolateAux p a b depth


def realRootsIsolate (p : URatPoly) (depth : Nat := 60) : List (Rat × Rat) :=
  if isZero p || degree p == 0 then
    []
  else
    let bound := rootBound p
    isolate p (-bound) bound depth


def shift (p : URatPoly) (a : Rat) : URatPoly :=
  -- p(x - a)
  let d := degree p
  Id.run do
    let mut res := zero
    for i in [:d+1] do
      let coeff := p.coeffs[i]!
      if coeff != 0 then
        for k in [:i+1] do
          let bin := ratOfNat (binom i k)
          let term := coeff * bin * ratPow (-a) (i - k)
          let curr := if k < res.coeffs.size then res.coeffs[k]! else 0
          let mut coeffs := if res.coeffs.size > k then res.coeffs else Array.replicate (k + 1) (0 : Rat)
          coeffs := arraySet coeffs k (curr + term)
          res := trim { coeffs := coeffs }
    return res


def scaleVar (p : URatPoly) (c : Rat) : URatPoly :=
  -- c^deg * p(x / c)
  if c = 0 then
    if degree p == 0 then const (p.coeffs[0]!) else zero
  else
    let d := degree p
    Id.run do
      let mut coeffs := Array.replicate (d + 1) (0 : Rat)
      for i in [:d+1] do
        let coeff := p.coeffs[i]!
        let factor := ratPow c (d - i)
        coeffs := arraySet coeffs i (coeff * factor)
      return trim { coeffs := coeffs }

end URatPoly


-- Polynomials in x with coefficients in URatPoly (for resultants)
structure UAlgPoly where
  coeffs : Array URatPoly

namespace UAlgPoly


def zero : UAlgPoly := { coeffs := #[] }


def trim (p : UAlgPoly) : UAlgPoly :=
  Id.run do
    let mut n := p.coeffs.size
    while n > 0 && URatPoly.isZero (p.coeffs[n - 1]!) do
      n := n - 1
    return { coeffs := p.coeffs.extract 0 n }


def isZero (p : UAlgPoly) : Bool :=
  p.coeffs.size == 0


def degree (p : UAlgPoly) : Nat :=
  if isZero p then 0 else p.coeffs.size - 1


def leadingCoeff (p : UAlgPoly) : URatPoly :=
  if isZero p then URatPoly.zero else p.coeffs[p.coeffs.size - 1]!


def add (p q : UAlgPoly) : UAlgPoly :=
  let n := max p.coeffs.size q.coeffs.size
  Id.run do
    let mut res := Array.replicate n URatPoly.zero
    for i in [:n] do
      let a := if i < p.coeffs.size then p.coeffs[i]! else URatPoly.zero
      let b := if i < q.coeffs.size then q.coeffs[i]! else URatPoly.zero
      res := arraySet res i (URatPoly.add a b)
    return trim { coeffs := res }


def neg (p : UAlgPoly) : UAlgPoly :=
  { coeffs := p.coeffs.map URatPoly.neg }


def sub (p q : UAlgPoly) : UAlgPoly :=
  add p (neg q)


def scale (p : UAlgPoly) (c : URatPoly) : UAlgPoly :=
  if URatPoly.isZero c then zero else { coeffs := p.coeffs.map (fun x => URatPoly.mul c x) } |> trim


def mul (p q : UAlgPoly) : UAlgPoly :=
  if isZero p || isZero q then
    zero
  else
    let n := p.coeffs.size + q.coeffs.size - 1
    Id.run do
      let mut res := Array.replicate n URatPoly.zero
      for i in [:p.coeffs.size] do
        for j in [:q.coeffs.size] do
          let curr := res[i + j]!
          res := arraySet res (i + j) (URatPoly.add curr (URatPoly.mul p.coeffs[i]! q.coeffs[j]!))
      return trim { coeffs := res }


def ofRatPoly (p : URatPoly) : UAlgPoly :=
  { coeffs := p.coeffs.map (fun c => URatPoly.const c) } |> trim

end UAlgPoly


partial def detURatPoly (m : Array (Array URatPoly)) : URatPoly :=
  let n := m.size
  if n == 0 then
    URatPoly.const 1
  else if n == 1 then
    (m[0]!)[0]!
  else
    Id.run do
      let mut acc := URatPoly.zero
      for j in [:n] do
        let sign := if (j % 2) == 0 then (1 : Rat) else (-1 : Rat)
        let mut rows := Array.mkEmpty (n - 1)
        for i in [:n] do
          if i != 0 then
            let mut r := Array.mkEmpty (n - 1)
            for k in [:n] do
              if k != j then
                r := r.push ((m[i]!)[k]!)
            rows := rows.push r
        let cofactor := detURatPoly rows
        let term := URatPoly.mul (URatPoly.scale (m[0]!)[j]! sign) cofactor
        acc := URatPoly.add acc term
      return acc


def sylvesterMatrixAlg (f g : UAlgPoly) : Array (Array URatPoly) :=
  let mf := UAlgPoly.degree f
  let mg := UAlgPoly.degree g
  let fCoeffs := f.coeffs.reverse
  let gCoeffs := g.coeffs.reverse
  let n := mf + mg
  Id.run do
    let mut rows : Array (Array URatPoly) := Array.mkEmpty n
    for i in [:mg] do
      let mut row := Array.replicate n URatPoly.zero
      for j in [:mf+1] do
        row := arraySet row (i + j) (fCoeffs[j]!)
      rows := rows.push row
    for i in [:mf] do
      let mut row := Array.replicate n URatPoly.zero
      for j in [:mg+1] do
        row := arraySet row (i + j) (gCoeffs[j]!)
      rows := rows.push row
    return rows


def resultantAlg (f g : UAlgPoly) : URatPoly :=
  let mat := sylvesterMatrixAlg f g
  detURatPoly mat


def polyZMinusX (q : URatPoly) : UAlgPoly :=
  -- q(z - x) as polynomial in x with coeffs in z
  let n := URatPoly.degree q
  Id.run do
    let mut coeffs := Array.replicate (n + 1) URatPoly.zero
    for i in [:n+1] do
      let qi := q.coeffs[i]!
      if qi != 0 then
        for k in [:i+1] do
          let bin := ratOfNat (binom i k)
          let coeff := qi * bin * ratPow (-1 : Rat) k
          let zpow := URatPoly.monomial (i - k) 1
          let term := URatPoly.scale zpow coeff
          let curr := coeffs[k]!
          coeffs := arraySet coeffs k (URatPoly.add curr term)
    return UAlgPoly.trim { coeffs := coeffs }


def polyZXOverX (q : URatPoly) : UAlgPoly :=
  -- x^{deg} * q(z/x)
  let n := URatPoly.degree q
  Id.run do
    let mut coeffs := Array.replicate (n + 1) URatPoly.zero
    for i in [:n+1] do
      let qi := q.coeffs[i]!
      if qi != 0 then
        let zpow := URatPoly.monomial i qi
        let idx := n - i
        let curr := coeffs[idx]!
        coeffs := arraySet coeffs idx (URatPoly.add curr zpow)
    return UAlgPoly.trim { coeffs := coeffs }


-- Algebraic real numbers (roots of URatPoly with isolating interval)
inductive AReal where
  | rat (r : Rat)
  | alg (poly : URatPoly) (lo hi : Rat)
  deriving Repr

namespace AReal


def interval : AReal → (Rat × Rat)
  | rat r => (r, r)
  | alg _ lo hi => (lo, hi)


def approx : AReal → Rat
  | rat r => r
  | alg _ lo hi => (lo + hi) / 2


def fromRat (r : Rat) : AReal :=
  rat r


def sign (x : AReal) (iters : Nat := 40) : Int :=
  match x with
  | rat r => if r > 0 then 1 else if r < 0 then -1 else 0
  | alg p lo hi =>
      let rec refine (lo hi : Rat) : Nat → Int
        | 0 =>
            if lo > 0 then 1 else if hi < 0 then -1 else 0
        | n + 1 =>
            if lo > 0 then 1
            else if hi < 0 then -1
            else if lo <= 0 && 0 <= hi && URatPoly.eval p 0 = 0 then 0
            else
              let m := (lo + hi) / 2
              let c := URatPoly.rootCount p lo m
              if c == 1 then
                refine lo m n
              else
                refine m hi n
      refine lo hi iters


def add (a b : AReal) : AReal :=
  match a, b with
  | rat r1, rat r2 => rat (r1 + r2)
  | rat r, alg p lo hi =>
      let p' := URatPoly.shift p r
      alg p' (lo + r) (hi + r)
  | alg p lo hi, rat r =>
      let p' := URatPoly.shift p r
      alg p' (lo + r) (hi + r)
  | alg p lo1 hi1, alg q lo2 hi2 =>
      let f := UAlgPoly.ofRatPoly p
      let g := polyZMinusX q
      let r := resultantAlg f g
      let lo := lo1 + lo2
      let hi := hi1 + hi2
      let target := approx a + approx b
      let intervals := URatPoly.isolate r lo hi 60
      let pick :=
        intervals.find? (fun iv =>
          let (a,b) := iv
          a <= target && target <= b
        )
      match pick with
      | some (l,h) => alg r l h
      | none =>
          match intervals with
          | [] => rat target
          | iv :: _ => alg r iv.1 iv.2


def neg (a : AReal) : AReal :=
  match a with
  | rat r => rat (-r)
  | alg p lo hi =>
      let p' := URatPoly.scaleVar p (-1)
      alg p' (-hi) (-lo)


def sub (a b : AReal) : AReal :=
  add a (neg b)


def mul (a b : AReal) : AReal :=
  match a, b with
  | rat r1, rat r2 => rat (r1 * r2)
  | rat r, alg p lo hi =>
      if r = 0 then rat 0
      else
        let p' := URatPoly.scaleVar p r
        let lo' := lo * r
        let hi' := hi * r
        if lo' <= hi' then alg p' lo' hi' else alg p' hi' lo'
  | alg p lo hi, rat r =>
      if r = 0 then rat 0
      else
        let p' := URatPoly.scaleVar p r
        let lo' := lo * r
        let hi' := hi * r
        if lo' <= hi' then alg p' lo' hi' else alg p' hi' lo'
  | alg p lo1 hi1, alg q lo2 hi2 =>
      let f := UAlgPoly.ofRatPoly p
      let g := polyZXOverX q
      let r := resultantAlg f g
      let candidates := [lo1*lo2, lo1*hi2, hi1*lo2, hi1*hi2]
      let lo := candidates.foldl (fun a b => if b < a then b else a) candidates.head!
      let hi := candidates.foldl (fun a b => if b > a then b else a) candidates.head!
      let target := approx a * approx b
      let intervals := URatPoly.isolate r lo hi 60
      let pick :=
        intervals.find? (fun iv =>
          let (a,b) := iv
          a <= target && target <= b
        )
      match pick with
      | some (l,h) => alg r l h
      | none =>
          match intervals with
          | [] => rat target
          | iv :: _ => alg r iv.1 iv.2


def pow (a : AReal) (n : Nat) : AReal :=
  match n with
  | 0 => rat 1
  | n + 1 => mul (pow a n) a

end AReal


-- Multivariate polynomials with rational coefficients
structure Poly where
  nvars : Nat
  terms : Std.HashMap (Array Nat) Rat

instance : Inhabited Poly where
  default := { nvars := 0, terms := {} }

namespace Poly


def zero (n : Nat) : Poly :=
  { nvars := n, terms := {} }


def const (n : Nat) (c : Rat) : Poly :=
  if c = 0 then
    zero n
  else
    let exps := Array.replicate n 0
    let m : Std.HashMap (Array Nat) Rat := {}
    { nvars := n, terms := m.insert exps c }


def one (n : Nat) : Poly :=
  const n 1


def var (n : Nat) (i : Nat) : Poly :=
  let exps := arraySet (Array.replicate n 0) i 1
  let m : Std.HashMap (Array Nat) Rat := {}
  { nvars := n, terms := m.insert exps 1 }


def isZero (p : Poly) : Bool :=
  p.terms.isEmpty


def expsAllZero (exps : Array Nat) : Bool :=
  Id.run do
    let mut ok := true
    for e in exps do
      if e != 0 then
        ok := false
    return ok


def isConst (p : Poly) : Bool :=
  p.terms.toList.all (fun kv => expsAllZero kv.fst)


def addTerm (p : Poly) (exps : Array Nat) (coeff : Rat) : Poly :=
  if coeff = 0 then
    p
  else
    match p.terms.get? exps with
    | some old =>
        let new := old + coeff
        if new = 0 then
          { p with terms := p.terms.erase exps }
        else
          { p with terms := p.terms.insert exps new }
    | none =>
        { p with terms := p.terms.insert exps coeff }


def addExps (a b : Array Nat) : Array Nat :=
  Id.run do
    let mut res := Array.mkEmpty a.size
    for i in [:a.size] do
      res := res.push (a[i]! + b[i]!)
    return res


def setExp (exps : Array Nat) (i : Nat) (v : Nat) : Array Nat :=
  arraySet exps i v


def add (p q : Poly) : Poly :=
  if p.nvars != q.nvars then
    panic! "Poly.add: nvars mismatch"
  else
    Id.run do
      let mut res := p
      for (k, v) in q.terms.toList do
        res := addTerm res k v
      return res


def neg (p : Poly) : Poly :=
  Id.run do
    let mut res := zero p.nvars
    for (k, v) in p.terms.toList do
      res := addTerm res k (-v)
    return res


def sub (p q : Poly) : Poly :=
  add p (neg q)


def mul (p q : Poly) : Poly :=
  if p.nvars != q.nvars then
    panic! "Poly.mul: nvars mismatch"
  else
    Id.run do
      let mut res := zero p.nvars
      for (k1, v1) in p.terms.toList do
        for (k2, v2) in q.terms.toList do
          let exps := addExps k1 k2
          res := addTerm res exps (v1 * v2)
      return res


def pow (p : Poly) (n : Nat) : Poly :=
  match n with
  | 0 => one p.nvars
  | n + 1 => mul (pow p n) p


def scale (p : Poly) (c : Rat) : Poly :=
  if c = 0 then
    zero p.nvars
  else
    Id.run do
      let mut res := zero p.nvars
      for (k, v) in p.terms.toList do
        res := addTerm res k (c * v)
      return res


def degree (p : Poly) (i : Nat) : Nat :=
  Id.run do
    let mut d := 0
    for (k, _) in p.terms.toList do
      let e := k[i]!
      if e > d then
        d := e
    return d


def leadingCoeff (p : Poly) (i : Nat) : Poly :=
  let d := degree p i
  Id.run do
    let mut res := zero p.nvars
    for (k, v) in p.terms.toList do
      if k[i]! == d then
        let k' := setExp k i 0
        res := addTerm res k' v
    return res


def red (p : Poly) (i : Nat) : Poly :=
  let d := degree p i
  Id.run do
    let mut res := zero p.nvars
    for (k, v) in p.terms.toList do
      if k[i]! != d then
        res := addTerm res k v
    return res


def redSet (p : Poly) (i : Nat) : List Poly :=
  if isConst p then
    []
  else
    Id.run do
      let d := degree p i
      let mut res : List Poly := []
      let mut curr := p
      for _ in [:d+1] do
        res := res.concat curr
        curr := red curr i
      return res


def derivative (p : Poly) (i : Nat) : Poly :=
  Id.run do
    let mut res := zero p.nvars
    for (k, v) in p.terms.toList do
      let e := k[i]!
      if e > 0 then
        let k' := setExp k i (e - 1)
        let v' := v * ratOfNat e
        res := addTerm res k' v'
    return res


def evalAReal (p : Poly) (assign : Std.HashMap Nat AReal) : AReal :=
  Id.run do
    let mut sum := AReal.fromRat 0
    for (k, v) in p.terms.toList do
      let mut term := AReal.fromRat v
      for j in [:p.nvars] do
        let e := k[j]!
        if e > 0 then
          let x := assign.getD j (AReal.fromRat 0)
          term := AReal.mul term (AReal.pow x e)
      sum := AReal.add sum term
    return sum


def compareExps (a b : Array Nat) : Ordering :=
  Id.run do
    let n := min a.size b.size
    for i in [:n] do
      let ai := a[i]!
      let bi := b[i]!
      if ai < bi then
        return Ordering.lt
      if ai > bi then
        return Ordering.gt
    return Ordering.eq


def toSortedList (p : Poly) : List (Array Nat × Rat) :=
  let lst := p.terms.toList
  listSort (fun x y => compareExps x.fst y.fst == Ordering.lt) lst


def eq (p q : Poly) : Bool :=
  if p.nvars != q.nvars then
    false
  else
    toSortedList p == toSortedList q


def normalizeSign (p : Poly) : Poly :=
  if isZero p then
    p
  else
    let lst := toSortedList p
    match lst.reverse with
    | [] => p
    | (_, c) :: _ =>
        if c < 0 then
          neg p
        else
          p


def toUnivariate (p : Poly) (mvar : Nat) : Array Poly :=
  let d := degree p mvar
  Id.run do
    let mut coeffs := Array.replicate (d + 1) (zero p.nvars)
    for (k, v) in p.terms.toList do
      let e := k[mvar]!
      let k' := setExp k mvar 0
      let curr := coeffs[e]!
      let term := addTerm (zero p.nvars) k' v
      coeffs := arraySet coeffs e (add curr term)
    return coeffs


def evalToUnivariateApprox (p : Poly) (mvar : Nat) (assign : Std.HashMap Nat AReal) : URatPoly :=
  let d := degree p mvar
  Id.run do
    let mut coeffs := Array.replicate (d + 1) (0 : Rat)
    for (k, v) in p.terms.toList do
      let e := k[mvar]!
      let mut coeff := AReal.fromRat v
      for j in [:p.nvars] do
        if j != mvar then
          let exp := k[j]!
          if exp > 0 then
            let x := assign.getD j (AReal.fromRat 0)
            coeff := AReal.mul coeff (AReal.pow x exp)
      let curr := coeffs[e]!
      coeffs := arraySet coeffs e (curr + AReal.approx coeff)
    return URatPoly.trim { coeffs := coeffs }


def simplifyAlgSub (p : Poly) (mvar : Nat) (assign : Std.HashMap Nat AReal) : URatPoly :=
  evalToUnivariateApprox p mvar assign

end Poly

instance : Pow Poly Nat where
  pow := Poly.pow

instance : HAdd Poly Poly Poly where
  hAdd p q := Poly.add p q

instance : HSub Poly Poly Poly where
  hSub p q := Poly.sub p q

instance : HMul Poly Poly Poly where
  hMul p q := Poly.mul p q

instance : Neg Poly where
  neg p := Poly.neg p

instance : HAdd Poly Rat Poly where
  hAdd p r := Poly.add p (Poly.const p.nvars r)

instance : HAdd Rat Poly Poly where
  hAdd r p := Poly.add (Poly.const p.nvars r) p

instance : HSub Poly Rat Poly where
  hSub p r := Poly.sub p (Poly.const p.nvars r)

instance : HSub Rat Poly Poly where
  hSub r p := Poly.sub (Poly.const p.nvars r) p

instance : HMul Poly Rat Poly where
  hMul p r := Poly.scale p r

instance : HMul Rat Poly Poly where
  hMul r p := Poly.scale p r


-- Determinant for Poly matrices (for PSCs)

partial def detPoly (nvars : Nat) (m : Array (Array Poly)) : Poly :=
  let n := m.size
  if n == 0 then
    Poly.const nvars 1
  else if n == 1 then
    (m[0]!)[0]!
  else
    Id.run do
      let mut acc := Poly.zero nvars
      for j in [:n] do
        let sign := if (j % 2) == 0 then (1 : Rat) else (-1 : Rat)
        let mut rows := Array.mkEmpty (n - 1)
        for i in [:n] do
          if i != 0 then
            let mut r := Array.mkEmpty (n - 1)
            for k in [:n] do
              if k != j then
                r := r.push ((m[i]!)[k]!)
            rows := rows.push r
        let cofactor := detPoly nvars rows
        let term := Poly.mul (Poly.scale (m[0]!)[j]! sign) cofactor
        acc := Poly.add acc term
      return acc


def subresultantCoefficients (f g : Poly) (mvar : Nat) : List Poly :=
  -- PSCs via subresultant matrices (slow but exact)
  let df := Poly.degree f mvar
  let dg := Poly.degree g mvar
  if dg == 0 then
    []
  else
    let (f, g, df, dg) :=
      if df < dg then (g, f, dg, df) else (f, g, df, dg)
    Id.run do
      let fCoeffs := Poly.toUnivariate f mvar
      let gCoeffs := Poly.toUnivariate g mvar
      let mut res : List Poly := []
      for k in [:dg] do
        let rowsF := dg - k
        let rowsG := df - k
        let size := df + dg - 2 * k
        let mut rows : Array (Array Poly) := Array.mkEmpty size
        for i in [:rowsF] do
          let mut row := Array.replicate size (Poly.zero f.nvars)
          for j in [:df+1] do
            if i + j < size then
              row := arraySet row (i + j) (fCoeffs[df - j]! )
          rows := rows.push row
        for i in [:rowsG] do
          let mut row := Array.replicate size (Poly.zero f.nvars)
          for j in [:dg+1] do
            if i + j < size then
              row := arraySet row (i + j) (gCoeffs[dg - j]! )
          rows := rows.push row
        let psc := detPoly f.nvars rows
        res := res.concat psc
      let lcPow := (Poly.leadingCoeff g mvar) ^ (df - dg)
      res := res.concat lcPow
      return res


def projone (F : List Poly) (mvar : Nat) : List Poly :=
  Id.run do
    let mut acc : List Poly := []
    for f in F do
      for g in Poly.redSet f mvar do
        acc := acc.concat (Poly.leadingCoeff g mvar)
        acc := acc ++ subresultantCoefficients g (Poly.derivative g mvar) mvar
    return acc


def projtwo (F : List Poly) (mvar : Nat) : List Poly :=
  Id.run do
    let mut acc : List Poly := []
    let arr := F.toArray
    for i in [:arr.size] do
      for j in [i+1:arr.size] do
        let f := arr[i]!
        let g := arr[j]!
        for f' in Poly.redSet f mvar do
          acc := acc ++ subresultantCoefficients f' g mvar
    return acc


def hongproj (F : List Poly) (mvar : Nat) : List Poly :=
  let proj := projone F mvar ++ projtwo F mvar
  Id.run do
    let mut uniq : List Poly := []
    for p in proj do
      if Poly.isConst p || Poly.isZero p then
        continue
      let p' := Poly.normalizeSign p
      if uniq.any (fun q => Poly.eq q p') then
        continue
      uniq := uniq.concat p'
    return uniq


-- CAD lifting and solving

inductive Rel where
  | lt | le | gt | ge | eq | ne
  deriving Repr, BEq

structure Constraint where
  poly : Poly
  rel : Rel


def epsRat : Rat := (1 : Rat) / 1000000


def holdsRel (rel : Rel) (x : AReal) : Bool :=
  let s := AReal.sign x 50
  match rel with
  | Rel.eq => s == 0
  | Rel.ne => s != 0
  | Rel.lt => s < 0
  | Rel.le => s <= 0
  | Rel.gt => s > 0
  | Rel.ge => s >= 0


def mergeCloseRoots (roots : List AReal) (eps : Rat) : List AReal :=
  let sorted := listSort (fun a b => AReal.approx a < AReal.approx b) roots
  let rec loop (lst : List AReal) (acc : List AReal) : List AReal :=
    match lst, acc with
    | [], _ => acc
    | r :: rs, [] => loop rs [r]
    | r :: rs, a :: accTail =>
        if ratAbs (AReal.approx r - AReal.approx a) <= eps then
          loop rs (a :: accTail)
        else
          loop rs (r :: a :: accTail)
  loop sorted [] |>.reverse


def getNiceRoots (p : URatPoly) : List AReal :=
  let intervals := URatPoly.realRootsIsolate p 60
  let roots := intervals.map (fun (a,b) => AReal.alg p a b)
  listSort (fun a b => AReal.approx a < AReal.approx b) roots


def getSamplePoint (l r : Option Rat) : Rat :=
  match l, r with
  | none, none => 0
  | none, some b =>
      Rat.ofInt (Rat.floor b) - 1
  | some a, none =>
      Rat.ofInt (Rat.ceil a) + 1
  | some a, some b =>
      let (a', b') := if a > b then (b, a) else (a, b)
      if a' == b' then
        a'
      else if a' < 0 && 0 < b' then
        if ratAbs a' <= epsRat || ratAbs b' <= epsRat then
          (a' + b') / 2
        else
          0
      else
        let mid := (a' + b') / 2
        let flo := Rat.ofInt (Rat.floor mid)
        let cei := Rat.ofInt (Rat.ceil mid)
        if a' < flo && flo < b' then
          flo
        else if a' < cei && cei < b' then
          cei
        else
          mid


def makeSamples (roots : List AReal) : List AReal :=
  match roots with
  | [] => [AReal.rat 0]
  | r0 :: rs =>
      let rec loop (prev : AReal) (rest : List AReal) (acc : List AReal) : List AReal :=
        match rest with
        | [] => acc ++ [AReal.rat (getSamplePoint (some (AReal.approx prev)) none)]
        | r :: rs =>
            let acc' := acc ++ [AReal.rat (getSamplePoint (some (AReal.approx prev)) (some (AReal.approx r))), r]
            loop r rs acc'
      let acc0 := [AReal.rat (getSamplePoint none (some (AReal.approx r0))), r0]
      loop r0 rs acc0


def collectRoots (projs : List Poly) (mvar : Nat) (assign : Std.HashMap Nat AReal) : List AReal :=
  Id.run do
    let mut roots : List AReal := []
    for p in projs do
      let up := Poly.simplifyAlgSub p mvar assign
      let rs := getNiceRoots up
      roots := roots ++ rs
    return mergeCloseRoots roots epsRat


def cylindricalAlgebraicDecomposition (polys : List Poly) (vars : Array String) : List (Std.HashMap Nat AReal) :=
  if vars.isEmpty then
    []
  else
    Id.run do
      let mut projSets : Array (List Poly) := #[polys]
      for i in [:vars.size - 1] do
        let prev := projSets[projSets.size - 1]!
        let next := hongproj prev i
        projSets := projSets.push next
      let mut samplePoints : List (Std.HashMap Nat AReal) := [{}]
      for i in (List.range vars.size).reverse do
        let projs := projSets[i]!
        let mut newPoints : List (Std.HashMap Nat AReal) := []
        for pt in samplePoints do
          let roots := collectRoots projs i pt
          let samples := makeSamples roots
          for v in samples do
            let pt' := pt.insert i v
            newPoints := newPoints.concat pt'
        samplePoints := newPoints
      return samplePoints


def assignmentToNameMap (assign : Std.HashMap Nat AReal) (vars : Array String) : Std.HashMap String AReal :=
  Id.run do
    let mut res : Std.HashMap String AReal := {}
    for i in [:vars.size] do
      let name := vars[i]!
      let value := assign.getD i (AReal.rat 0)
      res := res.insert name value
    return res


def solvePolySystemCAD (constraints : List Constraint) (vars : Array String) (returnOneSample : Bool := true)
    : List (Std.HashMap String AReal) :=
  let polys := constraints.map (fun c => c.poly)
  let samples := cylindricalAlgebraicDecomposition polys vars
  Id.run do
    let mut results : List (Std.HashMap String AReal) := []
    for pt in samples do
      let mut ok := true
      for c in constraints do
        let v := Poly.evalAReal c.poly pt
        if !holdsRel c.rel v then
          ok := false
      if ok then
        results := results.concat (assignmentToNameMap pt vars)
        if returnOneSample then
          break
    return results


-- Convenience constructors

def eq0 (p : Poly) : Constraint := { poly := p, rel := Rel.eq }

def ne0 (p : Poly) : Constraint := { poly := p, rel := Rel.ne }

def lt0 (p : Poly) : Constraint := { poly := p, rel := Rel.lt }

def le0 (p : Poly) : Constraint := { poly := p, rel := Rel.le }

def gt0 (p : Poly) : Constraint := { poly := p, rel := Rel.gt }

def ge0 (p : Poly) : Constraint := { poly := p, rel := Rel.ge }


-- Examples (approximate; uses eps tolerance)

def example1 : List (Std.HashMap String AReal) :=
  let vars := #["x"]
  let x := Poly.var vars.size 0
  solvePolySystemCAD [gt0 (x^2 + (1 : Rat))] vars


def example2 : List (Std.HashMap String AReal) :=
  let vars := #["x", "y"]
  let x := Poly.var vars.size 0
  let y := Poly.var vars.size 1
  solvePolySystemCAD [
    lt0 (x*y^2 - (4 : Rat)),
    lt0 (x^5 + x^3 - x*y + (5 : Rat))
  ] vars

end CadLean
