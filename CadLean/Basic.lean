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


def evalRat (p : Poly) (assign : Std.HashMap Nat Rat) : Rat :=
  Id.run do
    let mut sum : Rat := 0
    for (k, v) in p.terms.toList do
      let mut term := v
      for j in [:p.nvars] do
        let e := k[j]!
        if e > 0 then
          let x := assign.getD j 0
          term := term * ratPow x e
      sum := sum + term
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


def evalToUnivariate (p : Poly) (mvar : Nat) (assign : Std.HashMap Nat Rat) : Array Rat :=
  let d := degree p mvar
  Id.run do
    let mut coeffs := Array.replicate (d + 1) (0 : Rat)
    for (k, v) in p.terms.toList do
      let e := k[mvar]!
      let mut coeff := v
      for j in [:p.nvars] do
        if j != mvar then
          let exp := k[j]!
          if exp > 0 then
            let x := assign.getD j 0
            coeff := coeff * ratPow x exp
      let curr := coeffs[e]!
      coeffs := arraySet coeffs e (curr + coeff)
    return coeffs

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


-- Univariate polynomials over Rat (coeffs low -> high)
structure URatPoly where
  coeffs : Array Rat

namespace URatPoly


def zero : URatPoly :=
  { coeffs := #[] }


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
      else if c == 1 then
        [(a, b)]
      else
        let m := (a + b) / 2
        isolateAux p a m depth ++ isolateAux p m b depth


def isolate (p : URatPoly) (a b : Rat) (depth : Nat) : List (Rat × Rat) :=
  isolateAux p a b depth


def refineRootAux (p : URatPoly) (a b : Rat) : Nat → (Rat × Rat)
  | 0 => (a, b)
  | iters + 1 =>
      let m := (a + b) / 2
      if rootCount p a m == 1 then
        refineRootAux p a m iters
      else
        refineRootAux p m b iters


def refineRoot (p : URatPoly) (a b : Rat) (iters : Nat) : (Rat × Rat) :=
  refineRootAux p a b iters


def realRootsApprox (p : URatPoly) (depth : Nat := 60) (refine : Nat := 30) : List Rat :=
  if isZero p || degree p == 0 then
    []
  else
    let bound := rootBound p
    let intervals := isolate p (-bound) bound depth
    intervals.map (fun (a,b) =>
      let (a', b') := refineRoot p a b refine
      (a' + b') / 2
    )

end URatPoly


-- Determinant on matrices of polynomials (slow, for subresultants)

def minorMatrix (m : Array (Array Poly)) (row col : Nat) : Array (Array Poly) :=
  Id.run do
    let mut rows := Array.mkEmpty (m.size - 1)
    for i in [:m.size] do
      if i != row then
        let mut r := Array.mkEmpty (m.size - 1)
        for j in [:m.size] do
          if j != col then
            r := r.push ((m[i]!)[j]!)
        rows := rows.push r
    return rows


def detAux (nvars : Nat) : Nat → Array (Array Poly) → Poly
  | 0, _ => Poly.const nvars 1
  | 1, m => (m[0]!)[0]!
  | (n + 2), m =>
      Id.run do
        let mut acc := Poly.zero nvars
        for j in [:n+2] do
          let sign := if (j % 2) == 0 then (1 : Rat) else (-1 : Rat)
          let cofactor := detAux nvars (n + 1) (minorMatrix m 0 j)
          let term := Poly.mul (Poly.scale (m[0]!)[j]! sign) cofactor
          acc := Poly.add acc term
        return acc


def det (nvars : Nat) (m : Array (Array Poly)) : Poly :=
  detAux nvars m.size m


-- Hong projection operator using subresultant coefficients

def coeffsDesc (coeffs : Array Poly) : Array Poly :=
  let d := coeffs.size - 1
  Id.run do
    let mut res := Array.mkEmpty (d + 1)
    for i in [:d+1] do
      res := res.push (coeffs[d - i]!)
    return res


def subresultantMatrix (f g : Poly) (mvar k : Nat) : Array (Array Poly) :=
  let fCoeffs := coeffsDesc (Poly.toUnivariate f mvar)
  let gCoeffs := coeffsDesc (Poly.toUnivariate g mvar)
  let m := fCoeffs.size - 1
  let n := gCoeffs.size - 1
  let rowsF := n - k
  let rowsG := m - k
  let size := m + n - 2 * k
  Id.run do
    let mut rows : Array (Array Poly) := Array.mkEmpty size
    for i in [:rowsF] do
      let mut row := Array.replicate size (Poly.zero f.nvars)
      for j in [:m+1] do
        if i + j < size then
          row := arraySet row (i + j) (fCoeffs[j]! )
      rows := rows.push row
    for i in [:rowsG] do
      let mut row := Array.replicate size (Poly.zero f.nvars)
      for j in [:n+1] do
        if i + j < size then
          row := arraySet row (i + j) (gCoeffs[j]! )
      rows := rows.push row
    return rows


def subresultantCoefficients (f g : Poly) (mvar : Nat) : List Poly :=
  let df := Poly.degree f mvar
  let dg := Poly.degree g mvar
  if dg == 0 then
    []
  else
    let (f, g, dg) :=
      if df < dg then (g, f, df) else (f, g, dg)
    Id.run do
      let mut res : List Poly := []
      for k in [:dg] do
        let mat := subresultantMatrix f g mvar k
        let psc := det f.nvars mat
        res := res.concat psc
      -- final PSC term (approximate): leading coefficient of g
      res := res.concat (Poly.leadingCoeff g mvar)
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


def holdsRel (rel : Rel) (x : Rat) : Bool :=
  let s :=
    if ratAbs x <= epsRat then 0
    else if x < 0 then -1 else 1
  match rel with
  | Rel.eq => s == 0
  | Rel.ne => s != 0
  | Rel.lt => s < 0
  | Rel.le => s <= 0
  | Rel.gt => s > 0
  | Rel.ge => s >= 0


def mergeCloseRoots (roots : List Rat) (eps : Rat) : List Rat :=
  let sorted := listSort (fun a b => a < b) roots
  let rec loop (lst : List Rat) (acc : List Rat) : List Rat :=
    match lst, acc with
    | [], _ => acc
    | r :: rs, [] => loop rs [r]
    | r :: rs, a :: accTail =>
        if ratAbs (r - a) <= eps then
          loop rs (a :: accTail)
        else
          loop rs (r :: a :: accTail)
  loop sorted [] |>.reverse


def getSamplePoint (l r : Option Rat) : Rat :=
  match l, r with
  | none, none => 0
  | none, some b => b - 1
  | some a, none => a + 1
  | some a, some b =>
      let (a', b') := if a > b then (b, a) else (a, b)
      if a' == b' then
        a'
      else if a' < 0 && 0 < b' then
        0
      else
        (a' + b') / 2


def makeSamples (roots : List Rat) : List Rat :=
  match roots with
  | [] => [0]
  | r0 :: rs =>
      let rec loop (prev : Rat) (rest : List Rat) (acc : List Rat) : List Rat :=
        match rest with
        | [] => acc ++ [getSamplePoint (some prev) none]
        | r :: rs =>
            let acc' := acc ++ [getSamplePoint (some prev) (some r), r]
            loop r rs acc'
      let acc0 := [getSamplePoint none (some r0), r0]
      loop r0 rs acc0


def evalToURatPoly (p : Poly) (mvar : Nat) (assign : Std.HashMap Nat Rat) : URatPoly :=
  let coeffs := Poly.evalToUnivariate p mvar assign
  URatPoly.trim { coeffs := coeffs }


def collectRoots (projs : List Poly) (mvar : Nat) (assign : Std.HashMap Nat Rat) : List Rat :=
  Id.run do
    let mut roots : List Rat := []
    for p in projs do
      let up := evalToURatPoly p mvar assign
      let rs := URatPoly.realRootsApprox up
      roots := roots ++ rs
    return mergeCloseRoots roots epsRat


def cylindricalAlgebraicDecomposition (polys : List Poly) (vars : Array String) : List (Std.HashMap Nat Rat) :=
  if vars.isEmpty then
    []
  else
    Id.run do
      let mut projSets : Array (List Poly) := #[polys]
      for i in [:vars.size - 1] do
        let prev := projSets[projSets.size - 1]!
        let next := hongproj prev i
        projSets := projSets.push next
      let mut samplePoints : List (Std.HashMap Nat Rat) := [{}]
      for i in (List.range vars.size).reverse do
        let projs := projSets[i]!
        let mut newPoints : List (Std.HashMap Nat Rat) := []
        for pt in samplePoints do
          let roots := collectRoots projs i pt
          let samples := makeSamples roots
          for v in samples do
            let pt' := pt.insert i v
            newPoints := newPoints.concat pt'
        samplePoints := newPoints
      return samplePoints


def assignmentToNameMap (assign : Std.HashMap Nat Rat) (vars : Array String) : Std.HashMap String Rat :=
  Id.run do
    let mut res : Std.HashMap String Rat := {}
    for i in [:vars.size] do
      let name := vars[i]!
      let value := assign.getD i 0
      res := res.insert name value
    return res


def solvePolySystemCAD (constraints : List Constraint) (vars : Array String) (returnOneSample : Bool := true)
    : List (Std.HashMap String Rat) :=
  let polys := constraints.map (fun c => c.poly)
  let samples := cylindricalAlgebraicDecomposition polys vars
  Id.run do
    let mut results : List (Std.HashMap String Rat) := []
    for pt in samples do
      let mut ok := true
      for c in constraints do
        let v := Poly.evalRat c.poly pt
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

def example1 : List (Std.HashMap String Rat) :=
  let vars := #["x"]
  let x := Poly.var vars.size 0
  solvePolySystemCAD [gt0 (x^2 + (1 : Rat))] vars


def example2 : List (Std.HashMap String Rat) :=
  let vars := #["x", "y"]
  let x := Poly.var vars.size 0
  let y := Poly.var vars.size 1
  solvePolySystemCAD [
    lt0 (x*y^2 - (4 : Rat)),
    lt0 (x^5 + x^3 - x*y + (5 : Rat))
  ] vars

end CadLean
