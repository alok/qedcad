import LeanBench
import CadLean.Basic

open CadLean

-- Simple helpers for benches

def poly2 (terms : List (Array Nat × Rat)) : Poly :=
  Id.run do
    let mut p := Poly.zero 2
    for (exps, coeff) in terms do
      p := Poly.addTerm p exps coeff
    return p


def urat (coeffs : List Rat) : URatPoly :=
  URatPoly.trim { coeffs := coeffs.toArray }


def vars2 : Array String := #["x", "y"]


def pconst (n : Nat) (r : Rat) : Poly :=
  Poly.const n r


bench "spin.1e6" do
  let mut acc : Nat := 0
  for i in [0:1_000_000] do
    acc := acc + i
  if acc == 1234567 then
    IO.println ""
  pure ()


bench "roots.quad" do
  let t ← IO.monoNanosNow
  let shift : Rat := Rat.ofInt (Int.ofNat (t % 3))
  let p := URatPoly.add (urat [(-2 : Rat), 0, 1]) (URatPoly.const shift)
  let mut acc := 0
  for _ in [:10] do
    let res := URatPoly.realRootsIsolate p 40
    acc := acc + res.length
  if acc == 999 then
    IO.println ""
  pure ()


bench "proj.hong" do
  let t ← IO.monoNanosNow
  let shift : Rat := Rat.ofInt (Int.ofNat (t % 3))
  let x := Poly.var 2 0
  let y := Poly.var 2 1
  let p0 := Poly.add (x^2) y
  let p1 := Poly.sub (x*y^2) (pconst 2 (3 : Rat))
  let p2 := Poly.add (Poly.add x y) (pconst 2 shift)
  let polys : List Poly := [p0, p1, p2]
  let mut acc := 0
  for _ in [:10] do
    let res := hongproj polys 0
    acc := acc + res.length
  if acc == 999 then
    IO.println ""
  pure ()


bench "cad.small" do
  let t ← IO.monoNanosNow
  let shift : Rat := Rat.ofInt (Int.ofNat (t % 3))
  let x := Poly.var 2 0
  let y := Poly.var 2 1
  let p0 := Poly.add (x^2) (pconst 2 (1 : Rat))
  let p1 := Poly.sub (x*y^2) (pconst 2 (4 : Rat))
  let p2base := Poly.add (Poly.sub (Poly.add (x^5) (x^3)) (x*y)) (pconst 2 (5 : Rat))
  let p2 := Poly.add p2base (pconst 2 shift)
  let constraints : List Constraint := [
    gt0 p0,
    lt0 p1,
    lt0 p2
  ]
  let mut acc := 0
  for _ in [:1] do
    let res := solvePolySystemCAD constraints vars2
    acc := acc + res.length
  if acc == 999 then
    IO.println ""
  pure ()


bench "cad.linear" do
  let t ← IO.monoNanosNow
  let shift : Rat := Rat.ofInt (Int.ofNat (t % 3))
  let p0 := poly2 [(#[1, 0], (2 : Rat))]
  let p1 := poly2 [(#[1, 0], (-2 : Rat)), (#[0, 0], (2 : Rat) + shift)]
  let constraints : List Constraint := [gt0 p0, gt0 p1]
  let mut acc := 0
  for _ in [:5] do
    let res := solvePolySystemCAD constraints vars2
    acc := acc + res.length
  if acc == 999 then
    IO.println ""
  pure ()


def main (args : List String) : IO UInt32 :=
  LeanBench.runMain args
