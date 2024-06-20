import Mathlib.Algebra.Polynomial.Eval
import Mathlib

structure SparsePoly (R : Type) [CommRing R] : Type where
  coeffs : List (ℕ × R)
  sorted : coeffs.Sorted (·.1 > ·.1)
  nonzero : ∀ x ∈ coeffs, x.2 ≠ 0

namespace SparsePoly
open Polynomial

variable [CommRing R] [DecidableEq R]
def ofSortedList
    (coeffs : List (ℕ × R)) (sorted : coeffs.Sorted (·.1 > ·.1)) :
    SparsePoly R where
  coeffs := coeffs.filter (·.2 ≠ 0)
  sorted := sorted.sublist (List.filter_sublist _)
  nonzero := by simp [List.mem_filter]

instance : Zero (SparsePoly R) where
  zero := { coeffs := [], sorted := .nil, nonzero := nofun }

def C (r : R) : SparsePoly R := ofSortedList [(0, r)] (List.sorted_singleton _)

instance : One (SparsePoly R) where
  one := C 1

def degLt (a : ℕ) (l : List (ℕ × R)) : Prop := ∀ x ∈ l, x.1 < a

noncomputable def toPolyCore : List (ℕ × R) → R[X]
  | [] => 0
  | (i, a) :: x => Polynomial.C a * Polynomial.X^i + toPolyCore x

noncomputable def toPoly (x : SparsePoly R) : Polynomial R :=
  toPolyCore x.coeffs

def addCore : List (ℕ × R) → List (ℕ × R) → List (ℕ × R)
  | [], y => y
  | x, [] => x
  | (i, a) :: x, (j, b) :: y =>
    if i < j then
      (j, b) :: addCore ((i, a) :: x) y
    else if j < i then
      (i, a) :: addCore x ((j, b) :: y)
    else
      (i, a + b) :: addCore x y

theorem addCore_sorted : ∀ (x y : List (ℕ × R)),
    x.Sorted (·.1 > ·.1) → y.Sorted (·.1 > ·.1) →
    (addCore x y).Sorted (·.1 > ·.1) := sorry
  -- | [], y, _, hy => hy
  -- | x, [], hx, _ => hx
  -- | (i, a) :: x, (j, b) :: y, hx, hy =>
  --   if hi : i < j then
  --     let ⟨hb, hy⟩ := List.pairwise_cons.1 hy
  --     let ⟨y', hy'⟩ := addCore ((i, a) :: x) y hx hy
  --     ⟨(j, b) :: y', .cons (_) hy'⟩
  --   else
  --     let ⟨ha, hx⟩ := List.pairwise_cons.1 hx
  --     _

instance : Add (SparsePoly R) where
  add x y :=
    let coeffs := addCore x.coeffs y.coeffs
    ofSortedList coeffs (addCore_sorted _ _ x.sorted y.sorted)

def mulCore : List (ℕ × R) → List (ℕ × R) → List (ℕ × R)
  | [], y => y
  | x, [] => x
  | (i, a) :: x, (j, b) :: y =>
    if i < j then
      (j, b) :: addCore ((i, a) :: x) y
    else if j < i then
      (i, a) :: addCore x ((j, b) :: y)
    else
      (i, a + b) :: addCore x y

def dedupList : List (ℕ × R) → List (ℕ × R)
  | (i, a) :: (j, b) :: x =>
    if i = j then
      dedupList ((i, a + b) :: x)
    else
      (i, a) :: dedupList ((j, b) :: x)
  | x => x

theorem dedupList_sorted (coeffs : List (ℕ × R))
  (sorted : coeffs.Sorted (·.1 ≥ ·.1)) :
  (dedupList coeffs).Sorted (·.1 > ·.1) := sorry

def ofList (coeffs : List (ℕ × R)) : SparsePoly R :=
  let coeffs' := coeffs.mergeSort (·.1 ≥ ·.1)
  have : IsTotal (ℕ × R) (·.1 ≥ ·.1) := sorry
  have : IsTrans (ℕ × R) (·.1 ≥ ·.1) := sorry
  ofSortedList (dedupList coeffs')
    (dedupList_sorted coeffs' (coeffs.sorted_mergeSort _))

def X : SparsePoly R := ofSortedList [(1, 1)] (List.sorted_singleton _)

instance : Mul (SparsePoly R) where
  mul x y :=
    ofList do
      let (i, a) ← x.coeffs
      let (j, b) ← y.coeffs
      return (i + j, a * b)

instance : CommRing (SparsePoly R) := by
  refine' { zero := 0, one := 1, add := (·+·), mul := (·*·), .. } <;> sorry

instance : Algebra R (SparsePoly R) := by refine' { toFun := C, ..} <;> sorry

noncomputable def toPolyEquiv : SparsePoly R ≃ₐ[R] Polynomial R where
  toFun := toPoly
  invFun p := p.eval₂ (algebraMap ..) X
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry
  map_mul' := sorry
  commutes' := sorry

@[simp]
theorem ofPoly_X : toPolyEquiv.symm Polynomial.X = (X : SparsePoly R) := by
  simp [toPolyEquiv]

@[simp]
theorem toPoly_X : (X : SparsePoly R).toPoly = Polynomial.X := by
  rw [← toPolyEquiv.apply_symm_apply Polynomial.X, ofPoly_X]; rfl
