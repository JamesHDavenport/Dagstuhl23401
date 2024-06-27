-- A computational representation of Polynomials in several (anonymous) variables
-- over a commutative ring R
-- Representation is distributed and sparse, number of variables if fixed as nvars
-- Computational implies that need DecidableEq for R
-- Based on univariates by Mario Carniero at Hausdorff Institute June 2024
-- Representation is as a list of pairs (exponent, coefficient) in ℕ × R
-- Exponents in decreasing order, coefficients non-zero (so zero polynomial is empty list)
-- Note that Lean allows the ring with just 0 (so 1=0)
-- JHD: we may wish to rethink allowing this, as it causes extra checks

import Mathlib.Algebra.Polynomial.Eval
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib

@[ext] structure MvDegrees (nvars : ℕ) where
  degrees: Array ℕ
  correct: degrees.size = nvars
  totalDegree : ℕ
  totalDegree_eq : totalDegree = degrees.foldl (· + ·) 0

instance : AddCommMonoid (MvDegrees nvars) where
  add a b := {
    degrees := a.degrees.zipWith b.degrees (· + ·)
    correct := sorry
    totalDegree := a.totalDegree + b.totalDegree
    totalDegree_eq := sorry
  }
  add_assoc := sorry
  zero := {
    degrees := Array.mkArray nvars 0
    correct := by simp
    totalDegree := 0
    totalDegree_eq := sorry
  }
  zero_add := sorry
  add_zero := sorry
  nsmul n a := {
    degrees := a.degrees.map (· * n)
    correct := sorry
    totalDegree := a.totalDegree * n
    totalDegree_eq := sorry
  }
  nsmul_zero := sorry
  nsmul_succ := sorry
  add_comm := sorry

-- @[ext] structure MvMonomial (R : Type) (nvars : ℕ) where
--   coeff : R
--   degrees : MvDegrees nvars

@[ext] class WOrdering (nvars : ℕ) extends LinearOrder (MvDegrees nvars) where
  zero_le {x : MvDegrees nvars} : 0 ≤ x
  add_le_add {x y z : MvDegrees nvars} : x ≤ y → x + z ≤ y + z

-- def lexordering (a: MvDegrees nvars,b: MvDegrees nvars) : Bool := sorry
-- But also needs to be a member of WOrdering

@[ext] structure MvSparsePoly (R : Type) [CommRing R] (nvars : ℕ) [WOrdering nvars] : Type where
  terms : List (MvDegrees nvars × R)
  sorted : terms.Sorted (·.1 > ·.1)
  nonzero : ∀ x ∈ terms, x.2 ≠ 0

namespace MvSparsePoly
open MvPolynomial

--instance [CommRing R] [Lean.ToFormat R] : Lean.ToFormat (MvSparsePoly R nvars) where
--  format x :=
--    have := x.terms.foldl (init := none) fun (f : Option Lean.Format) (i, x) =>
--      let monomial := if i = 0 then f!"({x})" else if i = 1 then f!"({x})*X" else f!"({x})*X^{i}"
--      match f with
--      | none => monomial
--      | some f => f ++ " + " ++ monomial
--    this.getD f!"0"
--instance [CommRing R] [Lean.ToFormat R] : Repr (SparsePoly R) where
--  reprPrec x _ := Lean.format x

variable {R : Type} [CommRing R] [DecidableEq R] [WOrdering nvars]
def ofSortedList
    (terms : List (MvDegrees nvars × R)) (sorted : terms.Sorted (·.1 > ·.1)) :
    MvSparsePoly R nvars where
  terms := terms.filter (·.2 ≠ 0)
  sorted := sorted.sublist (List.filter_sublist _)
  nonzero := by simp [List.mem_filter]

instance : Zero (MvSparsePoly R nvars) where
  zero := { terms := [], sorted := .nil, nonzero := nofun }

def C (r : R) : MvSparsePoly R nvars := ofSortedList [(0, r)] (List.sorted_singleton _)
-- Need the ofSortedList to deal with r=0; note that 0 is the 0 of the MvDegrees monoid

instance : One (MvSparsePoly R nvars) where
  one := C 1

-- def degLt (a : ℕ) (l : List (ℕ × R)) : Prop := ∀ x ∈ l, x.1 < a

-- Relate our structures to the MvPolynomial of Mathlib
noncomputable def MvDegrees.toFinsupp (deg : MvDegrees nvars) : Fin nvars →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun i => deg.degrees[i]'(by simp [deg.correct, i.2])) (by simp)

noncomputable def toPolyCore : List (MvDegrees nvars × R) → MvPolynomial (Fin nvars) R
  | [] => 0
  | (i, a) :: x => monomial (MvDegrees.toFinsupp i) a + toPolyCore x

noncomputable def toPoly (x : MvSparsePoly R nvars) : MvPolynomial (Fin nvars) R :=
  toPolyCore x.terms

def addCore : List (ℕ × R) → List (ℕ × R) → List (ℕ × R)
  | [], y => y
  | x, [] => x
  | (i, a) :: x, (j, b) :: y =>
    if i < j then
      (j, b) :: addCore ((i, a) :: x) y
    else if j < i then
      (i, a) :: addCore x ((j, b) :: y)
    else  -- Don't we want to worry about a+b=0
      (i, a + b) :: addCore x y

theorem addCore_degLt {n : ℕ} : ∀ {x y : List (ℕ × R)},
    degLt n x → degLt n y → degLt n (addCore x y) := by
  intro x y hx hy
  unfold addCore
  split
  · exact hy
  · exact hx
  · next i a x j b y =>
    let ⟨hi, hx'⟩ := List.forall_mem_cons.1 hx
    sorry
--     let .cons hj hy' := hy
--     split
--     · next ij =>
--       constructor
--       · apply addCore_degLt
--         · intro
--           | _, .head _ => exact ij
--           | p, .tail _ hp => exact (hi _ hp).trans ij
--         · exact hj
--       · exact addCore_sorted hx hy'
--     split
--     · next ij =>
--       constructor
--       · apply addCore_degLt
--         · exact hi
--         · intro
--         | _, .head _ => exact ij
--         | p, .tail _ hp => exact (hj _ hp).trans ij
--       · exact addCore_sorted hx' hy
--     · cases (by omega : i = j)
--       constructor
--       · exact addCore_degLt hi hj
--       · exact addCore_sorted hx' hy'
-- termination_by x y => x.length + y.length

theorem addCore_sorted : ∀ {x y : List (ℕ × R)},
    x.Sorted (·.1 > ·.1) → y.Sorted (·.1 > ·.1) →
    (addCore x y).Sorted (·.1 > ·.1) := by
  intro x y hx hy
  unfold addCore
  split
  · exact hy
  · exact hx
  · next i a x j b y =>
    let .cons hi hx' := hx
    let .cons hj hy' := hy
    split
    · next ij =>
      constructor
      · apply addCore_degLt
        · intro
          | _, .head _ => exact ij
          | p, .tail _ hp => exact (hi _ hp).trans ij
        · exact hj
      · exact addCore_sorted hx hy'
    split
    · next ij =>
      constructor
      · apply addCore_degLt
        · exact hi
        · intro
        | _, .head _ => exact ij
        | p, .tail _ hp => exact (hj _ hp).trans ij
      · exact addCore_sorted hx' hy
    · cases (by omega : i = j)
      constructor
      · exact addCore_degLt hi hj
      · exact addCore_sorted hx' hy'
termination_by x y => x.length + y.length

instance : Add (MvSparsePoly R nvars) where
  add x y :=
    let terms := addCore x.terms y.terms
    ofSortedList terms (addCore_sorted x.sorted y.sorted)

def dedupList : List (ℕ × R) → List (ℕ × R)
  | (i, a) :: (j, b) :: x =>
    if i = j then
      dedupList ((i, a + b) :: x)
    else
      (i, a) :: dedupList ((j, b) :: x)
  | x => x

theorem dedupList_sorted (terms : List (ℕ × R))
  (sorted : terms.Sorted (·.1 ≥ ·.1)) :
  (dedupList terms).Sorted (·.1 > ·.1) := sorry

def ofList (terms : List (ℕ × R)) : MvSparsePoly R nvars :=
  let terms' := terms.mergeSort (·.1 ≥ ·.1)
  have : IsTotal (ℕ × R) (·.1 ≥ ·.1) := sorry
  have : IsTrans (ℕ × R) (·.1 ≥ ·.1) := sorry
  ofSortedList (dedupList terms')
    (dedupList_sorted terms' (terms.sorted_mergeSort _))

def X : MvSparsePoly R nvars := ofSortedList [(1, 1)] (List.sorted_singleton _)

instance : Mul (MvSparsePoly R nvars) where
  mul x y :=
    ofList do
      let (i, a) ← x.terms
      let (j, b) ← y.terms
      return (i + j, a * b)

instance : Neg (MvSparsePoly R nvars) where
  neg x := C (-1) * x


instance : CommRing (MvSparsePoly R nvars) where
  add := (·+·)
  add_assoc := sorry
  zero := 0
  zero_add := sorry
  add_zero := sorry
  nsmul := (C (R := R) · * ·)
  add_comm := sorry
  mul := (·*·)
  left_distrib := sorry
  right_distrib := sorry
  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one := 1
  one_mul := sorry
  mul_one := sorry
  neg := (-·)
  zsmul := zsmulRec (C (R := R) · * ·)
  add_left_neg := sorry
  mul_comm := sorry
  natCast n := C n
  nsmul_zero := sorry
  nsmul_succ := sorry
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry
  natCast_zero := sorry
  natCast_succ := sorry
  -- refine' {
  --   zero := 0, one := 1, add := (·+·), mul := (·*·)
  --   sub := (·+-·), neg := (-·)
  --   npow := npowRec
  --   nsmul := nsmulRec
  --   zsmul := zsmulRec
  --   .. } <;> sorry
#print AddMonoidWithOne
instance : Algebra R (MvSparsePoly R nvars) := by
  refine' { toFun := C, smul := fun a r => C a * r, ..} <;> sorry

class IsExactDiv (R : Type*) [Monoid R] [Div R] : Prop where
  mul_div_cancel {a b : R} : b ∣ a → b * (a / b) = a

def degree (a : MvSparsePoly R nvars) : ℕ := (a.terms.headD (0, 0)).1

def gcdPrim (a b : MvSparsePoly R nvars) : MvSparsePoly R nvars :=
  match a.terms with
  | [] => b
  | (i, x) :: as =>
    match b.terms with
    | [] => a
    | (j, y) :: bs =>
      if i > j then
        gcdPrim (y • a - x • X^(i-j) * b) b
      else
        gcdPrim a (x • b - y • X^(j-i) * a)
termination_by a.degree + b.degree
decreasing_by all_goals sorry

def content [CancelCommMonoidWithZero R] [GCDMonoid R] (a : MvSparsePoly R nvars) : R :=
  a.terms.foldl (init := 0) (gcd · ·.2)

def primitivePart [CancelCommMonoidWithZero R] [GCDMonoid R]
    [Div R] [IsExactDiv R] (a : MvSparsePoly R nvars) : MvSparsePoly R nvars where
  terms :=
    let b := a.content
    a.terms.map fun (i, a) => (i, a / b)
  sorted := sorry
  nonzero := sorry

nonrec def gcd [CancelCommMonoidWithZero R] [GCDMonoid R]
    [Div R] [IsExactDiv R] (a b : MvSparsePoly R nvars) : MvSparsePoly R nvars :=
  gcd a.content b.content • (gcdPrim a b).primitivePart

instance : IsExactDiv ℤ where
  mul_div_cancel := Int.mul_ediv_cancel'

instance {R} [CommGroupWithZero R] : IsExactDiv R where
  mul_div_cancel h := by
    apply mul_div_cancel_of_imp'; rintro rfl
    simpa only [zero_dvd_iff] using h

-- divRem a b = (q, r) -> a = b * q + r
def divRem [Div R] (a b : MvSparsePoly R nvars) : MvSparsePoly R nvars × MvSparsePoly R nvars :=
  match a.terms, b.terms with
  | (i, x) :: _, (j, y) :: _ =>
    if i < j then
      (0, a)
    else
      let c := (x / y) • X^(i-j)
      if y * (x / y) = x then
        let (q', r') := divRem (a - c * b) b
        (q' + c, r')
      else
        (0, a)
  | _, _ => (0, a)
termination_by a.degree
decreasing_by all_goals sorry

instance [Div R] : Div (MvSparsePoly R nvars) where
  div a b := (divRem a b).1

instance [Div R] [IsExactDiv R] : IsExactDiv (MvSparsePoly R nvars) where
  mul_div_cancel h := sorry

instance : DecidableEq (MvSparsePoly R nvars) := fun a b =>
  decidable_of_iff' (a.terms = b.terms) (SparsePoly.ext_iff ..)

#eval (X * (C X * X + C (X + 2) : SparsePoly (SparsePoly ℤ))) / X

noncomputable def toPolyEquiv : MvSparsePoly R nvars ≃ₐ[R] Polynomial R where
  toFun := toPoly
  invFun p := p.eval₂ (algebraMap ..) X
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry
  map_mul' := sorry
  commutes' := sorry

@[simp]
theorem ofPoly_X : toPolyEquiv.symm Polynomial.X = (X : MvSparsePoly R nvars) := by
  simp [toPolyEquiv]

@[simp]
theorem toPoly_X : (X : MvSparsePoly R nvars).toPoly = Polynomial.X := by
  rw [← toPolyEquiv.apply_symm_apply Polynomial.X, ofPoly_X]; rfl
