/-
Copyright (c) 2023 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/

import Mathlib.Data.Polynomial.RingDivision
import Mathlib

/-!
# Mahler Measure

## Main definitions

* `MahlerMeasure`

## Notation

* `M` is used for the Mahler measure of a polynomial, as in `M f`.

## References

* https://en.wikipedia.org/wiki/Mahler_measure

-/


open BigOperators

variable {R : Type _} [CommRing R] [Algebra R ℂ] [NoZeroSMulDivisors R ℂ]

namespace Polynomial
noncomputable
def mahlerMeasure (f : R[X]) : ℂ :=
  ((f.aroots ℂ).map (fun α => max ‖α‖ 1)).prod * (algebraMap R ℂ f.leadingCoeff)

lemma one_le_mahlerMeasure {f : R[X]} : ‖algebraMap R ℂ f.leadingCoeff‖ ≤ ‖f.mahlerMeasure‖ := by
  simp [mahlerMeasure]
  -- apply?
  sorry
  -- rw?

@[simp]
lemma mahlerMeasure_zero : mahlerMeasure (0 : R[X]) = 0 := by
  simp [mahlerMeasure]

@[simp]
lemma mahlerMeasure_one : mahlerMeasure (1 : R[X]) = 1 := by
  simp [mahlerMeasure]

@[simp]
lemma mahlerMeasure_X : mahlerMeasure (X : R[X]) = 1 := by
  simp [mahlerMeasure]

@[to_additive (attr := simp)]
theorem _root_.Multiset.map_smul {α β : Type _} (f : α → β) (d : ℕ) (u : Multiset α) :
    (d • u).map f =  d • (u.map f) := by
  exact Multiset.map_nsmul f d u  -- TODO simp?

open Multiset in
-- @[to_additive (attr := simp)]
@[simp]
theorem _root_.Multiset.prod_smul {α : Type _} [CommMonoid α] (d : ℕ) (u : Multiset α) :
    (d • u).prod = u.prod ^ d := by
  exact prod_nsmul u d -- TODO simp?

@[simp]
lemma mahlerMeasure_X_pow {n : ℕ} : mahlerMeasure (X ^ n : R[X]) = 1 := by
  simp [mahlerMeasure, Multiset.map_smul]

@[simp]
lemma mahlerMeasure_C {r : R} : mahlerMeasure (C r) = algebraMap R ℂ r := by
  simp [mahlerMeasure]

-- TODO is this useless?
lemma mahlerMeasure_smul {r : R} {f : R[X]} (h : IsSMulRegular R r) (hr : r ≠ 0) :
    mahlerMeasure (r • f) = algebraMap R ℂ r • mahlerMeasure f := by
  simp [mahlerMeasure, aroots_smul_nonzero _ hr,
    leadingCoeff_smul_of_smul_regular _ h, Algebra.left_comm]

lemma isDomain_of_noZeroSMulDivisors (F G : Type _) [CommRing F] [Field G] [Algebra F G]
    [NoZeroSMulDivisors F G] :
    IsDomain F :=
  Function.Injective.isDomain (algebraMap F G) (NoZeroSMulDivisors.algebraMap_injective F G)

@[simp]
lemma mahlerMeasure_mul {f g : R[X]} : -- TODO domain should be free?
    mahlerMeasure (f * g) = mahlerMeasure f * mahlerMeasure g := by
  by_cases hf : f = 0
  · simp [hf]
  by_cases hg : g = 0
  · simp [hg]
  have := isDomain_of_noZeroSMulDivisors R ℂ
  simp [mahlerMeasure, aroots_mul (mul_ne_zero hf hg), mul_mul_mul_comm]

@[simp]
lemma mahlerMeasure_smul' {r : R} {f : R[X]} :
    mahlerMeasure (r • f) = algebraMap R ℂ r • mahlerMeasure f := by
  simp [smul_eq_C_mul]

@[simp]
lemma leadingCoeff_cyclotomic' {n : ℕ} [IsDomain R] : leadingCoeff (Polynomial.cyclotomic' n R) = 1 :=
  cyclotomic'.monic n R

@[simp]
lemma leadingCoeff_cyclotomic {n : ℕ} : leadingCoeff (Polynomial.cyclotomic n R) = 1 := by
  exact cyclotomic.monic n _
-- set_option maxHeartbeats 0 in
lemma mahlerMeasure_cyclotomic {n : ℕ} : mahlerMeasure (Polynomial.cyclotomic n R) = 1 := by
  by_cases hn : n = 0
  · simp [hn]
  simp only [mahlerMeasure, aroots_def, map_cyclotomic, Complex.norm_eq_abs, ge_iff_le,
    leadingCoeff_cyclotomic, map_one, mul_one, Complex.ofReal_eq_one]
  have := (int_cyclotomic_spec n).1
  simp only [map_cyclotomic] at this
  simp only [this, ge_iff_le]  -- TOOD eh
  rw [roots_of_cyclotomic]
  convert Multiset.prod_map_one
  rename_i x hx
  simp only [ge_iff_le, max_eq_right_iff]
  simp only [Finset.mem_val] at hx
  rw [mem_primitiveRoots (Nat.pos_of_ne_zero hn)] at hx
  apply Eq.le
  rw [← Complex.norm_eq_abs]
  exact IsPrimitiveRoot.norm'_eq_one hx hn -- maybe want isprimitve.abs_eq_one

-- variable (p : ℂ[X])
-- -- def ad (i : p.support) : ℂ   := p.coeff i.val


-- #check  p.coeff
-- #check ((WithLp.equiv 2 (ℕ → ℂ)).symm p.coeff : WithLp 2 (ℕ → ℂ))
