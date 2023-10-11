/-
Copyright (c) 2023 Alex J. Best, Edgar Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Edgar Costa
-/

import Mathlib.Data.Polynomial.RingDivision
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
--import Mathlib

/-!
# Mahler Measure

## Main definitions

* MahlerMeasure

## Notation

* M is used for the Mahler measure of a polynomial, as in M f.

## References

* https://en.wikipedia.org/wiki/Mahler_measure

-/


open BigOperators
open Polynomial
open Multiset
open ComplexConjugate

-- We need NoZeroSMulDivisors as we could take R = C[x]/x^2
variable {R : Type _} [CommRing R] [Algebra R ℂ] [NoZeroSMulDivisors R ℂ] [IsDomain R]


noncomputable
def mahlerMeasure (f : R[X]) : ℝ :=
  ((f.aroots ℂ).map (fun α => max ‖α‖ 1)).prod * ‖algebraMap R ℂ f.leadingCoeff‖

@[simp]
lemma mahler_zero :
    mahlerMeasure (0 : R[X]) = 0 := by
  rw [mahlerMeasure]
  simp

@[simp]
lemma mahler_mul (f g : R[X]) :
    mahlerMeasure (f*g) = mahlerMeasure f * mahlerMeasure g:= by
  --(f*g).arroots ℂ = (f.arroots ℂ) union (g.roots ℂ)
  by_cases a1: f=0
  . simp [a1]
  by_cases a2: g=0
  . simp [a2]
  have : f*g ≠ 0
  . simp
    rw [@not_or]
    simp[a1,a2]
  simp [mahlerMeasure]
  rw [@mul_mul_mul_comm]
  rw [aroots_mul this]
  simp
  done

-- # check p.coeff
-- # check ((WithLp.equiv 2 (ℕ → ℂ).symm p.coeff : WithLp 2 (ℕ → ℂ)))
noncomputable
def L2normSq (f : R[X]) : ℝ :=
  ∑ a in f.support, ‖algebraMap R ℂ (f.coeff a)‖^2

@[simp]
lemma L2normSq_zero : L2normSq (0 : R[X]) = 0 := by
  simp [L2normSq]

universe u v
theorem support_smul_eq {R : Type u} {S : Type v} [Semiring R] [Semiring S] [SMulWithZero S R] (r : S) (h: r ≠ 0) [NoZeroSMulDivisors S R] (p : R[X]) :
    support (r • p) = support p := by
  ext x
  simp
  tauto

@[simp]
theorem support_X_mul {R : Type u} [Semiring R] (p : R[X]) :
    support (X * p) = (support p).map (addRightEmbedding 1) := by
  ext i
  simp only [mem_support_iff, ne_eq, Finset.mem_map, addRightEmbedding_apply]
  cases i
  · simp
  · simp only [coeff_X_mul]
    rw[Nat.succ_eq_add_one]
    simp

lemma addLeftEmbedding_zero : addLeftEmbedding 0 = Function.Embedding.refl _ := by
  ext
  rw[addLeftEmbedding_apply]
  simp

lemma addRightEmbedding_zero : addRightEmbedding 0 = Function.Embedding.refl _ := by
  ext
  rw[addRightEmbedding_apply]
  simp

theorem support_monomial_mul {R : Type u} [Semiring R] (p : R[X]) (n : ℕ) :
    support (X^n * p) = (support p).map (addRightEmbedding n) := by
  induction' n with n ih
  . simp only [Nat.zero_eq, pow_zero, one_mul]
    rw[addRightEmbedding_zero]
    simp
  . rw [@pow_succ]
    rw [@mul_assoc]
    rw [support_X_mul]
    rw [ih]
    rw [@Finset.map_map]
    congr

@[simp]
lemma L2normSq_smul_eq (g : ℂ[X]) (α: ℂ) : L2normSq ( α • g ) = ‖α‖^2  *  L2normSq g := by
  by_cases zero: α = 0
  . simp[zero]
  simp [L2normSq]
  rw [support_smul_eq α zero]
  rw [@Finset.mul_sum]
  simp [pow_two]
  simp [mul_mul_mul_comm]

@[simp]
lemma L2normSq_X_mul_eq (g : R[X]) :  L2normSq ( X * g ) =  L2normSq ( g ) := by
  simp [L2normSq]


lemma foobar (g : ℂ[X]) (α: ℂ) :
    L2normSq ( (X - Polynomial.C α ) *g ) = L2normSq (( (Polynomial.C (conj α) )*X - ↑ 1) * g) := by
  simp [L2normSq]
  rw?




-- lemma mahler_l2 (f : R[X]) :
--     mahlerMeasure f ≤ Real.sqrt (L2normSq f):= by
--   have (g : ℂ[X]) (α: ℂ) : L2normSq ( (X - Polynomial.C α ) *g ) = L2normSq (( (Polynomial.C (conj α) )*X - ↑ 1) * g)
--   . simp [L2normSq]
--     rw [@mul_eq_sum_sum]
--     simp
--     --rw [coeff_prod
--     --rw?
--   sorry
