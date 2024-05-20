/-
Copyright (c) 2023 Alex J. Best, Edgar Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Edgar Costa, James H. Davenport
-/

import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
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
  have : f*g ≠ 0 := by simp [a1,a2]
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

-- # we deal in the square of the L2 norm
open Classical
lemma L2normSq_finsum (f : R[X]) :
    L2normSq f = ∑ᶠ (a : ℕ), ‖algebraMap R ℂ (f.coeff a)‖^2 := by
  have := finsum_eq_finset_sum_of_support_subset (fun a => ‖algebraMap R ℂ (f.coeff a)‖^2) (s := Polynomial.support f) ?_
  rw [this]
  rw [L2normSq]
  intro a ha
  simp
  simp at *
  contrapose! ha
  simp [ha]



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
  . rw [@pow_succ']
    rw [@mul_assoc]
    rw [support_X_mul]
    rw [ih]
    rw [@Finset.map_map]
    congr

@[simp]
lemma coeff_smul_pow_add_mul {R : Type u} [Semiring R] (a b : R) (p : R[X]) (k n : ℕ) (h : n ≤ k):
    Polynomial.coeff ((a • X^n + C b) * p) k = a * p.coeff (k - n) + b * p.coeff k := by
  simp [add_mul, coeff_add, coeff_C_mul, smul_mul_assoc, coeff_smul, smul_eq_mul, ge_iff_le, coeff_X_pow_mul', h]

@[simp]
lemma coeff_smul_pow_add_mul' {R : Type u} [Semiring R] (b : R) (p : R[X]) (k n : ℕ) (h : n ≤ k):
    Polynomial.coeff ((X^n + C b) * p) k = p.coeff (k - n) + b * p.coeff k := by
  simpa using coeff_smul_pow_add_mul 1 b p k n h

@[simp]
lemma coeff_smul_pow_neg_mul {R : Type u} [Ring R] (a b : R) (p : R[X]) (k n : ℕ) (h : n ≤ k):
    Polynomial.coeff ((a • X^n - C b) * p) k = a * p.coeff (k - n) - b * p.coeff k := by
  simpa[sub_eq_add_neg] using coeff_smul_pow_add_mul a (-b) p k n h

@[simp]
lemma coeff_smul_pow_neg_mul' {R : Type u} [Ring R] (b : R) (p : R[X]) (k n : ℕ) (h : n ≤ k):
    Polynomial.coeff ((X^n - C b) * p) k = p.coeff (k - n) - b * p.coeff k := by
  simpa using coeff_smul_pow_neg_mul 1 b p k n h

@[simp]
lemma coeff_smul_pow_neg_mul'' {R : Type u} [Ring R] (b : R) (p : R[X]) (k : ℕ) (h : 1 ≤ k):
    Polynomial.coeff ((X - C b) * p) k = p.coeff (k - 1) - b * p.coeff k := by
  simpa using coeff_smul_pow_neg_mul 1 b p k 1 h


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

-- JHD start here
open Classical
open BigOperators Finset Complex
lemma L2normSq_sum (f : R[X]) :
    L2normSq f = ∑ k in Ioc 0 f.natDegree, ‖algebraMap R ℂ (f.coeff k)‖^2 := by
  simp [sum.subset]

--lemma Mignotte1974L1a (p :  ℂ[X])  (α β: ℂ) : (L2normSq ((X+ Polynomial.C α)*p):ℂ) = ((‖α * p.coeff 0‖^2:ℝ):ℂ) + ∑ k in Ioc 0 p.natDegree, (( ((‖p.coeff (k-1)‖^2:ℝ):ℂ) +  α*p.coeff (k)*conj (p.coeff (k-1)) +conj ( α)*(p.coeff (k-1))*conj (p.coeff (k))+((‖α * p.coeff k‖^2:ℝ):ℂ)):ℂ) +(((‖p.coeff (p.natDegree)‖^2):ℝ):ℂ) := by
lemma Mignotte1974L1a (p :  ℂ[X])  (α β: ℂ) :
    (L2normSq ((X+ Polynomial.C α)*p):ℂ) = ∑ᶠ l : ℕ,
      ((‖p.coeff (l)‖^2:ℝ) +
        α*p.coeff (l+1) * conj (p.coeff l) +
        conj α * p.coeff l * conj (p.coeff (l+1)) +
        (‖α * p.coeff (l+1)‖^2:ℝ)).re := by
  simp only [L2normSq_finsum]
  congr; ext l
  refine (ofReal_re _).symm.trans ?_; congr
  simp [add_mul]
  cases l <;> simp [Polynomial.coeff_X_mul_zero, mul_pow, normSq_eq_conj_mul_self, ← normSq_eq_abs]

--  their code below here
lemma foobar_2  (g : ℂ[X]) (α β: ℂ) :
    L2normSq ( ( α • X - Polynomial.C β ) * g ) =  ‖β * g.coeff 0‖^2 + ∑ᶠ (a : ℕ) (ha : a ≠ 0), ‖α * g.coeff (a - 1) - β * g.coeff a‖^2  := by
  -- g = 1 LHS 1^2 + |alpha|^2
  -- RHS |alpha^2|
  simp [L2normSq_finsum]
  sorry
  /-
  rw [Finsum.sum_eq_sum_diff_singleton_add (i := 0)]
  simp [coeff_smul_pow_neg_mul'']
  --simp [L2normSq, L2normSq_smul_eq]
  --rw [coeff_smul_pow_add_mul]
  -/

lemma foobar_1  (g : ℂ[X]) (α β: ℂ) :
    L2normSq ( ( α • X - Polynomial.C β ) * g ) =  ∑ᶠ (a : ℕ) , ‖α * (if a ≠ 0 then g.coeff (a - 1) else 0) - β * g.coeff a‖^2  := by
  -- g = 1 LHS 1^2 + |alpha|^2
  -- RHS |alpha^2|
  simp [L2normSq_finsum]
  sorry
  /-
  rw [Finsum.sum_eq_sum_diff_singleton_add (i := 0)]
  simp [coeff_smul_pow_neg_mul'']
  --simp [L2normSq, L2normSq_smul_eq]
  --rw [coeff_smul_pow_add_mul]
  -/
lemma finsum_if_mul (f : ℕ → R) (α : R) (hf : Set.Finite f.support ) :
  ∑ᶠ (i : ℕ), (if i = 0 then 0 else f i * α) = α * (∑ᶠ (i : ℕ), (if i = 0 then 0 else f i)) := by
  rw [mul_comm]
  rw [finsum_mul]
  simp only [ite_mul, zero_mul]
  apply Set.Finite.subset hf
  simp

lemma finsum_succ (f : ℕ → R) (hf : Set.Finite f.support ) (hg : f 0 = 0) :
  ∑ᶠ (i : ℕ), f i = ∑ᶠ (i : ℕ), f (i + 1) := by
  simp_rw [← Nat.succ_eq_add_one]
  rw [← @finsum_mem_univ]
  rw [← Nat.zero_union_range_succ]
  rw [finsum_mem_union']
  simp only [Set.mem_singleton_iff, finsum_cond_eq_left, Set.mem_setOf_eq]
  rw [hg]
  simp only [zero_add]
  rw [finsum_mem_range]
  apply Nat.succ_injective
  simp only [Nat.range_succ, Set.disjoint_singleton_left]
  apply Set.Finite.subset hf
  simp only [Set.inter_subset_right]
  apply Set.Finite.inter_of_right hf

open Classical
lemma finsum_shift (g : R[X]) (f : R -> R) (h: f 0 = 0):
  ∑ᶠ (i : ℕ), (if i = 0 then 0 else f (g.coeff (i - 1))) = ∑ᶠ (i : ℕ), f (g.coeff i) := by
  rw [finsum_succ]
  simp only [add_eq_zero, and_false, ite_false]
  simp_rw [← Nat.succ_eq_add_one, ← Nat.pred_eq_sub_one, Nat.pred_succ]
  rw [← h]
  have h1: (fun i => if i = 0 then f 0 else f (coeff g (i - 1))) = fun i => f (if i = 0 then 0 else coeff g (i - 1)) := by
    congr
    ext i
    rw [← @apply_ite]
  rw [h1]
  have h2: Function.support (fun i => if i = 0 then 0 else coeff g (i - 1)) ⊆ (g.coeff ∘ Nat.pred).support := by
    intro i
    -- rw [Function.support]
    rw [@Function.mem_support, @Function.mem_support]
    simp only [ge_iff_le, ne_eq, ite_eq_left_iff, not_forall, exists_prop, Function.comp_apply, and_imp]
    tauto
  have h3: Function.support ( fun i => f (if i = 0 then 0 else coeff g (i - 1) ) ) ⊆ Function.support (fun i => if i = 0 then 0 else coeff g (i - 1))  := by
    rw [← h1, h]
    intro i
    rw [@Function.mem_support, @Function.mem_support]
    contrapose
    simp only [ge_iff_le, ne_eq, ite_eq_left_iff, not_forall, exists_prop, not_and, not_not]
    cases i
    · simp
    . simp only [Nat.succ_ne_zero, not_false_eq_true, ge_iff_le, Nat.succ_sub_succ_eq_sub, nonpos_iff_eq_zero,
      tsub_zero, forall_true_left]
      aesop
    done
  have h4: Function.support ( fun i => f (if i = 0 then 0 else coeff g (i - 1) ) )  ⊆ (g.coeff ∘ Nat.pred).support := by
    tauto











#exit









  -- rw [ite]





  -- rw [finsum_eq_of_bijective]
#exit

open Complex
lemma foobar (g : ℂ[X]) (α: ℂ) :
    L2normSq ( (X - Polynomial.C α ) *g ) = L2normSq (( (conj α) • X - Polynomial.C 1) * g) := by
  have := foobar_1 (β := α) (α := 1)
  simp only [one_smul, ne_eq, ge_iff_le, ite_not, mul_ite, mul_zero, one_mul, norm_eq_abs] at this
  rw[this]
  rw [map_one]
  have := foobar_1 (β := 1) (α := conj α)
  simp only [map_one, ne_eq, ge_iff_le, ite_not, mul_ite, mul_zero, one_mul, norm_eq_abs] at this
  rw[this]
  simp_rw [Complex.sq_abs]
  simp_rw [Complex.normSq_sub]
  simp_rw [map_mul]
  simp_rw [← mul_assoc]
  simp_rw [mul_comm _ (coeff _ _)]
  rw [finsum_sub_distrib, finsum_sub_distrib]
  simp only [ge_iff_le, ite_mul, zero_mul, sub_left_inj]
  rw [finsum_add_distrib, finsum_add_distrib]
  simp_rw [apply_ite]
  simp only [_root_.map_zero, ge_iff_le, map_mul, normSq_conj]
  sorry


  -- rw?
  -- [@mul_assoc]





#exit

-- lemma mahler_l2 (f : R[X]) :
--     mahlerMeasure f ≤ Real.sqrt (L2normSq f):= by
--   have (g : ℂ[X]) (α: ℂ) : L2normSq ( (X - Polynomial.C α ) *g ) = L2normSq (( (Polynomial.C (conj α) )*X - ↑ 1) * g)
--   . simp [L2normSq]
--     rw [@mul_eq_sum_sum]
--     simp
--     --rw [coeff_prod
--     --rw?
--   sorry
