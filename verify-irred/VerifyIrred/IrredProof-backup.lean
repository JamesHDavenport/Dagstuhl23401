import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt


open BigOperators Polynomial

noncomputable def toZ (p : Polynomial (ZMod n)) : Polynomial ℤ :=
  p.sum fun e a => (n/2 - ((n/2 : ℤ) - a).cast : ℤ) • X ^ e

theorem zassenhaus_but_not_really
    (p : ℕ) [Fact p.Prime]
    (f : Polynomial (ZMod p))
    (hgcd : ∀ d : ℕ, 2 * d ≤ f.degree → IsCoprime f (X^(p^d) - X))
    : Irreducible f := by
  sorry
theorem foo (f : Polynomial ℤ)
    (p : ℕ) (pp : Prime p) -- from CAS
    (n : ℕ) -- from CAS
    (fi : Fin m → Polynomial (ZMod (p^n))) -- from CAS
    (hpn : p ∣ p^n)
    (fi_irred : ∀ i, Irreducible ((fi i).map (ZMod.castHom hpn (ZMod p))))
    (f_eq_prod : f.map (Int.castRingHom (ZMod (p^n))) = ∏ i, fi i)
    (B : ℕ)
    (B_is_max : ∀ g, g ∣ f → ∀ i, |g.coeff i| ≤ B)
    (hn : 2 * B ≤ p ^ n)
    (qr : {S : Finset (Fin m) // S.card ≤ m/2 ∨ 2*S.card = m ∧ S.sort (·≤·) < Sᶜ.sort (·≤·)} →
      ℕ ⊕ (Polynomial ℤ × Polynomial ℤ)) -- from CAS, uses Collins1979
    (hqr : ∀ S,
      let f' := toZ (∏ i ∈ S.1, fi i)
      match qr S with
      | .inl k => |f'.coeff k| > B
      | .inr (q, r) => f = q * f' + r ∧ r.degree < f'.degree ∧ r ≠ 0)
    : Irreducible f := by
  sorry
