import Conjectures.FlowCopies
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.FieldSimp

namespace CameronKayibi.FlowCopies
open FlowGraph Polynomial

/-- Ordinary d-fold replication followed by permutation of N identical blocks. -/
noncomputable def orbitPolynomial (P : Polynomial ℂ) (d N : ℕ) : Polynomial ℂ :=
  C ((N.factorial : ℂ)⁻¹) * ∏ i ∈ Finset.range N, (P^d + C (i:ℂ))

@[simp] theorem eval_orbitPolynomial (P : Polynomial ℂ) (d N : ℕ) (z : ℂ) :
    (orbitPolynomial P d N).eval z =
      (N.factorial:ℂ)⁻¹ * ∏ i ∈ Finset.range N, (P.eval z ^ d + i) := by
  simp [orbitPolynomial, eval_prod]

/-- The polynomial gives the actual orbit count for any finite abelian group at whose
cardinality the chosen base polynomial counts flows. -/
theorem eval_counts {V E : Type} [Fintype E] [DecidableEq V] (H : OrientedGraph V E)
    (A : Type) [AddCommGroup A] [Fintype A] (P : Polynomial ℂ) (d N : ℕ)
    (h : P.eval (Fintype.card A : ℂ) = Nat.card (Flow H A)) :
    (orbitPolynomial P d N).eval (Fintype.card A : ℂ) =
      Nat.card (Orbits (copies H d) A N) := by
  have hc := congrArg (Nat.cast : ℕ → ℂ) (factorial_mul_orbit_count (copies H d) A N)
  rw [ordinary_count H A d] at hc
  push_cast at hc
  rw [eval_orbitPolynomial, h, ← hc]
  have hf : (N.factorial : ℂ) ≠ 0 := by exact_mod_cast N.factorial_ne_zero
  field_simp

/-- Each negative integer from 0 to −(N−1) in the image of the power gives a root. -/
theorem root_of_value (P : Polynomial ℂ) (d N : ℕ) {z : ℂ} {j : ℕ}
    (hj : j < N) (h : P.eval z ^ d = -(j:ℂ)) :
    (orbitPolynomial P d N).eval z = 0 := by
  rw [eval_orbitPolynomial]
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hj)
  simp [h]

end CameronKayibi.FlowCopies
