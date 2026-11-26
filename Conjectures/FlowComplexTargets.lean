import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace CameronKayibi.Flow

/-- Positive-degree roots of nonpositive integers. -/
def PowerTargets : Set ℂ := {w | ∃ d j : ℕ, 0 < d ∧ w^d = -(j : ℂ)}

/-- To the right of one, amplification by the nth power increases gaps by at least n. -/
private theorem power_gap {r δ : ℝ} (hr : 1 ≤ r) (hδ : 0 ≤ δ) (n : ℕ) :
    (n:ℝ)*δ ≤ (r+δ)^n-r^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hr0 : 0 ≤ r := by linarith
    have hmono := pow_le_pow_left₀ hr0 (show r ≤ r+δ by linarith) n
    have h1 : 1 ≤ r^n := one_le_pow₀ hr
    have h2 := mul_nonneg (sub_nonneg.mpr hmono) (show 0 ≤ r+δ-1 by linarith)
    have h3 := mul_nonneg (sub_nonneg.mpr h1) hδ
    rw [Nat.cast_succ, pow_succ, pow_succ]
    nlinarith only [ih,h2,h3]

private noncomputable def polar (t : ℝ × ℝ) : ℂ := (t.1:ℂ)*Complex.exp ((t.2:ℂ)*Complex.I)

private theorem polar_cont : Continuous polar := by unfold polar; fun_prop

/-- Every point outside the closed unit disk is approximated by complex numbers
whose positive integral powers are negative integers. -/
theorem mem_closure_powerTargets {z : ℂ} (h : 1 < ‖z‖) : z ∈ closure PowerTargets := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let r := ‖z‖
  let θ := Complex.arg z
  have hr : 1 < r := h
  obtain ⟨δ,hδ,hball⟩ := Metric.continuousAt_iff.mp
    (polar_cont.continuousAt (x := (r,θ))) ε hε
  obtain ⟨d,hd⟩ := exists_nat_gt ((Real.pi+2)/δ)
  have hdδ := (div_lt_iff₀ hδ).mp hd
  have hπ := Real.pi_pos
  have hdpos : (0 : ℝ) < d := (div_pos (by linarith) hδ).trans hd
  have hdN : 0 < d := by exact_mod_cast hdpos
  let j := ⌊r^d⌋₊+1
  have hjlo : r^d < (j : ℝ) := by simpa [j] using Nat.lt_floor_add_one (r^d)
  have hjhi : (j : ℝ) < (r+δ)^d := by
    have hj := Nat.floor_le (pow_nonneg (by linarith : 0 ≤ r) d)
    have hg := power_gap hr.le hδ.le d
    change (↑(⌊r^d⌋₊+1) : ℝ) < _
    rw [Nat.cast_add,Nat.cast_one]
    linarith only [hj,hg,hdδ,hπ]
  obtain ⟨ρ,hρ,hρpow⟩ := intermediate_value_Ioo (show r ≤ r+δ by linarith)
    (continuous_pow d).continuousOn (show (j : ℝ) ∈ Set.Ioo (r^d) ((r+δ)^d) from ⟨hjlo,hjhi⟩)
  let k := ⌊(θ*d)/(2*Real.pi)⌋
  let α := ((k:ℝ)*(2*Real.pi)+Real.pi)/(d:ℝ)
  have h2π : 0 < 2*Real.pi := by linarith
  have hkl : (k:ℝ)*(2*Real.pi) ≤ θ*d := (le_div_iff₀ h2π).mp (Int.floor_le _)
  have hku : θ*d < ((k:ℝ)+1)*(2*Real.pi) := (div_lt_iff₀ h2π).mp (Int.lt_floor_add_one _)
  have hαlo : θ-δ < α := (lt_div_iff₀ hdpos).mpr (by nlinarith only [hdδ,hku])
  have hαhi : α < θ+δ := (div_lt_iff₀ hdpos).mpr (by nlinarith only [hdδ,hkl])
  have hangle : (d:ℝ)*α = (k:ℝ)*(2*Real.pi)+Real.pi := by
    dsimp [α]; field_simp
  have hangleC : (d:ℂ)*(α:ℂ) = (k:ℂ)*(2*(Real.pi:ℂ))+Real.pi := by exact_mod_cast hangle
  have hneg : Complex.exp ((α:ℂ)*Complex.I)^d = -1 := by
    rw [← Complex.exp_nat_mul, ← mul_assoc, hangleC, add_mul, mul_assoc, Complex.exp_add_pi_mul_I,
      Complex.exp_int_mul_two_pi_mul_I]
  have hw : polar (ρ,α) ∈ PowerTargets := by
    refine ⟨d,j,hdN,?_⟩
    change ((ρ:ℂ)*Complex.exp ((α:ℂ)*Complex.I))^d = _
    rw [mul_pow,hneg,mul_neg_one]
    exact_mod_cast congrArg Neg.neg hρpow
  have hdist : dist (ρ,α) (r,θ) < δ := by
    rw [Prod.dist_eq]
    apply max_lt
    · rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hρ.1.le)]
      linarith only [hρ.2]
    · rw [Real.dist_eq,abs_lt]
      exact ⟨by linarith only [hαlo],by linarith only [hαhi]⟩
  refine ⟨polar (ρ,α),hw,?_⟩
  have hz : polar (r,θ) = z := Complex.norm_mul_exp_arg_mul_I z
  rw [dist_comm, ← hz]
  exact hball hdist

end CameronKayibi.Flow
