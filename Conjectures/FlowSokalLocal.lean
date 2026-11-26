import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open Filter Topology

namespace CameronKayibi.Flow.Sokal

/-- Near a root of unity attained by a nonconstant analytic R, some large power of R
equals a prescribed nonvanishing analytic function T. The local logarithm of T is
chosen about T(y), so its argument can meet the principal branch cut. -/
theorem local_power_equal {R T : ℂ → ℂ} {y : ℂ} {U : Set ℂ} {d : ℕ}
    (hU : U ∈ 𝓝 y) (hR : AnalyticAt ℂ R y) (hT : AnalyticAt ℂ T y)
    (hnc : ¬ ∀ᶠ z in 𝓝 y, R z = R y) (hd : 0 < d) (hroot : R y ^ d = 1)
    (ht₀ : T y ≠ 0) (ht₁ : T y ≠ 1) :
    ∃ (p : ℕ) (z : ℂ), 2 ≤ p ∧ z ∈ U ∧ R z ^ p = T z := by
  have hω : R y ≠ 0 := by
    intro h
    rw [h, zero_pow hd.ne'] at hroot
    exact zero_ne_one hroot
  let A := fun z => Complex.log (R z / R y)
  let B := fun z => Complex.log (T z / T y) + Complex.log (T y)
  let Q := fun z => A z / B z
  have hA : AnalyticAt ℂ A y := (hR.div analyticAt_const hω).clog (by simp [hω])
  have hB : AnalyticAt ℂ B y :=
    ((hT.div analyticAt_const ht₀).clog (by simp [ht₀])).add analyticAt_const
  have hAy : A y = 0 := by simp [A,hω]
  have hBy : B y ≠ 0 := by
    simp only [B,div_self ht₀,Complex.log_one,zero_add]
    intro he
    have h := Complex.exp_log ht₀
    rw [he, Complex.exp_zero] at h
    exact ht₁ h.symm
  have hQ : AnalyticAt ℂ Q y := hA.div hB hBy
  have hQy : Q y = 0 := by simp [Q,hAy]
  let V := {z | z ∈ U ∧ R z ≠ 0 ∧ T z ≠ 0 ∧ B z ≠ 0}
  have hV : V ∈ 𝓝 y := by
    filter_upwards [hU,hR.continuousAt.eventually_ne hω,hT.continuousAt.eventually_ne ht₀,
      hB.continuousAt.eventually_ne hBy] with z hz hr ht hb
    exact ⟨hz,hr,ht,hb⟩
  have hopen : 𝓝 0 ≤ map Q (𝓝 y) := by
    rcases hQ.eventually_constant_or_nhds_le_map_nhds with he | he
    · exfalso
      apply hnc
      filter_upwards [he,hV] with z hz hv
      rw [hQy] at hz
      have haz : A z = 0 := (div_eq_zero_iff.mp hz).resolve_right hv.2.2.2
      have hex := Complex.exp_log (div_ne_zero hv.2.1 hω)
      change Complex.exp (A z) = R z / R y at hex
      rw [haz,Complex.exp_zero] at hex
      exact (div_eq_one_iff_eq hω).mp hex.symm
    · simpa only [hQy] using he
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hopen (image_mem_map hV))
  obtain ⟨n,hn⟩ := exists_nat_gt (1/ε+2)
  have hn₂ : 2 ≤ n := by
    have : (2:ℝ) < n := by linarith [one_div_pos.mpr hε]
    exact_mod_cast this.le
  let p := d*n
  have hpn : n ≤ p := by dsimp [p]; simpa using Nat.mul_le_mul_right n hd
  have hp₂ : 2 ≤ p := hn₂.trans hpn
  have hpR : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hpC : (p:ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hsmall : (1:ℝ)/p < ε := (one_div_lt hpR hε).mpr (by
    have : (n:ℝ) ≤ p := by exact_mod_cast hpn
    linarith)
  have hmem : (1/(p:ℂ)) ∈ Metric.ball 0 ε := by
    simpa [Metric.mem_ball, dist_eq_norm] using hsmall
  obtain ⟨z,hz,hqz⟩ := hball hmem
  have hab : (p:ℂ)*A z = B z := by
    change A z / B z = 1 / (p:ℂ) at hqz
    have hh := (div_eq_div_iff hz.2.2.2 hpC).mp hqz
    simpa [mul_comm] using hh
  have hpow : (R z / R y) ^ p = T z := by
    have hh := congrArg Complex.exp hab
    rw [Complex.exp_nat_mul, show A z = Complex.log (R z / R y) from rfl,
      Complex.exp_log (div_ne_zero hz.2.1 hω)] at hh
    simp only [B, Complex.exp_add, Complex.exp_log (div_ne_zero hz.2.2.1 ht₀),
      Complex.exp_log ht₀, div_mul_cancel₀ _ ht₀] at hh
    exact hh
  have hωp : R y ^ p = 1 := by simp [p,pow_mul,hroot]
  refine ⟨p,z,hp₂,hz.1,?_⟩
  simpa only [div_pow,hωp,div_one] using hpow

end CameronKayibi.Flow.Sokal
