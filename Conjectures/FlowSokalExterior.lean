import Conjectures.FlowSokalLocal
import Conjectures.FlowSokalCrossing
import Conjectures.FlowSwapDisk

open Filter Topology

namespace CameronKayibi.Flow.Sokal

/-- If an analytic ratio passes through the unit circle on a connected open set,
one of its powers equals a prescribed analytic target somewhere in the set. -/
theorem power_equal_on_crossing {R T : ℂ → ℂ} {D : Set ℂ} (hopen : IsOpen D)
    (hpre : IsPreconnected D) (hr : AnalyticOnNhd ℂ R D) (ht : AnalyticOnNhd ℂ T D)
    (ht₀ : ∀ x ∈ D, T x ≠ 0) (ht₁ : ∀ x ∈ D, T x ≠ 1)
    {a b : ℂ} (ha : a ∈ D) (hb : b ∈ D) (hal : ‖R a‖ < 1) (hbl : 1 < ‖R b‖) :
    ∃ (p : ℕ) (z : ℂ), 2 ≤ p ∧ z ∈ D ∧ R z ^ p = T z := by
  have hnc (c : ℂ) : ¬ ∀ v ∈ D, R v = c := by
    intro he
    exact (hal.trans hbl).ne (congrArg norm ((he a ha).trans (he b hb).symm))
  obtain ⟨w,hw,hunit⟩ := hpre.intermediate_value ha hb (continuous_norm.comp_continuousOn hr.continuousOn)
    (show (1:ℝ) ∈ Set.Icc ‖R a‖ ‖R b‖ from ⟨hal.le,hbl.le⟩)
  have hIm : IsOpen (R '' D) := by
    rcases hr.is_constant_or_isOpen hpre with ⟨c,h⟩ | h
    · exact (hnc c h).elim
    · exact h D Set.Subset.rfl hopen
  obtain ⟨ω,⟨y,hy,hRy⟩,d,hd,hωd⟩ := SwapDisk.root_of_neg_one_in_open hIm ⟨w,hw,rfl⟩ hunit
  have hyn : ¬ ∀ᶠ v in 𝓝 y, R v = R y := by
    intro he
    apply hnc (R y)
    exact hr.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hpre hy he
  have hω : R y ^ (d*2) = 1 := by rw [hRy,pow_mul,hωd]; norm_num
  exact local_power_equal (hopen.mem_nhds hy) (hr y hy) (ht y hy) hyn (by omega) hω
    (ht₀ y hy) (ht₁ y hy)

/-- Every disk in the exterior contains a zero of a theta numerator with at least two
branches, each of length at least two. -/
theorem exists_theta_root {z : ℂ} (hz : 1 < ‖1-z‖) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s p : ℕ) (w : ℂ), 2 ≤ s ∧ 2 ≤ p ∧ dist w z < ε ∧ w ≠ 0 ∧
      ((1-w)^s-(1-w))^p + (w-1)*((1-w)^s-1)^p = 0 := by
  let δ := min ε ((‖1-z‖-1)/2)
  have hδ : 0 < δ := lt_min hε (by linarith)
  let D := Metric.ball z δ
  have hD (w : ℂ) (hw : w ∈ D) : 1 < ‖1-w‖ := by
    have ht := dist_triangle (1:ℂ) w z
    change dist w z < δ at hw
    have hδ' : δ ≤ (‖1-z‖-1)/2 := min_le_right _ _
    rw [dist_eq_norm (1:ℂ) z, dist_eq_norm (1:ℂ) w] at ht
    linarith only [ht,hw,hδ',hz]
  obtain ⟨s,hs,a,ha,b,hb,hl,hh⟩ := sign_crossing hz hδ
  have hden (w : ℂ) (hw : w ∈ D) : (1-w)^s-1 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have hbig : 1 < ‖1-w‖^s := one_lt_pow₀ (hD w hw) (by omega)
    rw [← norm_pow,he,norm_one] at hbig
    exact (lt_irrefl _ hbig)
  have hr : AnalyticOnNhd ℂ (ratio s) D := by
    intro w hw
    unfold ratio
    fun_prop (disch := exact hden w hw)
  have ht : AnalyticOnNhd ℂ (fun w : ℂ => 1-w) D := by intro w _; fun_prop
  have ht₀ (w : ℂ) (hw : w ∈ D) : 1-w ≠ 0 := by
    have := hD w hw
    intro he; rw [he,norm_zero] at this; linarith
  have ht₁ (w : ℂ) (hw : w ∈ D) : 1-w ≠ 1 := by
    have := hD w hw
    intro he; rw [he,norm_one] at this; linarith
  obtain ⟨p,w,hp,hw,hpw⟩ := power_equal_on_crossing Metric.isOpen_ball
    (convex_ball z δ).isPreconnected hr ht ht₀ ht₁ ha hb hl hh
  have hw₀ : w ≠ 0 := by intro he; exact ht₁ w hw (by rw [he,sub_zero])
  have hpoly : ((1-w)^s-(1-w))^p = (1-w)*((1-w)^s-1)^p := by
    apply (div_eq_iff (pow_ne_zero _ (hden w hw))).mp
    simpa only [ratio,div_pow] using hpw
  refine ⟨s,p,w,hs,hp,lt_of_lt_of_le hw (min_le_left _ _),hw₀,?_⟩
  rw [hpoly]
  ring

end CameronKayibi.Flow.Sokal
