import Conjectures.FlowComplexTargets
import Mathlib.Tactic.FieldSimp

namespace CameronKayibi.Flow.Sokal
open Filter Topology

noncomputable def ratio (s : ℕ) (z : ℂ) := ((1-z)^s-(1-z))/((1-z)^s-1)

private theorem squared_difference (x : ℂ) (a : ℝ) :
    ‖(a:ℂ)-x‖^2 - ‖(a:ℂ)-1‖^2 = ‖x‖^2-1 + 2*a*(1-x.re) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]
  ring

private theorem select {U : Set ℂ} (hU : IsOpen U) {x : ℂ} (hx : x ∈ U)
    (h_ext : ∀ w ∈ U, 1 < ‖w‖) : ∃ u ∈ U, u.re ≠ 1 ∧ u ∈ PowerTargets := by
  obtain ⟨x',hx',h're⟩ : ∃ x' ∈ U, x'.re ≠ 1 := by
    by_cases he : x.re = 1
    · obtain ⟨δ,hδ,hb⟩ := Metric.isOpen_iff.mp hU x hx
      refine ⟨x+(δ/2:ℝ),hb ?_,?_⟩
      · rw [Metric.mem_ball,dist_eq_norm]
        simp [Complex.norm_real, abs_of_pos hδ]
        linarith
      · simp [he, hδ.ne']
    · exact ⟨x,hx,he⟩
  let W := U ∩ {w : ℂ | w.re ≠ 1}
  have hW : IsOpen W := hU.inter (isOpen_ne_fun Complex.continuous_re continuous_const)
  obtain ⟨u,⟨hu,hr⟩,hp⟩ := mem_closure_iff.mp (mem_closure_powerTargets (h_ext x' hx')) W hW ⟨hx',h're⟩
  exact ⟨u,hu,hr,hp⟩

private theorem half_turn_power (s : ℕ) (hs : 0 < s) :
    Complex.exp (↑(Real.pi/(s:ℝ)) * Complex.I)^s = -1 := by
  rw [← Complex.exp_nat_mul, ← mul_assoc, Complex.ofReal_div]
  have hn : (s:ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  simp only [Complex.ofReal_natCast]
  rw [show (s:ℂ)*((Real.pi:ℂ)/s) = (Real.pi:ℂ) by field_simp, Complex.exp_pi_mul_I]

private theorem compare {s : ℕ} (hs : 0 < s) {x : ℂ} (hx : 1 < ‖x‖)
    {a : ℝ} (ha : x^s = (a:ℂ)) :
    (‖ratio s (1-x)‖ < 1 ↔ ‖x‖^2-1 + 2*a*(1-x.re) < 0) ∧
    (1 < ‖ratio s (1-x)‖ ↔ 0 < ‖x‖^2-1 + 2*a*(1-x.re)) := by
  have hn : a ≠ 1 := by
    intro h
    have hu := congrArg norm ha
    rw [h] at hu
    simp only [norm_pow,Complex.ofReal_one,norm_one] at hu
    exact (one_lt_pow₀ hx hs.ne').ne' hu
  have hd : 0 < ‖(a:ℂ)-1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (by exact_mod_cast hn))
  rw [ratio, sub_sub_cancel, ha, norm_div, div_lt_one hd, one_lt_div hd, ← squared_difference]
  have hn₀ := norm_nonneg ((a:ℂ)-x)
  constructor <;> constructor <;> intro h <;> nlinarith

/-- In each exterior ball, the ratio for a single common path length has
values on both sides of the unit circle. -/
theorem sign_crossing {z : ℂ} (h : 1 < ‖1-z‖) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : ℕ, 2 ≤ s ∧ ∃ u ∈ Metric.ball z ε, ∃ v ∈ Metric.ball z ε,
      ‖ratio s u‖ < 1 ∧ 1 < ‖ratio s v‖ := by
  let U : Set ℂ := {x : ℂ | 1-x ∈ Metric.ball z ε} ∩ {x : ℂ | 1<‖x‖}
  have hU : IsOpen U := (Metric.isOpen_ball.preimage (continuous_const.sub continuous_id)).inter
    (isOpen_lt continuous_const continuous_norm)
  have hz : 1-z ∈ U := ⟨by simpa using Metric.mem_ball_self (x:=z) hε,h⟩
  obtain ⟨u,hu,hre,d,j,hd,hj⟩ := select hU hz (fun _ h' => h'.2)
  let s (n : ℕ) := 2*d*(n+1)
  let a (n : ℕ) := ((j:ℝ)^2)^(n+1)
  let v (n : ℕ) := u*Complex.exp (↑(Real.pi / (s n : ℝ))*Complex.I)
  have hs n : 2 ≤ s n := by dsimp [s]; nlinarith
  have hsn : Tendsto s atTop atTop := tendsto_atTop_mono (fun n => by dsimp [s]; nlinarith) tendsto_id
  have hp n : u^(s n) = (a n:ℂ) := by
    dsimp [s,a]; rw [Nat.mul_comm 2 d, pow_mul, pow_mul, hj, neg_sq]; norm_cast
  have hm n : (v n)^(s n) = (-a n:ℝ) := by
    dsimp only [v]
    rw [mul_pow,half_turn_power _ (by have := hs n; omega),hp,mul_neg_one,Complex.ofReal_neg]
  have hn n : ‖v n‖ = ‖u‖ := by simp only [v,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one]
  have ha n : a n = ‖u‖^(s n) := by
    have ha₀ : 0 ≤ a n := pow_nonneg (sq_nonneg _) _
    simpa only [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ha₀] using (congrArg norm (hp n)).symm
  have haTop : Tendsto a atTop atTop := by
    simpa only [funext ha] using (tendsto_pow_atTop_atTop_of_one_lt hu.2).comp hsn
  have hθ := (tendsto_const_div_atTop_nhds_zero_nat Real.pi).comp hsn
  have hvc : Tendsto v atTop (𝓝 u) := by
    have hc := Complex.continuous_exp.continuousAt (x := (0:ℂ)*Complex.I)
    have ht := Complex.continuous_ofReal.continuousAt.tendsto.comp hθ
    simpa [v,Function.comp_def] using ((hc.tendsto.comp (ht.mul_const Complex.I)).const_mul u)
  have hbase : Tendsto (fun n => (‖u‖^2-1)/a n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop haTop
  let b := 2*(1-u.re)
  have hb : b ≠ 0 := mul_ne_zero (by norm_num) (sub_ne_zero.mpr hre.symm)
  have hp' : Tendsto (fun n => (‖u‖^2-1)/a n + b) atTop (𝓝 b) := by simpa using hbase.add_const b
  have hv' : Tendsto (fun n => (‖u‖^2-1)/a n - 2*(1-(v n).re)) atTop (𝓝 (-b)) := by
    have hre' := Complex.continuous_re.continuousAt.tendsto.comp hvc
    simpa [b,Function.comp_def] using hbase.sub ((tendsto_const_nhds.sub hre').const_mul (2:ℝ))
  have hin : ∀ᶠ n in atTop, v n ∈ U := hvc.eventually (hU.mem_nhds hu)
  have hprod n : 0 < a n := by rw [ha]; exact pow_pos (zero_lt_one.trans hu.2) _
  have hpos n : (‖u‖^2-1)/a n+b = (‖u‖^2-1+2*a n*(1-u.re))/a n := by
    dsimp [b]; field_simp [(hprod n).ne']; ring
  have hneg n : (‖u‖^2-1)/a n-2*(1-(v n).re) = (‖v n‖^2-1+2*(-a n)*(1-(v n).re))/a n := by
    rw [hn]; field_simp [(hprod n).ne']; ring
  rcases lt_or_gt_of_ne hb with hb | hb
  · obtain ⟨n,huv,hl,hr⟩ := (hin.and ((hp'.eventually_lt_const hb).and
      (hv'.eventually_const_lt (neg_pos.mpr hb)))).exists
    rw [hpos, div_lt_iff₀ (hprod n), zero_mul] at hl
    rw [hneg, lt_div_iff₀ (hprod n), zero_mul] at hr
    exact ⟨s n,hs n,1-u,hu.1,1-v n,huv.1,
      (compare (by have := hs n; omega) hu.2 (hp n)).1.mpr hl,
      (compare (by have := hs n; omega) huv.2 (hm n)).2.mpr hr⟩
  · obtain ⟨n,huv,hr,hl⟩ := (hin.and ((hp'.eventually_const_lt hb).and
      (hv'.eventually_lt_const (neg_neg_of_pos hb)))).exists
    rw [hpos, lt_div_iff₀ (hprod n), zero_mul] at hr
    rw [hneg, div_lt_iff₀ (hprod n), zero_mul] at hl
    exact ⟨s n,hs n,1-v n,huv.1,1-u,hu.1,
      (compare (by have := hs n; omega) huv.2 (hm n)).1.mpr hl,
      (compare (by have := hs n; omega) hu.2 (hp n)).2.mpr hr⟩

end CameronKayibi.Flow.Sokal
