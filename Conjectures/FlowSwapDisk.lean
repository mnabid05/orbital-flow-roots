import Conjectures.CameronKayibi
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Normed.Module.Convex

namespace CameronKayibi.Flow.SwapDisk

/-- Move away from the real axis while staying on the same vertical line. -/
private noncomputable def shift (z : ℂ) (t : ℝ) : ℂ := ⟨z.re, if 0 ≤ z.im then z.im+t else z.im-t⟩

private theorem shift_dist (z : ℂ) {t : ℝ} (ht : 0 ≤ t) : dist (shift z t) z = t := by
  rw [dist_eq_norm]
  have hs : ‖shift z t-z‖^2 = t^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    by_cases h : 0 ≤ z.im <;> simp [shift,h] <;> ring
  nlinarith [norm_nonneg (shift z t-z)]

private theorem shift_grows (z : ℂ) (a : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖z-(a:ℂ)‖ < ‖shift z t-(a:ℂ)‖ := by
  have hs : ‖z-(a:ℂ)‖^2 < ‖shift z t-(a:ℂ)‖^2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
      Complex.ofReal_re,Complex.ofReal_im,sub_zero]
    by_cases h : 0 ≤ z.im
    · simp [shift,h]
      nlinarith [mul_nonneg h ht.le, sq_pos_of_pos ht]
    · simp [shift,h]
      nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) ht.le, sq_pos_of_pos ht]
  nlinarith [norm_nonneg (z-(a:ℂ)),norm_nonneg (shift z t-(a:ℂ))]

theorem root_of_neg_one_in_open {U : Set ℂ} (hU : IsOpen U)
    {w : ℂ} (hw : w ∈ U) (hn : ‖w‖ = 1) :
    ∃ ζ ∈ U, ∃ d : ℕ, 0 < d ∧ ζ^d = -1 := by
  let θ := Complex.arg w
  let circle := fun t : ℝ => Complex.exp ((t:ℂ)*Complex.I)
  have hwθ : circle θ = w := by simpa [circle,θ,hn] using Complex.norm_mul_exp_arg_mul_I w
  have hcont : Continuous circle := by unfold circle; fun_prop
  obtain ⟨δ,hδ,hδU⟩ := Metric.isOpen_iff.mp (hU.preimage hcont) θ (show circle θ ∈ U by rwa [hwθ])
  obtain ⟨d,hd⟩ := exists_nat_gt (Real.pi/δ)
  have hdδ := (div_lt_iff₀ hδ).mp hd
  have hπ := Real.pi_pos
  have hp : (0:ℝ)<d := (div_pos hπ hδ).trans hd
  let k := ⌊(θ*d)/(2*Real.pi)⌋
  let α := ((k:ℝ)*(2*Real.pi)+Real.pi)/(d:ℝ)
  have h2π : 0 < 2*Real.pi := by linarith
  have hkl : (k:ℝ)*(2*Real.pi) ≤ θ*d := (le_div_iff₀ h2π).mp (Int.floor_le _)
  have hku : θ*d < ((k:ℝ)+1)*(2*Real.pi) := (div_lt_iff₀ h2π).mp (Int.lt_floor_add_one _)
  have hlo : θ-δ < α := (lt_div_iff₀ hp).mpr (by nlinarith only [hdδ,hku])
  have hhi : α < θ+δ := (div_lt_iff₀ hp).mpr (by nlinarith only [hdδ,hkl])
  have hα : (d:ℝ)*α = (k:ℝ)*(2*Real.pi)+Real.pi := by dsimp [α]; field_simp
  have hαc : (d:ℂ)*(α:ℂ) = (k:ℂ)*(2*(Real.pi:ℂ))+Real.pi := by exact_mod_cast hα
  refine ⟨circle α,hδU ?_,d,by exact_mod_cast hp,?_⟩
  · change dist α θ < δ
    rw [Real.dist_eq,abs_lt]
    exact ⟨by linarith,by linarith⟩
  · dsimp [circle]
    rw [← Complex.exp_nat_mul, ← mul_assoc, hαc, add_mul, mul_assoc,
      Complex.exp_add_pi_mul_I, Complex.exp_int_mul_two_pi_mul_I]

/-- The ordinary polynomial is realized by the ladder together with extra loops. -/
def ordinary (m s : ℕ) (z : ℂ) : ℂ := (z-1)*(z-2)*(z-1)^m*(z-3)^s

/-- Roots witnessed by a single copy-swapping involution. -/
def Roots : Set ℂ := {z | ∃ m s d : ℕ, 0 < d ∧ ordinary m s z ^ d = -1}

private noncomputable def amp (w : ℂ) : ℝ := ‖w-1‖*‖w-2‖
private noncomputable def growth (m k : ℕ) (w : ℂ) : ℝ := ‖w-1‖^m * ‖w-3‖^k

private lemma norm_ordinary (m k n : ℕ) (z : ℂ) :
    ‖ordinary (m*n) (k*n) z‖ = amp z*(growth m k z)^n := by
  simp [ordinary,amp,growth,norm_mul,norm_pow,pow_mul,mul_pow,mul_assoc]

private lemma amplify {a b c d : ℝ} (ha : 0 ≤ a) (ha' : a < 1) (hb : 1 < b) (hd : 0 < d) :
    ∃ t : ℕ, c*a^t < 1 ∧ 1 < d*b^t := by
  have hleft := (tendsto_pow_atTop_nhds_zero_of_lt_one ha ha').const_mul c
  rw [mul_zero] at hleft
  have hright := Filter.Tendsto.atTop_mul_pos hd (tendsto_pow_atTop_atTop_of_one_lt hb)
    (tendsto_const_nhds (x:=d))
  have hl := hleft.eventually_lt_const (show (0:ℝ)<1 by norm_num)
  have hr := (Filter.tendsto_atTop.mp hright 2)
  obtain ⟨t,ht₁,ht₂⟩ := (hl.and hr).exists
  exact ⟨t,ht₁,by linarith [mul_comm d (b^t)]⟩

/-- Every open disk meeting the punctured unit disk about 1 contains a root
realized by a single copy swap on a replicated ladder with extra loops. -/
theorem mem_closure {z : ℂ} (h₁ : 0 < ‖z-1‖) (hz : ‖z-1‖ < 1) : z ∈ closure Roots := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let δ := min ε (1-‖z-1‖) / 2
  have hδ : 0 < δ := half_pos (lt_min hε (by linarith))
  have hδε : δ < ε := by dsimp [δ]; linarith [min_le_left ε (1-‖z-1‖)]
  have hδz : δ < 1-‖z-1‖ := by dsimp [δ]; linarith [min_le_right ε (1-‖z-1‖)]
  let v := shift z δ
  have hvdist : dist v z = δ := shift_dist z hδ.le
  have hv : ‖v-1‖ < 1 := by
    have h := dist_triangle v z (1:ℂ)
    rw [hvdist,dist_eq_norm,dist_eq_norm] at h
    linarith
  have h₃ : 1 < ‖z-3‖ := by
    have h := dist_triangle (1:ℂ) z 3
    rw [dist_comm 1 z,dist_eq_norm,dist_eq_norm,dist_eq_norm] at h
    norm_num at h
    linarith
  have hstep₁ := shift_grows z 1 hδ
  have hstep₃ := shift_grows z 3 hδ
  push_cast at hstep₁ hstep₃
  obtain ⟨m,k,hhu,hlo⟩ := separate h₁ hstep₁.le hv h₃ hstep₃
  have hfv₁ := h₁.trans hstep₁
  have hfv₂ : (0:ℝ) < ‖v-2‖ := by
    rw [norm_pos_iff,sub_ne_zero]; intro he; rw [he] at hv; norm_num at hv
  obtain ⟨n,hnz,hnv⟩ := amplify (show 0 ≤ growth m k z from
    mul_nonneg (pow_nonneg (norm_nonneg _) _) (pow_nonneg (norm_nonneg _) _))
    hlo hhu (show 0 < amp v from mul_pos hfv₁ hfv₂) (c:=amp z)
  let P := ordinary (m*n) (k*n)
  change amp z*(growth m k z)^n < 1 at hnz
  change 1 < amp v*(growth m k v)^n at hnv
  rw [← norm_ordinary] at hnz hnv
  have ha : AnalyticOnNhd ℂ P Set.univ := by
    intro x _
    unfold P ordinary
    fun_prop
  let D := Metric.ball z ε
  have hD : IsOpen D := Metric.isOpen_ball
  have hzD : z ∈ D := Metric.mem_ball_self hε
  have hvD : v ∈ D := hvdist.trans_lt hδε
  have hc : Continuous (fun w => ‖P w‖) := by unfold P ordinary; fun_prop
  obtain ⟨w,hw,hw₁⟩ := (convex_ball z ε).isPreconnected.intermediate_value hzD hvD
    hc.continuousOn (show (1:ℝ) ∈ Set.Icc ‖P z‖ ‖P v‖ from ⟨hnz.le,hnv.le⟩)
  have hImage : IsOpen (P '' D) := by
    rcases ha.is_constant_or_isOpen isPreconnected_univ with ⟨y,hy⟩ | h
    · have h₀ := hy z (Set.mem_univ _)
      have h₁' := hy v (Set.mem_univ _)
      exact False.elim ((hnz.trans hnv).ne (congrArg norm (h₀.trans h₁'.symm)))
    · exact h D (Set.subset_univ _) hD
  obtain ⟨ζ,⟨x,hx,hxζ⟩,d,hd,hζ⟩ := root_of_neg_one_in_open (U:=P '' D) hImage ⟨w,hw,rfl⟩ hw₁
  refine ⟨x,⟨m*n,k*n,d,hd,?_⟩,?_⟩
  · change P x ^ d = -1
    rw [hxζ,hζ]
  · rw [dist_comm]; exact hx

end CameronKayibi.Flow.SwapDisk
