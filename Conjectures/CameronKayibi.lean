import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! The polynomial part of the Cameron–Kayibi construction. -/
namespace CameronKayibi

/-- Separate two endpoint values by taking integral powers of the two decorating factors. -/
theorem separate {a c b d : ℝ} (hc : 0 < c) (hca : c ≤ a) (ha : a < 1)
    (hd : 1 < d) (hdb : d < b) :
    ∃ m k : ℕ, 1 < a^m*b^k ∧ c^m*d^k < 1 := by
  have ha0 := hc.trans_le hca
  let z := (d+b)/2
  have hdz : d < z := by dsimp [z]; linarith
  have hzb : z < b := by dsimp [z]; linarith
  have hz1 : 1 < z := hd.trans hdz
  have hz : 0 < z := by linarith
  have hd0 : 0 < d := by linarith
  have hratio : d / z < 1 := (div_lt_one hz).mpr hdz
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one ha0 hratio
  have hk0 : k ≠ 0 := by intro hh; subst k; simp at hk; linarith
  have hzk := pow_pos hz k
  obtain ⟨m, hmlo, hmhi⟩ := exists_nat_pow_near_of_lt_one (inv_pos.mpr hzk)
    ((inv_le_one₀ hzk).mpr (one_le_pow₀ hz1.le)) ha0 ha
  refine ⟨m,k,?_,?_⟩
  · calc
      1 = (z^k)⁻¹*z^k := (inv_mul_cancel₀ hzk.ne').symm
      _ ≤ a^m*z^k := mul_le_mul_of_nonneg_right hmhi hzk.le
      _ < a^m*b^k := mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hzb hz.le hk0) (pow_pos ha0 m)
  · rw [div_pow] at hk
    have hdk := (div_lt_iff₀ hzk).mp hk
    calc
      c^m*d^k ≤ a^m*d^k := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc.le hca m) (pow_nonneg hd0.le _)
      _ < a^(m+1)*z^k := by rw [pow_succ]; nlinarith only [mul_lt_mul_of_pos_left hdk (pow_pos ha0 m)]
      _ < (z^k)⁻¹*z^k := mul_lt_mul_of_pos_right hmlo hzk
      _ = 1 := inv_mul_cancel₀ hzk.ne'

/-- Colorings of one marked edge's attached triangles and tetrahedra. -/
def decoration (m k : ℕ) (x : ℝ) : ℝ := (x-2)^m * ((x-2)*(x-3))^k

/-- Ordinary chromatic polynomial of the base, K₂,₃. -/
def base (x : ℝ) : ℝ := x*(x-1)^3 + x*(x-1)*(x-2)^3

/-- Fixed-coloring polynomial for either nontrivial element of C₃. -/
def quotient (x : ℝ) : ℝ := x*(x-1)^2

/-- The orbit-counting formula for the decorated graph. -/
noncomputable def orbitalValue (m k : ℕ) (x : ℝ) : ℝ :=
  decoration m k x * (base x * decoration m k x ^ 2 + 2 * quotient x) / 3

private theorem base_neg {x : ℝ} (hx : 1 < x) (hx' : x < 32/27) : base x < 0 := by
  have h1 : (x-1)^2 < (1/5 : ℝ)^2 :=
    pow_lt_pow_left₀ (by linarith) (by linarith) (by decide)
  have h2 : (4/5 : ℝ)^3 < (2-x)^3 :=
    pow_lt_pow_left₀ (by linarith) (by norm_num) (by decide)
  have he : base x = x*(x-1)*((x-1)^2+(x-2)^3) := by unfold base; ring
  rw [he]
  apply mul_neg_of_pos_of_neg (mul_pos (by linarith) (by linarith))
  nlinarith only [h1,h2]

private theorem quotient_pos {x : ℝ} (hx : 1 < x) : 0 < quotient x :=
  mul_pos (by linarith) (pow_pos (by linarith) _)

private def weight (m k : ℕ) (x : ℝ) : ℝ :=
  (2-x)^m * ((2-x)*(3-x))^k

private theorem decoration_sq (m k : ℕ) (x : ℝ) :
    (decoration m k x)^2 = (weight m k x)^2 := by
  have hprod : (x-2)*(x-3) = (2-x)*(3-x) := by ring
  have hpow : ((x-2)^m)^2 = ((2-x)^m)^2 := by
    calc
      _ = ((x-2)^2)^m := by rw [←pow_mul, ←pow_mul, Nat.mul_comm]
      _ = ((2-x)^2)^m := by rw [show (x-2)^2=(2-x)^2 by ring]
      _ = ((2-x)^m)^2 := by rw [←pow_mul, ←pow_mul, Nat.mul_comm]
  simp only [decoration, weight, hprod, mul_pow, hpow]

private theorem weight_scale (m k j : ℕ) (x : ℝ) :
    weight (m*j) (k*j) x = (weight m k x)^j := by
  simp only [weight, pow_mul, mul_pow]

private theorem amplify {a b ul vl ur vr : ℝ} (ha : 1 < a) (hb0 : 0 ≤ b) (hb : b < 1)
    (hul : ul < 0) (hur : ur < 0) (hvr : 0 < vr) :
    ∃ j : ℕ, ul * (a^j)^2 + 2*vl < 0 ∧ 0 < ur*(b^j)^2 + 2*vr := by
  have hal : 1 < a^2 := by nlinarith [sq_nonneg (a-1)]
  have hbr : b^2 < 1 := by nlinarith [mul_pos (sub_pos.mpr hb) (show 0 < 1+b by linarith)]
  have hl := (tendsto_pow_atTop_atTop_of_one_lt hal).eventually
    (Filter.eventually_gt_atTop (2*vl/(-ul)))
  have hr := (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg b) hbr).eventually
    (eventually_lt_nhds (show 0 < 2*vr/(-ur) from div_pos (by linarith) (by linarith)))
  obtain ⟨j, hleft, hright⟩ := (hl.and hr).exists
  have hl' := (div_lt_iff₀ (show 0 < -ul by linarith)).mp hleft
  have hr' := (lt_div_iff₀ (show 0 < -ur by linarith)).mp hright
  change 2*vl < (a^2)^j * (-ul) at hl'
  change (b^2)^j * (-ur) < 2*vr at hr'
  rw [←pow_mul, Nat.mul_comm, pow_mul] at hl' hr'
  exact ⟨j, by linarith, by linarith⟩

/-- Every open subinterval of the ordinary chromatic root gap contains a root
of an explicit orbital polynomial. -/
theorem root_in_gap_interval {l u : ℝ} (hl : 1 < l) (hlu : l < u) (hu : u < 32/27) :
    ∃ (m k : ℕ) (x : ℝ), l < x ∧ x < u ∧ orbitalValue m k x = 0 := by
  have hu₀ : 0 < 2-u := by linarith
  have hB : 1 < (2-u)*(3-u) := by
    nlinarith [mul_pos (show 0 < (2-u)-4/5 by linarith) (show 0 < 3-u by linarith)]
  have hBu : (2-u)*(3-u) < (2-l)*(3-l) :=
    mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨m,k,hle,hri⟩ := separate hu₀ (by linarith : 2-u ≤ 2-l) (by linarith : 2-l < 1) hB hBu
  change 1 < weight m k l at hle
  change weight m k u < 1 at hri
  have hwu : 0 ≤ weight m k u := mul_nonneg (pow_nonneg hu₀.le _) (pow_nonneg (by linarith) _)
  obtain ⟨j, hneg, hpos⟩ := amplify (vl := quotient l) hle hwu hri
    (base_neg hl (hlu.trans hu)) (base_neg (hl.trans hlu) hu) (quotient_pos (hl.trans hlu))
  let f : ℝ → ℝ := fun x => base x * decoration (m*j) (k*j) x ^ 2 + 2*quotient x
  have hc : Continuous f := by unfold f base decoration quotient; fun_prop
  have fixed (x : ℝ) : f x = base x*((weight m k x)^j)^2 + 2*quotient x := by
    dsimp only [f]; rw [decoration_sq, weight_scale]
  have hz : (0 : ℝ) ∈ Set.Ioo (f l) (f u) := by
    simp only [Set.mem_Ioo, fixed]; exact ⟨hneg,hpos⟩
  obtain ⟨x,hx,hzero⟩ := intermediate_value_Ioo hlu.le hc.continuousOn hz
  refine ⟨m*j,k*j,x,hx.1,hx.2,?_⟩
  change decoration (m*j) (k*j) x * f x / 3 = 0
  rw [hzero,mul_zero,zero_div]

namespace Theta

/-- The quantity (x−1)^L for path length L=2(n+1). -/
def pathPower (n : ℕ) (x : ℝ) := ((x-1)^2)^n * (x-1)^2

theorem pathPower_eq (n : ℕ) (x : ℝ) : pathPower n x = (x-1)^(2*(n+1)) := by
  rw [Nat.mul_succ, pow_add, pow_mul]; rfl

/-- x² times the ordinary chromatic polynomial on the three paths. -/
def baseNumerator (n : ℕ) (x : ℝ) :=
  (pathPower n x + (x-1))^3 + (x-1)*(pathPower n x - 1)^3

/-- x² times the chromatic polynomial on the path fixed by a nonidentity rotation. -/
def fixedNumerator (n : ℕ) (x : ℝ) := x^3 * pathPower n x

/-- One book adds a vertex joined to the two edge ends and s vertices joined to all three. -/
def decoration (m k s : ℕ) (x : ℝ) := (x-2)^m * ((x-2)*(x-3)^s)^k

/-- Orbital chromatic value at nonzero x for the decorated three-path graph. -/
noncomputable def orbitalValue (n m k s : ℕ) (x : ℝ) :=
  decoration m k s x * (baseNumerator n x * decoration m k s x ^ 2 + 2*fixedNumerator n x) /
    (3*x^2)

private theorem eventually_negative {x : ℝ} (hx : 1 < x) (hx' : x < 2) :
    ∀ᶠ n in Filter.atTop, baseNumerator n x < 0 := by
  let g : ℝ → ℝ := fun z => (z+(x-1))^3+(x-1)*(z-1)^3
  have hsq : (x-1)^2 < 1 := by nlinarith [mul_neg_of_pos_of_neg (show 0 < x by linarith) (show x-2 < 0 by linarith)]
  have hlim : Filter.Tendsto (fun n => pathPower n x) Filter.atTop (nhds 0) := by
    simpa only [pathPower, zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg (x-1)) hsq).mul_const ((x-1)^2)
  have hcont : Continuous g := by dsimp [g]; fun_prop
  have hg : g 0 < 0 := by
    have hprod := mul_neg_of_pos_of_neg (mul_pos (show 0 < x-1 by linarith) (show 0 < x by linarith)) (show x-2 < 0 by linarith)
    dsimp [g]; nlinarith only [hprod]
  exact ((hcont.tendsto 0).comp hlim).eventually_lt_const hg

private def weight (m k s : ℕ) (x : ℝ) := (2-x)^m * ((2-x)*(3-x)^s)^k

private theorem decoration_sq (m k s : ℕ) (x : ℝ) :
    decoration m k s x ^ 2 = weight m k s x ^ 2 := by
  rw [← sq_abs (decoration m k s x), ← sq_abs (weight m k s x)]
  simp only [decoration, weight, abs_mul, abs_pow, abs_sub_comm x 2, abs_sub_comm x 3]

private theorem weight_scale (m k s j : ℕ) (x : ℝ) :
    weight (m*j) (k*j) s x = weight m k s x ^ j := by
  simp only [weight, pow_mul, mul_pow]

/-- Every open subinterval of (1,2) contains a root of an explicit orbital function. -/
theorem root_between_one_two {l u : ℝ} (hl : 1 < l) (hlu : l < u) (hu : u < 2) :
    ∃ (n m k s : ℕ) (x : ℝ), l < x ∧ x < u ∧ orbitalValue n m k s x = 0 := by
  obtain ⟨n,hnl,hnu⟩ := ((eventually_negative hl (hlu.trans hu)).and
    (eventually_negative (hl.trans hlu) hu)).exists
  have hcu : 0 < 2-u := by linarith
  have hdu : 1 < 3-u := by linarith
  obtain ⟨s,hs⟩ := pow_unbounded_of_one_lt (1/(2-u)) hdu
  have hbook : 1 < (2-u)*(3-u)^s := by
    simpa only [mul_comm] using (div_lt_iff₀ hcu).mp hs
  have hbook' : (2-u)*(3-u)^s < (2-l)*(3-l)^s :=
    mul_lt_mul_of_lt_of_le_of_pos_of_nonneg (by linarith)
      (pow_le_pow_left₀ (by linarith) (by linarith) s) (pow_pos (by linarith) _) (by linarith)
  obtain ⟨m,k,hle,hri⟩ := separate hcu (by linarith : 2-u ≤ 2-l) (by linarith : 2-l < 1)
    hbook hbook'
  change 1 < weight m k s l at hle
  change weight m k s u < 1 at hri
  have hwu : 0 ≤ weight m k s u :=
    mul_nonneg (pow_nonneg hcu.le _) (pow_nonneg (by linarith) _)
  have hfixed : 0 < fixedNumerator n u := by
    have : 0 < u-1 := by linarith
    have : 0 < u := by linarith
    unfold fixedNumerator pathPower; positivity
  obtain ⟨j,hneg,hpos⟩ := amplify (vl := fixedNumerator n l) hle hwu hri hnl hnu hfixed
  let f : ℝ → ℝ := fun x => baseNumerator n x * decoration (m*j) (k*j) s x ^ 2 + 2*fixedNumerator n x
  have hc : Continuous f := by unfold f baseNumerator fixedNumerator pathPower decoration; fun_prop
  have fixed (x : ℝ) : f x = baseNumerator n x * (weight m k s x ^ j)^2 + 2*fixedNumerator n x := by
    dsimp only [f]; rw [decoration_sq, weight_scale]
  have hz : (0 : ℝ) ∈ Set.Ioo (f l) (f u) := by
    simp only [Set.mem_Ioo, fixed]; exact ⟨hneg,hpos⟩
  obtain ⟨x,hx,hzero⟩ := intermediate_value_Ioo hlu.le hc.continuousOn hz
  refine ⟨n,m*j,k*j,s,x,hx.1,hx.2,?_⟩
  change decoration (m*j) (k*j) s x * f x / (3*x^2) = 0
  rw [hzero,mul_zero,zero_div]

/-- Joining to a fixed clique on j vertices gives a falling factorial and a translation. -/
noncomputable def joinedValue (j n m k s : ℕ) (x : ℝ) :=
  (∏ i ∈ Finset.range j, (x-i)) * orbitalValue n m k s (x-j)

/-- Root density on the entire half-line, using only this construction and fixed cliques. -/
theorem root_in_every_interval {l u : ℝ} (hl : 1 ≤ l) (hlu : l < u) :
    ∃ (j n m k s : ℕ) (x : ℝ), l < x ∧ x < u ∧ joinedValue j n m k s x = 0 := by
  let j := ⌊l-1⌋₊
  have hj : (j : ℝ) ≤ l-1 := Nat.floor_le (by linarith)
  have hj' : l-1 < (j:ℝ)+1 := Nat.lt_floor_add_one _
  let a := l-j
  let b := min (u-j) 2
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have hab : a < b := lt_min (by dsimp [a]; linarith) (by dsimp [a]; linarith)
  have hb : b ≤ 2 := min_le_right _ _
  have hbu : b ≤ u-j := min_le_left _ _
  obtain ⟨a',haa',ha'b⟩ := exists_between hab
  obtain ⟨b',ha'b',hb'b⟩ := exists_between ha'b
  obtain ⟨n,m,k,s,x,hxl,hxu,hz⟩ := root_between_one_two (ha.trans_lt haa') ha'b' (hb'b.trans_le hb)
  refine ⟨j,n,m,k,s,x+j,?_,?_,?_⟩
  · have hax := haa'.trans hxl
    change l-(j:ℝ) < x at hax
    linarith only [hax]
  · have hxu' := hxu.trans_le (hb'b.le.trans hbu)
    linarith only [hxu']
  · simp [joinedValue, hz]

end Theta
end CameronKayibi
