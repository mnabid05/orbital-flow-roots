import Conjectures.CameronKayibi
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace CameronKayibi.Flow

/-- Ordinary flow polynomial of the cyclic chain of doubled stages and cycle blocks. -/
def base (m k : ℕ) (x : ℝ) : ℝ := (x-1)^m * (x-2)^k

/-- The involution exchanges two copies. An orbit is an unordered pair of flows. -/
noncomputable def value (m k : ℕ) (x : ℝ) : ℝ := base m k x * (base m k x+1)/2

noncomputable def polynomial (m k : ℕ) : Polynomial ℝ :=
  let f := (Polynomial.X-1)^m * (Polynomial.X-2)^k
  Polynomial.C (1/2 : ℝ) * f * (f+1)

@[simp] theorem eval_polynomial (m k : ℕ) (x : ℝ) :
    (polynomial m k).eval x = value m k x := by
  simp [polynomial,value,base]
  ring

private lemma twice (z : ℝ) (m t : ℕ) : (-z)^(2*(m*t)) = ((z^m)^2)^t := by
  calc
    _ = ((z^2)^m)^t := by rw [pow_mul,neg_sq,pow_mul]
    _ = ((z^m)^2)^t := by congr 1; rw [←pow_mul, ←pow_mul, Nat.mul_comm 2 m]

private lemma scale (m k t : ℕ) (x : ℝ) :
    base (2*(m*t)+1) (2*(k*t)) x =
      -(1-x) * (((1-x)^m*(2-x)^k)^2)^t := by
  simp only [base, pow_succ, show x-1 = -(1-x) by ring, show x-2 = -(2-x) by ring, twice, mul_pow]
  ring

private theorem interior {l u : ℝ} (hl : 0 < l) (hlt : l < u) (hu : u < 1) :
    ∃ (a b : ℕ) (x : ℝ), l < x ∧ x < u ∧ value (2*a+1) (2*b) x = 0 := by
  have hpu : 0 < 1-u := by linarith
  have hpl : 0 < 1-l := by linarith
  obtain ⟨m,k,hle,hri⟩ := separate hpu (by linarith : 1-u ≤ 1-l)
    (by linarith : 1-l < 1) (by linarith : 1 < 2-u) (by linarith : 2-u < 2-l)
  let wl := (1-l)^m*(2-l)^k
  let wu := (1-u)^m*(2-u)^k
  change 1 < wl at hle
  change wu < 1 at hri
  have hu0 : 0 ≤ wu := mul_nonneg (pow_nonneg hpu.le _) (pow_nonneg (by linarith) _)
  have hL : 1 < wl^2 := by nlinarith [sq_nonneg (wl-1)]
  have hU : wu^2 ≤ 1 := by simpa using pow_le_pow_left₀ hu0 hri.le 2
  obtain ⟨t,ht⟩ := pow_unbounded_of_one_lt (1/(1-l)) hL
  have hL' : 1 < (1-l)*(wl^2)^t := by simpa only [mul_comm] using (div_lt_iff₀ hpl).mp ht
  have hU' : (1-u)*(wu^2)^t < 1 := by
    calc
      _ ≤ (1-u)*1 := mul_le_mul_of_nonneg_left (pow_le_one₀ (sq_nonneg _) hU) hpu.le
      _ < 1 := by linarith
  let f := fun x : ℝ => base (2*(m*t)+1) (2*(k*t)) x+1
  have cont : Continuous f := by unfold f base; fun_prop
  have h0 : (0:ℝ) ∈ Set.Ioo (f l) (f u) := by
    change _ < 0 ∧ 0 < _
    simp only [f,scale]
    change -(1-l)*(wl^2)^t+1 < 0 ∧ 0 < -(1-u)*(wu^2)^t+1
    exact ⟨by linarith only [hL'],by linarith only [hU']⟩
  obtain ⟨x,hx,hf⟩ := intermediate_value_Ioo hlt.le cont.continuousOn h0
  refine ⟨m*t,k*t,x,hx.1,hx.2,?_⟩
  change base _ _ x * f x/2=0
  rw [hf,mul_zero,zero_div]

/-- Every open subinterval of the closed unit interval contains a real orbital flow root. -/
theorem root_in_unit_interval {l u : ℝ} (hl : 0 ≤ l) (hlt : l < u) (hu : u ≤ 1) :
    ∃ (a b : ℕ) (x : ℝ), l < x ∧ x < u ∧ value (2*a+1) (2*b) x = 0 := by
  obtain ⟨l',hll',hl'u⟩ := exists_between hlt
  obtain ⟨u',hl'u',hu'u⟩ := exists_between hl'u
  obtain ⟨a,b,x,hxl,hxu,hz⟩ := interior (hl.trans_lt hll') hl'u' (hu'u.trans_le hu)
  exact ⟨a,b,x,hll'.trans hxl,hxu.trans hu'u,hz⟩

end CameronKayibi.Flow
