import Conjectures.FlowConnected
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Ring

namespace CameronKayibi.FlowGraph.Bundles

open Polynomial

/-- A cyclic graph with p+1 stages, each consisting of s parallel directed edges. -/
def graph (p s : ℕ) : OrientedGraph (Fin (p+1)) (Fin (p+1) × Fin s) where
  tail e := e.1
  head e := finRotate (p+1) e.1

variable {p s : ℕ} {A : Type} [AddCommGroup A]

private abbrev total (f : Fin (p+1) × Fin s → A) (i : Fin (p+1)) := ∑ j, f (i,j)

theorem kirchhoff_iff (f : Fin (p+1) × Fin s → A) : Kirchhoff (graph p s) f ↔
    ∀ i, total f i = total f 0 := by
  have hlocal (v : Fin (p+1)) :
      (∑ e, if (graph p s).tail e = finRotate _ v then f e else 0) = total f (finRotate _ v) ∧
      (∑ e, if (graph p s).head e = finRotate _ v then f e else 0) = total f v := by
    have sel (x y : Fin (p+1)) : (∑ j : Fin s, if x = y then f (x,j) else 0) =
        if x = y then total f x else 0 := by
      by_cases h : x = y <;> simp [h,total]
    simp only [graph,Fintype.sum_prod_type,Equiv.apply_eq_iff_eq,sel]
    simp
  constructor
  · intro h j
    induction j using Fin.induction with
    | zero => rfl
    | succ i ih =>
      have hl := h (finRotate _ i.castSucc)
      rw [(hlocal i.castSucc).1,(hlocal i.castSucc).2] at hl
      have hr : finRotate (p+1) i.castSucc = i.succ := finRotate_of_lt i.isLt
      exact (hr ▸ hl).trans ih
  · intro h v
    obtain ⟨i,rfl⟩ := (finRotate (p+1)).surjective v
    exact (hlocal i).1.trans (((h _).trans (h i).symm).trans (hlocal i).2.symm)

private abbrev Nonzero (A : Type) [Zero A] := {a : A // a ≠ 0}
private abbrev Config (s : ℕ) (a : A) := {f : Fin s → Nonzero A // (∑ i, (f i).1) = a}

private def splitEquiv : Flow (graph p s) A ≃ Σ a : A, Fin (p+1) → Config s a where
  toFun f := ⟨total f.1 0,fun i => ⟨fun j => ⟨f.1 (i,j),f.2.1 _⟩,
    (kirchhoff_iff f.1).mp f.2.2 i⟩⟩
  invFun d := ⟨fun e => (d.2 e.1 |>.1 e.2).1,fun e => (d.2 e.1 |>.1 e.2).2,
    (kirchhoff_iff _).mpr (fun i => (d.2 i).2.trans (d.2 0).2.symm)⟩
  left_inv _ := rfl
  right_inv d := by
    rcases d with ⟨a,g⟩
    apply Sigma.ext (g 0).2
    apply Function.hfunext rfl
    intro i j h
    cases h
    let t := ∑ j, ((g 0).1 j).1
    have ht : t = a := (g 0).2
    have hh (x : Fin s → Nonzero A) : ((∑ j, (x j).1) = t) ↔ (∑ j, (x j).1) = a := by rw [ht]
    apply (Subtype.heq_iff_coe_eq (a2:=g i) hh).mpr
    rfl

private def consEquiv (s : ℕ) (a : A) :
    Config (s+1) a ≃ Σ v : Nonzero A, Config s (a-v.1) where
  toFun f := ⟨f.1 0,fun i => f.1 i.succ,by
    have h := f.2
    rw [Fin.sum_univ_succ] at h
    exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans h)⟩
  invFun d := ⟨Fin.cons d.1 d.2.1,by
    rw [Fin.sum_univ_succ]
    change d.1.1 + (∑ i, (d.2.1 i).1) = a
    rw [d.2.2,add_comm,sub_add_cancel]⟩
  right_inv _ := rfl
  left_inv f := by
    apply Subtype.ext
    funext i
    induction i using Fin.cases <;> rfl

/-- The entries count assignments to a single bundle with specified total zero
and with specified nonzero total, respectively. -/
def counts (q : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1,0)
  | s+1 =>
    let c := counts q s
    ((q-1)*c.2,c.1+(q-2)*c.2)

private theorem sum_one_exception {X : Type} [Fintype X] [DecidableEq X] (u : X) (a b : ℕ) :
    (∑ x : X, if x=u then a else b) = a+(Fintype.card X-1)*b := by
  simp [Finset.sum_ite,Finset.filter_eq',Finset.filter_ne',Finset.card_erase_of_mem]

private lemma card_nonzero (A : Type) [Zero A] [Fintype A] [DecidableEq A] :
    Fintype.card (Nonzero A) = Fintype.card A - 1 := by
  change Fintype.card {x : A // ¬ x = 0} = _
  rw [Fintype.card_subtype_compl]
  simp

private theorem card_config [Fintype A] [DecidableEq A] (s : ℕ) (a : A) :
    Fintype.card (Config s a) =
      if a = 0 then (counts (Fintype.card A) s).1 else (counts (Fintype.card A) s).2 := by
  classical
  induction s generalizing a with
  | zero =>
    by_cases ha : a=0
    · subst a
      simp [Config,counts]
    · simp [Config,counts,ha,Ne.symm ha]
  | succ s ih =>
    rw [Fintype.card_congr (consEquiv s a), Fintype.card_sigma]
    simp_rw [ih]
    by_cases ha : a=0
    · subst a
      have hz (v : Nonzero A) : (0:A)-v.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm v.2)
      simp_rw [if_neg (hz _)]
      simp [counts,card_nonzero]
    · have he (v : Nonzero A) : (a-v.1 = 0) ↔ v = ⟨a,ha⟩ := by
        rw [sub_eq_zero,Subtype.ext_iff,eq_comm]
      simp_rw [he]
      rw [sum_one_exception]
      simp [counts,ha,card_nonzero,Nat.sub_sub]

theorem card_flow (p s : ℕ) (A : Type) [AddCommGroup A] [Fintype A] :
    Nat.card (Flow (graph p s) A) =
    (counts (Fintype.card A) s).1^(p+1) +
      (Fintype.card A-1)*(counts (Fintype.card A) s).2^(p+1) := by
  classical
  rw [Nat.card_congr (splitEquiv (p:=p) (s:=s) (A:=A)),Nat.card_eq_fintype_card,Fintype.card_sigma]
  simp only [Fintype.card_fun,Fintype.card_fin,card_config,ite_pow]
  exact sum_one_exception _ _ _


/-- The two single-bundle counting polynomials, by the same recurrence. -/
noncomputable def pairPolynomial : ℕ → Polynomial ℂ × Polynomial ℂ
  | 0 => (1,0)
  | s+1 =>
    let c := pairPolynomial s
    ((X-1)*c.2, c.1 + (X-2)*c.2)

/-- Ordinary flow polynomial of the bundle cycle. -/
noncomputable def polynomial (p s : ℕ) : Polynomial ℂ :=
  (pairPolynomial s).1^(p+1) + (X-1)*(pairPolynomial s).2^(p+1)

private theorem eval_nat_pair (s q : ℕ) (hq : 2 ≤ q) :
    ((pairPolynomial s).1.eval (q : ℂ) = (counts q s).1) ∧
    ((pairPolynomial s).2.eval (q : ℂ) = (counts q s).2) := by
  induction s with
  | zero => simp [pairPolynomial,counts]
  | succ s ih =>
    simp [pairPolynomial,counts,ih.1,ih.2,Nat.cast_sub (show 1 ≤ q by omega),Nat.cast_sub hq]

/-- At every finite abelian-group order, this polynomial counts the actual flows. -/
theorem eval_counts (p s : ℕ) (A : Type) [AddCommGroup A] [Fintype A] :
    (polynomial p s).eval (Fintype.card A : ℂ) = Nat.card (Flow (graph p s) A) := by
  rw [card_flow]
  by_cases hq : 2 ≤ Fintype.card A
  · obtain ⟨h₀,h₁⟩ := eval_nat_pair s _ hq
    simp [polynomial,h₀,h₁,Nat.cast_sub (show 1 ≤ Fintype.card A by omega)]
  · have hp : 0 < Fintype.card A := Fintype.card_pos
    have he : Fintype.card A = 1 := by omega
    rw [he]
    cases s <;> simp [polynomial,pairPolynomial,counts]

private theorem closed_pair (s : ℕ) (z : ℂ) :
    z*(pairPolynomial s).1.eval z = (z-1)^s+(z-1)*(-1)^s ∧
    z*(pairPolynomial s).2.eval z = (z-1)^s-(-1)^s := by
  induction s with
  | zero => simp [pairPolynomial]
  | succ s ih =>
    simp only [pairPolynomial,eval_mul,eval_sub,eval_X,eval_one,eval_add,eval_ofNat,pow_succ]
    constructor
    · rw [show z*((z-1)*(pairPolynomial s).2.eval z) =
        (z-1)*(z*(pairPolynomial s).2.eval z) by ring,ih.2]
      ring
    · rw [show z*((pairPolynomial s).1.eval z+(z-2)*(pairPolynomial s).2.eval z) =
        z*(pairPolynomial s).1.eval z+(z-2)*(z*(pairPolynomial s).2.eval z) by ring,
        ih.1,ih.2]
      ring

/-- Polynomial identity in the shifted coordinate, valid at zeros of either
denominator as well. This is the form entering the exterior complex-density proof. -/
theorem scaled_polynomial (p s : ℕ) (z : ℂ) :
    z^(p+1) * (polynomial p s).eval z = (-1:ℂ)^(s*(p+1)) *
       (((1-z)^s-(1-z))^(p+1) + (z-1)*((1-z)^s-1)^(p+1)) := by
  obtain ⟨hA,hB⟩ := closed_pair s z
  have hp : (z-1)^s = (-1:ℂ)^s*(1-z)^s := by rw [← mul_pow]; ring_nf
  have hA' : z*(pairPolynomial s).1.eval z = (-1:ℂ)^s*((1-z)^s-(1-z)) := by rw [hA,hp]; ring
  have hB' : z*(pairPolynomial s).2.eval z = (-1:ℂ)^s*((1-z)^s-1) := by rw [hB,hp]; ring
  calc
    _ = (z*(pairPolynomial s).1.eval z)^(p+1) + (z-1)*(z*(pairPolynomial s).2.eval z)^(p+1) := by
      simp [polynomial,mul_pow]; ring
    _ = _ := by rw [hA',hB']; simp only [mul_pow,pow_mul]; ring

/-- There is a forward edge between every two consecutive vertices as soon
as the bundle width is positive. -/
theorem connected (p s : ℕ) (hs : 0 < s) : (FlowBouquet.underlying (graph p s)).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨0,?_⟩
  intro v
  induction v using Fin.induction with
  | zero => exact SimpleGraph.Reachable.rfl
  | succ i ih =>
    have he := edge_reachable (graph p s) (i.castSucc,⟨0,hs⟩)
    change (FlowBouquet.underlying (graph p s)).Reachable i.castSucc (finRotate _ i.castSucc) at he
    have hr : finRotate (p+1) i.castSucc = i.succ := finRotate_of_lt i.isLt
    exact ih.trans (hr ▸ he)

/-- The constant edge current 1 over the cyclic group of order four is a flow. -/
theorem eval_four_ne_zero (p s : ℕ) : (polynomial p s).eval 4 ≠ 0 := by
  have hb := eval_counts p s (ZMod 4)
  rw [ZMod.card] at hb
  have f : Flow (graph p s) (ZMod 4) :=
    ⟨fun _ => 1,fun _ => (by decide : (1 : ZMod 4) ≠ 0),(kirchhoff_iff _).mpr (fun _ => rfl)⟩
  haveI : Nonempty (Flow (graph p s) (ZMod 4)) := ⟨f⟩
  have hp : 0 < Nat.card (Flow (graph p s) (ZMod 4)) := Nat.card_pos
  intro h
  norm_num at hb
  rw [h] at hb
  exact (Nat.cast_ne_zero.mpr hp.ne') hb.symm

end CameronKayibi.FlowGraph.Bundles
