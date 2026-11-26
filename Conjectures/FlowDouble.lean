import Conjectures.FlowGraph
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace CameronKayibi.FlowDouble

open FlowGraph

variable {V E : Type}

/-- Two disjoint copies, with the same tag on an edge and its two ends. -/
def double (H : OrientedGraph V E) : OrientedGraph (ZMod 2 × V) (ZMod 2 × E) where
  tail e := (e.1,H.tail e.2)
  head e := (e.1,H.head e.2)

/-- Translating the binary copy tag is a permutation; the nonidentity translation
interchanges the two copies. -/
def perm (X : Type) (r : ZMod 2) : Equiv.Perm (ZMod 2 × X) where
  toFun p := (p.1+r,p.2)
  invFun p := (p.1-r,p.2)
  left_inv p := by cases p; simp
  right_inv p := by cases p; simp

structure Automorphism (H : OrientedGraph V E) where
  vertex : Equiv.Perm V
  edge : Equiv.Perm E
  map_tail : ∀ e, H.tail (edge e) = vertex (H.tail e)
  map_head : ∀ e, H.head (edge e) = vertex (H.head e)

def rotation (H : OrientedGraph V E) (r : ZMod 2) : Automorphism (double H) :=
  ⟨perm V r, perm E r, fun _ => rfl, fun _ => rfl⟩

theorem faithful (X : Type) [Nonempty X] : Function.Injective (perm X) := by
  intro r s h
  have hh := congrArg (fun p : Equiv.Perm (ZMod 2 × X) => (p (0,Classical.choice (inferInstance : Nonempty X))).1) h
  simpa [perm] using hh

variable [Fintype E] [DecidableEq V] (H : OrientedGraph V E)
variable (A : Type) [AddCommGroup A]

theorem tagged_sum {I : Type} [Fintype I] [DecidableEq I] (t : E → V) (f : I × E → A) (i : I) (v : V) :
    (∑ u : I × E, if (u.1, t u.2)=(i,v) then f u else 0) =
      ∑ e : E, if t e = v then f (i,e) else 0 := by
  classical
  rw [Fintype.sum_prod_type]
  simp [Prod.ext_iff, ite_and]

theorem kirchhoff_iff (f : ZMod 2 × E → A) :
    Kirchhoff (double H) f ↔ ∀ i, Kirchhoff H (fun e => f (i,e)) := by
  simp only [Kirchhoff, double, Prod.forall, tagged_sum]

/-- Restrict a genuine nowhere-zero flow to each connected component copy. -/
def split : Flow (double H) A ≃ (ZMod 2 → Flow H A) where
  toFun f i := ⟨fun e => f.1 (i,e), fun e => f.2.1 (i,e),
    (kirchhoff_iff H A f.1).1 f.2.2 i⟩
  invFun f := ⟨fun e => (f e.1).1 e.2, fun e => (f e.1).2.1 e.2,
    (kirchhoff_iff H A _).2 (fun i => (f i).2.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Pullback along the actual copy-exchanging automorphism, on its edge colors. -/
instance action : AddAction (ZMod 2) (Flow (double H) A) where
  vadd r f := (split H A).symm (fun i => split H A f (i+r))
  zero_vadd f := by
    apply Subtype.ext; funext e
    change f.1 (e.1+0,e.2) = f.1 e
    rw [add_zero]
  add_vadd r s f := by
    apply Subtype.ext; funext e
    change f.1 (e.1+(r+s),e.2) = f.1 (e.1+r+s,e.2)
    rw [add_assoc]

theorem action_is_pullback (r : ZMod 2) (f : Flow (double H) A) (e : ZMod 2 × E) :
    (r +ᵥ f).1 e = f.1 ((rotation H r).edge e) := rfl

abbrev SwapOrbits := AddAction.orbitRel.Quotient (ZMod 2) (Flow (double H) A)

private def pairEquiv : Flow (double H) A ≃ (Flow H A × Flow H A) where
  toFun f := (split H A f 0,split H A f 1)
  invFun p := (split H A).symm (fun i => if i=0 then p.1 else p.2)
  left_inv f := by
    apply (split H A).injective
    funext i
    fin_cases i <;> rfl
  right_inv _ := rfl

/-- Actual flow orbits under the graph action are exactly unordered pairs of base flows. -/
def orbitsEquiv : SwapOrbits H A ≃ Sym2 (Flow H A) :=
  Quotient.congr (rb := Sym2.Rel.setoid _) (pairEquiv H A) (by
    intro f g
    change (AddAction.orbitRel (ZMod 2) _ f g) ↔ Sym2.Rel _ _ _
    rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff, Sym2.rel_iff']
    constructor
    · rintro ⟨r,rfl⟩
      fin_cases r
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (h | h)
      · exact ⟨0, (zero_vadd _ _).trans ((pairEquiv H A).injective h).symm⟩
      · exact ⟨1, (pairEquiv H A).injective h.symm⟩)

theorem orbit_count_div [Finite A] :
    Nat.card (SwapOrbits H A) = Nat.card (Flow H A) * (Nat.card (Flow H A)+1) / 2 := by
  classical
  letI : Fintype (Flow H A) := Fintype.ofFinite _
  rw [Nat.card_congr (orbitsEquiv H A), Nat.card_eq_fintype_card,
    Sym2.card, Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm]
  rw [Nat.card_eq_fintype_card]

theorem orbit_count [Finite A] :
    2 * Nat.card (SwapOrbits H A) = Nat.card (Flow H A) * (Nat.card (Flow H A)+1) := by
  classical
  rw [orbit_count_div]
  apply Nat.mul_div_cancel'
  exact (Nat.even_mul_succ_self _).two_dvd

end CameronKayibi.FlowDouble
