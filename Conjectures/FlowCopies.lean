import Conjectures.FlowDouble
import Mathlib.Data.Nat.Factorial.BigOperators

namespace CameronKayibi.FlowCopies
open FlowGraph

variable {V E : Type}

/-- The disjoint union of d copies of an oriented graph. -/
def copies (H : OrientedGraph V E) (d : ℕ) : OrientedGraph (Fin d × V) (Fin d × E) where
  tail e := (e.1,H.tail e.2)
  head e := (e.1,H.head e.2)

/-- Every permutation of the components is an actual directed graph automorphism. -/
def rotation (H : OrientedGraph V E) {d : ℕ} (p : Equiv.Perm (Fin d)) :
    FlowDouble.Automorphism (copies H d) :=
  ⟨p.prodCongr (Equiv.refl V), p.prodCongr (Equiv.refl E), fun _ => rfl, fun _ => rfl⟩

theorem faithful (H : OrientedGraph V E) [Nonempty V] (d : ℕ) :
    Function.Injective (fun p : Equiv.Perm (Fin d) => (rotation H p).vertex) := by
  intro p q h
  apply Equiv.ext
  intro i
  exact congrArg (fun e : Equiv.Perm (Fin d × V) => (e (i,Classical.choice (inferInstance : Nonempty V))).1) h

variable [Fintype E] [DecidableEq V] (H : OrientedGraph V E)
variable (A : Type) [AddCommGroup A] (d : ℕ)

theorem kirchhoff_iff (f : Fin d × E → A) :
    Kirchhoff (copies H d) f ↔ ∀ i, Kirchhoff H (fun e => f (i,e)) := by
  simp only [Kirchhoff, copies, Prod.forall, FlowDouble.tagged_sum]

/-- Component restriction is a bijection on actual nowhere-zero flows. -/
def split : Flow (copies H d) A ≃ (Fin d → Flow H A) where
  toFun f i := ⟨fun e => f.1 (i,e), fun e => f.2.1 (i,e), (kirchhoff_iff H A d f.1).1 f.2.2 i⟩
  invFun f := ⟨fun e => (f e.1).1 e.2, fun e => (f e.1).2.1 e.2,
    (kirchhoff_iff H A d _).2 (fun i => (f i).2.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem ordinary_count [Finite A] :
    Nat.card (Flow (copies H d) A) = Nat.card (Flow H A) ^ d := by
  rw [Nat.card_congr (split H A d), Nat.card_fun, show Nat.card (Fin d) = d by rw [Nat.card_eq_fintype_card, Fintype.card_fin]]

instance action : MulAction (Equiv.Perm (Fin d)) (Flow (copies H d) A) where
  smul p f := (split H A d).symm (fun i => split H A d f (p.symm i))
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem action_is_pullback (p : Equiv.Perm (Fin d)) (f : Flow (copies H d) A) (e : Fin d × E) :
    (p • f).1 e = f.1 ((rotation H p.symm).edge e) := rfl

abbrev Orbits := MulAction.orbitRel.Quotient (Equiv.Perm (Fin d)) (Flow (copies H d) A)

private theorem fiber_size {X : Type} [DecidableEq X] (f : Fin d → X) (x : X) :
    Fintype.card {i // f i = x} = (↑(List.ofFn f) : Multiset X).count x := by
  rw [← Fin.univ_val_map, Multiset.count_map, ← Finset.filter_val]
  simp [Fintype.card_subtype, eq_comm]
  rfl

private theorem perm_reindex {X : Type} (f g : Fin d → X) (h : (List.ofFn f).Perm (List.ofFn g)) :
    ∃ p : Equiv.Perm (Fin d), ∀ i, g (p i) = f i := by
  classical
  have hm : (↑(List.ofFn f) : Multiset X) = ↑(List.ofFn g) := Quot.sound h
  have hc (x : X) : Fintype.card {i // f i = x} = Fintype.card {i // g i = x} := by
    rw [fiber_size, fiber_size, hm]
  let e (x : X) := Fintype.equivOfCardEq (hc x)
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

private def vectorEquiv : Flow (copies H d) A ≃ List.Vector (Flow H A) d :=
  (split H A d).trans (Equiv.vectorEquivFin _ _).symm

/-- Two ordered collections are in the same graph-action orbit exactly when
their multisets of component flows agree. -/
noncomputable def orbitsEquiv : Orbits H A d ≃ Sym (Flow H A) d := by
  apply Equiv.trans _ Sym.symEquivSym'.symm
  apply Quotient.congr (vectorEquiv H A d)
  intro f g
  change (MulAction.orbitRel (Equiv.Perm (Fin d)) _ f g) ↔
    (List.Vector.ofFn (split H A d f)).toList.Perm (List.Vector.ofFn (split H A d g)).toList
  simp only [List.Vector.toList_ofFn]
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨p,rfl⟩
    exact Equiv.Perm.ofFn_comp_perm p.symm (split H A d g)
  · intro h
    obtain ⟨p,hp⟩ := perm_reindex d (split H A d f) (split H A d g) h
    refine ⟨p.symm, (split H A d).injective (funext hp)⟩

/-- The coefficient group may be any finite abelian group. -/
theorem orbit_count [Finite A] :
    Nat.card (Orbits H A d) = Nat.multichoose (Nat.card (Flow H A)) d := by
  classical
  letI : Fintype (Flow H A) := Fintype.ofFinite _
  rw [Nat.card_congr (orbitsEquiv H A d), Nat.card_eq_fintype_card,
    Sym.card_sym_eq_multichoose, Nat.card_eq_fintype_card]

theorem factorial_mul_orbit_count [Finite A] :
    d.factorial * Nat.card (Orbits H A d) = ∏ i ∈ Finset.range d, (Nat.card (Flow H A) + i) := by
  rw [orbit_count, Nat.multichoose_eq, ← Nat.ascFactorial_eq_factorial_mul_choose',
    Nat.ascFactorial_eq_prod_range]

end CameronKayibi.FlowCopies
