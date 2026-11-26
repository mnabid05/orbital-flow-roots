import Conjectures.FlowGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring

namespace CameronKayibi.FlowGraph

/-- The gadget has m loops at vertex zero, one edge returning to zero, and two
parallel edges in the forward direction at each of k consecutive stages. -/
abbrev GadgetEdge (m k : ℕ) := Fin m ⊕ (Unit ⊕ (Fin k × Bool))

def gadget (m k : ℕ) : OrientedGraph (Fin (k+1)) (GadgetEdge m k) where
  tail
    | .inl _ => 0
    | .inr (.inl ()) => Fin.last k
    | .inr (.inr (j,_)) => j.castSucc
  head
    | .inl _ => 0
    | .inr (.inl ()) => 0
    | .inr (.inr (j,_)) => j.succ

variable {m k : ℕ} {A : Type} [AddCommGroup A]

private abbrev returning (f : GadgetEdge m k → A) := f (.inr (.inl ()))
private abbrev first (f : GadgetEdge m k → A) (j : Fin k) := f (.inr (.inr (j,false)))
private abbrev second (f : GadgetEdge m k → A) (j : Fin k) := f (.inr (.inr (j,true)))
private def stage (f : GadgetEdge m k → A) (j : Fin k) := first f j + second f j

private theorem tail_sum (v : Fin (k+1)) (a : A) (t : Fin k → A) :
    (if Fin.last k = v then a else 0) + (∑ i, if i.castSucc = v then t i else 0) =
    Fin.lastCases (motive := fun _ => A) a t v := by
  have h := Fin.sum_univ_castSucc (fun i : Fin (k+1) => if i=v then Fin.lastCases (motive := fun _ => A) a t i else 0)
  simpa [add_comm] using h.symm

private theorem head_sum (v : Fin (k+1)) (a : A) (t : Fin k → A) :
    (if 0=v then a else 0) + (∑ i, if i.succ = v then t i else 0) = Fin.cases (motive := fun _ => A) a t v := by
  have h := Fin.sum_univ_succ (fun i : Fin (k+1) => if i=v then Fin.cases (motive := fun _ => A) a t i else 0)
  simpa using h.symm

private theorem local_balance (f : GadgetEdge m k → A) : Kirchhoff (gadget m k) f ↔
    ∀ v, Fin.lastCases (motive := fun _ => A) (returning f) (stage f) v = Fin.cases (motive := fun _ => A) (returning f) (stage f) v := by
  unfold Kirchhoff
  apply forall_congr'
  intro v
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool,
    gadget, add_right_inj]
  have merge (P : Prop) [Decidable P] (a b : A) :
      (if P then b else 0) + (if P then a else 0) = if P then a+b else 0 := by
    by_cases h : P <;> simp [h,add_comm]
  simp only [merge]
  change ((if Fin.last k=v then returning f else 0) + (∑ i, if i.castSucc=v then stage f i else 0) =
      (if 0=v then returning f else 0) + (∑ i, if i.succ=v then stage f i else 0)) ↔ _
  rw [tail_sum,head_sum]

/-- Conservation is exactly the requirement that every parallel pair has the
same total as the return edge. The loops balance independently at vertex zero. -/
theorem gadget_kirchhoff_iff (f : GadgetEdge m k → A) : Kirchhoff (gadget m k) f ↔
    ∀ j : Fin k, f (.inr (.inr (j,false))) + f (.inr (.inr (j,true))) = f (.inr (.inl ())) := by
  rw [local_balance]
  constructor
  · intro h
    have hall (v : Fin (k+1)) : Fin.lastCases (motive := fun _ => A) (returning f) (stage f) v = returning f := by
      induction v using Fin.induction with
      | zero => simpa using h 0
      | succ i ih =>
        have he := h i.succ
        simpa using he.trans (by simpa using ih)
    intro j
    simpa [stage] using hall j.castSucc
  · intro h v
    have eqfun : stage f = fun _ => returning f := funext h
    rw [eqfun]
    have hl : ∀ t : Fin (k+1), Fin.lastCases (motive := fun _ => A) (returning f) (fun _ => returning f) t = returning f :=
      by
        intro x
        induction x using Fin.lastCases <;> simp
    have hr : ∀ t : Fin (k+1), Fin.cases (motive := fun _ => A) (returning f) (fun _ => returning f) t = returning f :=
      by
        intro x
        induction x using Fin.cases <;> simp
    exact (hl v).trans (hr v).symm

private abbrev Nonzero (A : Type) [Zero A] := {a : A // a ≠ 0}
private abbrev Free (m k : ℕ) (A : Type) [Zero A] :=
  (Fin m → Nonzero A) × (Σ a : Nonzero A, Fin k → {x : Nonzero A // x ≠ a})

private def encode (f : Flow (gadget m k) A) : Free m k A := by
  let a : Nonzero A := ⟨returning f.1, f.2.1 _⟩
  refine ⟨fun j => ⟨f.1 (.inl j), f.2.1 _⟩,a,fun j => ⟨⟨first f.1 j,f.2.1 _⟩,?_⟩⟩
  intro he
  have h := (gadget_kirchhoff_iff f.1).mp f.2.2 j
  have he' : first f.1 j = returning f.1 := congrArg Subtype.val he
  change first f.1 j + second f.1 j = returning f.1 at h
  rw [he'] at h
  exact f.2.1 _ ((add_eq_left).mp h)

private def fromFree (d : Free m k A) : GadgetEdge m k → A
  | .inl j => (d.1 j).1
  | .inr (.inl ()) => d.2.1.1
  | .inr (.inr (j,false)) => (d.2.2 j).1.1
  | .inr (.inr (j,true)) => d.2.1.1 - (d.2.2 j).1.1

private def decode (d : Free m k A) : Flow (gadget m k) A := by
  refine ⟨fromFree d, ?_, (gadget_kirchhoff_iff _).mpr ?_⟩
  · rintro (j | (_ | ⟨j,_ | _⟩))
    · exact (d.1 j).2
    · exact d.2.1.2
    · exact (d.2.2 j).1.2
    · exact sub_ne_zero.mpr (fun he => (d.2.2 j).2 (Subtype.ext he.symm))
  · intro j
    change _ + (_ - _) = _
    exact (add_comm _ _).trans (sub_add_cancel _ _)

private def flowEquiv : Flow (gadget m k) A ≃ Free m k A where
  toFun := encode
  invFun := decode
  right_inv _ := rfl
  left_inv f := by
    apply Subtype.ext
    funext e
    rcases e with j | (_ | ⟨j,b⟩)
    · rfl
    · rfl
    · cases b
      · rfl
      · change returning f.1 - first f.1 j = second f.1 j
        have h := (gadget_kirchhoff_iff _).mp f.2.2 j
        change first f.1 j + second f.1 j = returning f.1 at h
        rw [← h, add_sub_cancel_left]

private theorem card_other {S : Type} [Fintype S] [DecidableEq S] (c : S) :
    Fintype.card {x : S // x ≠ c} = Fintype.card S - 1 := by
  change Fintype.card {x : S // ¬ x = c} = _
  rw [Fintype.card_subtype_compl]
  simp

/-- Exact number of nowhere-zero flows for every finite abelian coefficient group. -/
theorem card_flow_gadget (m k : ℕ) (A : Type) [AddCommGroup A] [Fintype A] :
    Nat.card (Flow (gadget m k) A) = (Fintype.card A-1)^(m+1)*(Fintype.card A-2)^k := by
  classical
  rw [Nat.card_congr (flowEquiv (m:=m) (k:=k) (A:=A)), Nat.card_eq_fintype_card]
  simp [Free, Nonzero, Fintype.card_prod, Fintype.card_sigma, Fintype.card_fun, card_other,
    Nat.sub_sub, pow_succ, Nat.mul_assoc]

end CameronKayibi.FlowGraph
