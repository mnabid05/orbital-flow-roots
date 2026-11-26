import Conjectures.FlowGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel

namespace CameronKayibi.FlowGraph

namespace Ladder

/-- Two end vertices, with an upper and a lower vertex at every internal level. -/
abbrev Vertex (s : ℕ) := Bool ⊕ (Fin s × Bool)

/-- One return edge, two horizontal rails, and a rung at every internal level. -/
abbrev Edge (s : ℕ) := Unit ⊕ ((Fin (s+1) × Bool) ⊕ Fin s)

variable {s : ℕ} {A : Type} [AddCommGroup A]

private def railTail (j : Fin (s+1)) (b : Bool) : Vertex s :=
  Fin.cases (.inl false) (fun i => .inr (i,b)) j

private def railHead (j : Fin (s+1)) (b : Bool) : Vertex s :=
  Fin.lastCases (.inl true) (fun i => .inr (i,b)) j

def graph (s : ℕ) : OrientedGraph (Vertex s) (Edge s) where
  tail
    | .inl () => .inl true
    | .inr (.inl (j,b)) => railTail j b
    | .inr (.inr i) => .inr (i,false)
  head
    | .inl () => .inl false
    | .inr (.inl (j,b)) => railHead j b
    | .inr (.inr i) => .inr (i,true)

private abbrev ret (f : Edge s → A) := f (.inl ())
private abbrev upper (f : Edge s → A) (j : Fin (s+1)) := f (.inr (.inl (j,false)))
private abbrev lower (f : Edge s → A) (j : Fin (s+1)) := f (.inr (.inl (j,true)))
private abbrev rung (f : Edge s → A) (j : Fin s) := f (.inr (.inr j))

private def outgoingRail (f : Edge s → A) : Vertex s → A
  | .inl false => upper f 0 + lower f 0
  | .inl true => 0
  | .inr (i,b) => f (.inr (.inl (i.succ,b)))

private def incomingRail (f : Edge s → A) : Vertex s → A
  | .inl false => 0
  | .inl true => upper f (Fin.last s) + lower f (Fin.last s)
  | .inr (i,b) => f (.inr (.inl (i.castSucc,b)))

private theorem sum_tail (v : Vertex s) (f : Edge s → A) :
    (∑ j : Fin (s+1), ∑ b : Bool, if railTail j b = v then f (.inr (.inl (j,b))) else 0) =
      outgoingRail f v := by
  rw [Fin.sum_univ_succ]
  rcases v with (_ | _) | ⟨i,_ | _⟩ <;>
    simp [railTail,Fintype.sum_bool,outgoingRail,add_comm]

private theorem sum_head (v : Vertex s) (f : Edge s → A) :
    (∑ j : Fin (s+1), ∑ b : Bool, if railHead j b = v then f (.inr (.inl (j,b))) else 0) =
      incomingRail f v := by
  rw [Fin.sum_univ_castSucc]
  rcases v with (_ | _) | ⟨i,_ | _⟩ <;>
    simp [railHead,Fintype.sum_bool,incomingRail,add_comm]

private theorem local_iff (f : Edge s → A) : Kirchhoff (graph s) f ↔
    upper f 0 + lower f 0 = ret f ∧
    ret f = upper f (Fin.last s) + lower f (Fin.last s) ∧
    (∀ i : Fin s, upper f i.succ + rung f i = upper f i.castSucc) ∧
    (∀ i : Fin s, lower f i.succ = lower f i.castSucc + rung f i) := by
  unfold Kirchhoff
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_unique, graph]
  simp only [sum_tail, sum_head]
  constructor
  · intro h
    refine ⟨?_,?_,?_,?_⟩
    · simpa [outgoingRail,incomingRail] using h (.inl false)
    · simpa [outgoingRail,incomingRail] using h (.inl true)
    · intro i
      simpa [outgoingRail,incomingRail] using h (.inr (i,false))
    · intro i
      simpa [outgoingRail,incomingRail] using h (.inr (i,true))
  · rintro ⟨h₀,h₁,hu,hl⟩ ( ( _ | _ ) | ⟨i, _ | _⟩ )
    · simpa [outgoingRail,incomingRail] using h₀
    · simpa [outgoingRail,incomingRail] using h₁
    · simpa [outgoingRail,incomingRail] using hu i
    · simpa [outgoingRail,incomingRail] using hl i

/-- The horizontal currents at every stage add to the return current. Each rung
carries the decrease in the upper current across that level. -/
theorem kirchhoff_iff (f : Edge s → A) : Kirchhoff (graph s) f ↔
    (∀ i : Fin (s+1), upper f i + lower f i = ret f) ∧
    (∀ i : Fin s, rung f i = upper f i.castSucc - upper f i.succ) := by
  rw [local_iff]
  constructor
  · rintro ⟨h₀,_,hu,hl⟩
    refine ⟨?_,?_⟩
    · intro j
      induction j using Fin.induction with
      | zero => exact h₀
      | succ i ih => rw [hl i, ← ih, ← hu i]; abel
    · intro i
      rw [← hu i]; abel
  · rintro ⟨ht,hr⟩
    refine ⟨ht 0,(ht _).symm,?_,?_⟩
    · intro i
      rw [hr i]; abel
    · intro i
      have hl (j : Fin (s+1)) : lower f j = ret f - upper f j := by rw [← ht j]; abel
      rw [hl,hl,hr]; abel


private abbrev Nonzero (A : Type) [Zero A] := {a : A // a ≠ 0}

private abbrev Other {X : Type} (a : X) := {x : X // x ≠ a}

/-- Sequences on the horizontal stages with distinct consecutive entries. -/
private abbrev Walk (s : ℕ) (X : Type) :=
  {x : Fin (s+1) → X // ∀ i : Fin s, x i.castSucc ≠ x i.succ}

private abbrev Free (s : ℕ) (A : Type) [Zero A] := Σ a : Nonzero A, Walk s (Other a)

private def encode (f : Flow (graph s) A) : Free s A := by
  let a : Nonzero A := ⟨ret f.1, f.2.1 _⟩
  have ht := ((kirchhoff_iff f.1).mp f.2.2).1
  have hr := ((kirchhoff_iff f.1).mp f.2.2).2
  let x (j : Fin (s+1)) : Other a := ⟨⟨upper f.1 j, f.2.1 _⟩,by
    intro h
    have ha : upper f.1 j = ret f.1 := congrArg Subtype.val h
    have hsum := ht j
    rw [ha] at hsum
    exact f.2.1 _ ((add_eq_left).mp hsum)⟩
  refine ⟨a,x,?_⟩
  intro i h
  have he : upper f.1 i.castSucc = upper f.1 i.succ := congrArg (fun z : Other a => z.1.1) h
  exact f.2.1 _ (by simpa [he] using hr i)

private def fromFree (d : Free s A) : Edge s → A
  | .inl () => d.1.1
  | .inr (.inl (j,false)) => (d.2.1 j).1.1
  | .inr (.inl (j,true)) => d.1.1 - (d.2.1 j).1.1
  | .inr (.inr i) => (d.2.1 i.castSucc).1.1 - (d.2.1 i.succ).1.1

private def decode (d : Free s A) : Flow (graph s) A := by
  refine ⟨fromFree d, ?_, (kirchhoff_iff _).mpr ⟨?_,?_⟩⟩
  · rintro (_ | (⟨j,_ | _⟩ | i))
    · exact d.1.2
    · exact (d.2.1 j).1.2
    · exact sub_ne_zero.mpr (fun h => (d.2.1 j).2 (Subtype.ext h.symm))
    · exact sub_ne_zero.mpr (fun h => d.2.2 i (Subtype.ext (Subtype.ext h)))
  · intro j
    change (d.2.1 j).1.1 + (d.1.1 - (d.2.1 j).1.1) = d.1.1
    abel
  · intro i
    rfl

private def flowEquiv : Flow (graph s) A ≃ Free s A where
  toFun := encode
  invFun := decode
  right_inv _ := rfl
  left_inv f := by
    apply Subtype.ext
    funext e
    obtain ⟨ht,hr⟩ := (kirchhoff_iff f.1).mp f.2.2
    rcases e with _ | (⟨j,_ | _⟩ | i)
    · rfl
    · rfl
    · change ret f.1 - upper f.1 j = lower f.1 j
      rw [← ht j]; abel
    · exact (hr i).symm

private def walkZero (X : Type) : Walk 0 X ≃ X where
  toFun w := w.1 0
  invFun x := ⟨fun _ => x,Fin.elim0⟩
  right_inv _ := rfl
  left_inv w := by
    apply Subtype.ext
    funext i
    apply congrArg w.1
    apply Fin.ext
    have hi := i.isLt
    simp only [Fin.val_zero]
    omega

private def walkStep (s : ℕ) (X : Type) :
    Walk (s+1) X ≃ Σ w : Walk s X, Other (w.1 0) where
  toFun z := ⟨⟨fun j => z.1 j.succ,fun i => z.2 i.succ⟩,⟨z.1 0,z.2 0⟩⟩
  invFun d := ⟨Fin.cons d.2.1 d.1.1,by
    intro j
    induction j using Fin.cases with
    | zero => exact d.2.2
    | succ i => exact d.1.2 i⟩
  right_inv _ := rfl
  left_inv z := by
    apply Subtype.ext
    funext j
    induction j using Fin.cases <;> rfl

private theorem card_other {X : Type} [Fintype X] [DecidableEq X] (a : X) :
    Fintype.card (Other a) = Fintype.card X - 1 := by
  change Fintype.card {x : X // ¬ x = a} = _
  rw [Fintype.card_subtype_compl]
  simp

private theorem card_walk (s : ℕ) (X : Type) [Fintype X] [DecidableEq X] :
    Fintype.card (Walk s X) = Fintype.card X * (Fintype.card X - 1)^s := by
  classical
  induction s with
  | zero => simpa using Fintype.card_congr (walkZero X)
  | succ s ih =>
    rw [Fintype.card_congr (walkStep s X),Fintype.card_sigma]
    simp [card_other,ih,pow_succ,Nat.mul_assoc]

/-- The return current excludes one value, the initial upper current excludes
two, and each subsequent upper current excludes three. This count applies to
every finite abelian group, including the small orders by natural subtraction. -/
theorem card_flow (s : ℕ) (A : Type) [AddCommGroup A] [Fintype A] :
    Nat.card (Flow (graph s) A) =
      (Fintype.card A-1)*(Fintype.card A-2)*(Fintype.card A-3)^s := by
  classical
  rw [Nat.card_congr (flowEquiv (s:=s) (A:=A)),Nat.card_eq_fintype_card]
  simp [Free,Nonzero,Fintype.card_sigma,card_walk,card_other,Nat.sub_sub,Nat.mul_assoc]

end Ladder
end CameronKayibi.FlowGraph
