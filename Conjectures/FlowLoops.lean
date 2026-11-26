import Conjectures.FlowGraph
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card

namespace CameronKayibi.FlowGraph.Loops

variable {V E A : Type}

/-- Add m independent loops at one specified vertex. -/
def graph (G : OrientedGraph V E) (o : V) (m : ℕ) : OrientedGraph V (E ⊕ Fin m) where
  tail := Sum.elim G.tail (fun _ => o)
  head := Sum.elim G.head (fun _ => o)

variable [Fintype E] [DecidableEq V] [AddCommGroup A]
variable (G : OrientedGraph V E) (o : V) (m : ℕ)

theorem kirchhoff_iff (f : E ⊕ Fin m → A) :
    Kirchhoff (graph G o m) f ↔ Kirchhoff G (fun e => f (.inl e)) := by
  simp [Kirchhoff,graph,Fintype.sum_sum_type]

private def flowEquiv : Flow (graph G o m) A ≃ (Flow G A × (Fin m → {a : A // a ≠ 0})) where
  toFun f := (⟨fun e => f.1 (.inl e),fun _ => f.2.1 _,(kirchhoff_iff G o m _).mp f.2.2⟩,
      fun e => ⟨f.1 (.inr e),f.2.1 _⟩)
  invFun p := ⟨Sum.elim p.1.1 (fun e => (p.2 e).1),by
    rintro (e|e)
    · exact p.1.2.1 e
    · exact (p.2 e).2,
    (kirchhoff_iff G o m _).mpr p.1.2.2⟩
  left_inv f := by
    apply Subtype.ext; funext e; cases e <;> rfl
  right_inv _ := rfl

theorem card_flow (A : Type) [AddCommGroup A] [Fintype A] :
    Nat.card (Flow (graph G o m) A) = Nat.card (Flow G A) * (Fintype.card A - 1)^m := by
  classical
  rw [Nat.card_congr (flowEquiv (A:=A) G o m),Nat.card_prod,Nat.card_fun]
  have hn : Fintype.card {a : A // a ≠ 0} = Fintype.card A-1 := by
    change Fintype.card {a : A // ¬a = 0} = _
    rw [Fintype.card_subtype_compl]; simp
  simp [Nat.card_eq_fintype_card,hn]

end CameronKayibi.FlowGraph.Loops
