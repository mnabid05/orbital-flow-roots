import Conjectures.FlowBouquet
import Mathlib.Data.Fintype.BigOperators

namespace CameronKayibi.FlowGraph.Subdivision

variable {V E A : Type}

abbrev Vertex (V E : Type) := V ⊕ (E ⊕ E)
abbrev Edge (E : Type) := E ⊕ (E ⊕ E)

/-- Replace each edge with three edges along a path with fresh intermediate vertices. -/
def graph (G : OrientedGraph V E) : OrientedGraph (Vertex V E) (Edge E) where
  tail
    | .inl e => .inl (G.tail e)
    | .inr (.inl e) => .inr (.inl e)
    | .inr (.inr e) => .inr (.inr e)
  head
    | .inl e => .inr (.inl e)
    | .inr (.inl e) => .inr (.inr e)
    | .inr (.inr e) => .inl (G.head e)

/-- Subdivision removes loops even when an original edge was a loop. -/
theorem tail_ne_head (G : OrientedGraph V E) (e : Edge E) :
    (graph G).tail e ≠ (graph G).head e := by
  rcases e with e | (e | e) <;> simp [graph]

/-- An unordered pair of endpoints determines at most one subdivided edge. -/
theorem edge_unique (G : OrientedGraph V E) {e e' : Edge E}
    (h : ((graph G).tail e = (graph G).tail e' ∧ (graph G).head e = (graph G).head e') ∨
         ((graph G).tail e = (graph G).head e' ∧ (graph G).head e = (graph G).tail e')) :
    e = e' := by
  rcases e with e | (e | e) <;> rcases e' with e' | (e' | e') <;> simp_all [graph]

open FlowBouquet (underlying)

/-- Subdivision preserves connectedness of the underlying undirected graph. -/
theorem connected (G : OrientedGraph V E) (h : (underlying G).Connected) :
    (underlying (graph G)).Connected := by
  obtain ⟨o,ho⟩ := (SimpleGraph.connected_iff_exists_forall_reachable _).mp h
  have segment (e : Edge E) :
      (underlying (graph G)).Reachable ((graph G).tail e) ((graph G).head e) :=
    SimpleGraph.Adj.reachable ⟨tail_ne_head G e,e,Or.inl ⟨rfl,rfl⟩⟩
  have follow (e : E) : (underlying (graph G)).Reachable (.inl (G.tail e)) (.inl (G.head e)) :=
    (segment (.inl e)).trans ((segment (.inr (.inl e))).trans (segment (.inr (.inr e))))
  have lift {a b : V} (p : (underlying G).Walk a b) :
      (underlying (graph G)).Reachable (.inl a) (.inl b) := by
    induction p with
    | nil => exact SimpleGraph.Reachable.rfl
    | cons h _ ih =>
      obtain ⟨_,e,⟨ha,hb⟩ | ⟨hb,ha⟩⟩ := h
      · exact (ha ▸ hb ▸ follow e).trans ih
      · exact (ha ▸ hb ▸ (follow e).symm).trans ih
  have atOriginal (v : V) : (underlying (graph G)).Reachable (.inl o) (.inl v) :=
    (ho v).elim lift
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨.inl o,?_⟩
  rintro (v | (e | e))
  · exact atOriginal v
  · exact (atOriginal (G.tail e)).trans (segment (.inl e))
  · exact (atOriginal (G.head e)).trans (segment (.inr (.inr e))).symm

variable [Fintype E] [DecidableEq V] [DecidableEq E] [AddCommGroup A]

/-- At each new vertex the two currents agree; at an original vertex Kirchhoff's
equation compares currents at the two original ends. -/
private theorem local_iff (G : OrientedGraph V E) (f : Edge E → A) :
    Kirchhoff (graph G) f ↔
    (∀ v, (∑ e : E, if G.tail e = v then f (.inl e) else 0) =
       ∑ e : E, if G.head e = v then f (.inr (.inr e)) else 0) ∧
    (∀ e, f (.inr (.inl e)) = f (.inl e)) ∧
    (∀ e, f (.inr (.inr e)) = f (.inr (.inl e))) := by
  simp [Kirchhoff, graph, Fintype.sum_sum_type, Sum.forall]

/-- The flow correspondence commutes with any relabeling of edges, since it
simply copies each original current to its three successive edges. -/
def flowEquiv (G : OrientedGraph V E) : Flow G A ≃ Flow (graph G) A where
  toFun f := ⟨Sum.elim f.1 (Sum.elim f.1 f.1),by
    rintro (e | (e | e)) <;> exact f.2.1 e,
    (local_iff G _).mpr ⟨f.2.2,fun _ => rfl,fun _ => rfl⟩⟩
  invFun f := ⟨fun e => f.1 (.inl e),fun e => f.2.1 _,by
    obtain ⟨h,h₁,h₂⟩ := (local_iff G f.1).mp f.2.2
    simpa [Kirchhoff,h₁,h₂] using h⟩
  left_inv _ := rfl
  right_inv f := by
    apply Subtype.ext
    funext e
    obtain ⟨_,h₁,h₂⟩ := (local_iff G f.1).mp f.2.2
    rcases e with e | (e | e)
    · rfl
    · exact (h₁ _).symm
    · exact ((h₂ _).trans (h₁ _)).symm

end CameronKayibi.FlowGraph.Subdivision
