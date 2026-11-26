import Conjectures.FlowBouquet
import Conjectures.FlowGadget
import Conjectures.FlowLadder

namespace CameronKayibi.FlowGraph
open FlowBouquet (underlying)

theorem edge_reachable {V E : Type} (H : OrientedGraph V E) (e : E) :
    (underlying H).Reachable (H.tail e) (H.head e) := by
  by_cases he : H.tail e = H.head e
  · rw [he]
  · exact (show (underlying H).Adj (H.tail e) (H.head e) from ⟨he,e,Or.inl ⟨rfl,rfl⟩⟩).reachable

theorem gadget_connected (m k : ℕ) : (underlying (gadget m k)).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).2
  refine ⟨0,?_⟩
  intro v
  induction v using Fin.induction with
  | zero => exact SimpleGraph.Reachable.rfl
  | succ i ih => exact ih.trans (edge_reachable (gadget m k) (.inr (.inr (i,false))))

theorem ladder_connected (s : ℕ) : (underlying (Ladder.graph s)).Connected := by
  let G := Ladder.graph s
  let start : Ladder.Vertex s := .inl false
  let pos (b : Bool) : Fin (s+1) → Ladder.Vertex s := Fin.cases start (fun i => .inr (i,b))
  have hpath (b : Bool) (j : Fin (s+1)) : (underlying G).Reachable start (pos b j) := by
    induction j using Fin.induction with
    | zero => exact SimpleGraph.Reachable.rfl
    | succ i ih =>
      apply ih.trans
      have he := edge_reachable G (.inr (.inl (i.castSucc,b)))
      change (underlying G).Reachable (pos b i.castSucc) (Fin.lastCases (.inl true) (fun j => .inr (j,b)) i.castSucc) at he
      simpa [pos] using he
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).2
  refine ⟨start,?_⟩
  rintro ((_|_) | ⟨i,b⟩)
  · exact SimpleGraph.Reachable.rfl
  · exact (edge_reachable G (.inl ())).symm
  · exact hpath b i.succ

end CameronKayibi.FlowGraph
