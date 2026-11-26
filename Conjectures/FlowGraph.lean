import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! Finite oriented multigraphs and their nowhere-zero flows. Distinct edges may
have the same endpoints, and a loop contributes at both ends of the balance equation. -/
namespace CameronKayibi.FlowGraph

structure OrientedGraph (V E : Type) where
  tail : E → V
  head : E → V

variable {V E A : Type} [Fintype E] [DecidableEq V] [AddCommGroup A]

def Kirchhoff (G : OrientedGraph V E) (f : E → A) : Prop :=
  ∀ v : V, (∑ e : E, if G.tail e = v then f e else 0) =
    ∑ e : E, if G.head e = v then f e else 0

abbrev Flow (G : OrientedGraph V E) (A : Type) [AddCommGroup A] :=
  {f : E → A // (∀ e, f e ≠ 0) ∧ Kirchhoff G f}

end CameronKayibi.FlowGraph
