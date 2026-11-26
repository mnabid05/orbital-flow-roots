import Conjectures.FlowConnected
import Conjectures.FlowSubdivision
import Conjectures.OrbitalFlowDensity
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Polynomial.Roots

/-! Real zeros of univariate orbital flow polynomials on the unit interval.
The coefficient group used to count flows can be any finite abelian group.
The graph action in every witness is permutation of two rooted copies. -/
namespace CameronKayibi.OrbitalFlowTheorem

open FlowGraph

set_option synthInstance.maxSize 1024

abbrev BaseVertex (m k : ℕ) := Subdivision.Vertex (Fin (k+1)) (GadgetEdge m k)
abbrev BaseEdge (m k : ℕ) := Subdivision.Edge (GadgetEdge m k)
abbrev subdivided (m k : ℕ) := Subdivision.graph (gadget m k)
abbrev root (m k : ℕ) : BaseVertex m k := .inl 0
abbrev Vertex (m k : ℕ) := FlowBouquet.Vertex (root m k) 2
abbrev Edge (m k : ℕ) := Fin 2 × BaseEdge m k
abbrev graph (m k : ℕ) : OrientedGraph (Vertex m k) (Edge m k) :=
  FlowBouquet.graph (subdivided m k) (root m k) 2
abbrev automorphism (m k : ℕ) (p : Equiv.Perm (Fin 2)) :=
  FlowBouquet.rotation (subdivided m k) (root m k) 2 p
abbrev Orbits (m k : ℕ) (A : Type) [AddCommGroup A] :=
  FlowBouquet.Orbits (subdivided m k) (root m k) A 2

/-- The action on edge assignments is pullback by the exhibited graph automorphism. -/
def Pullback {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedGraph V E) (o : V) : Prop :=
  ∀ (A : Type) [AddCommGroup A] (p : Equiv.Perm (Fin 2)) (f : Flow (FlowBouquet.graph G o 2) A) e,
    (p • f).1 e = f.1 ((FlowBouquet.rotation G o 2 p.symm).edge e)

/-- Each witness records the graph-theoretic and orbit-counting assertions for
the displayed graph and polynomial. The edge and vertex types are finite types
inferred directly from the construction. -/
structure Realization (m k : ℕ) (P : Polynomial ℝ) : Prop where
  nonzero : P ≠ 0
  connected : (FlowBouquet.underlying (graph m k)).Connected
  loopless : ∀ e, (graph m k).tail e ≠ (graph m k).head e
  edge_unique : ∀ {e f}, ((graph m k).tail e=(graph m k).tail f ∧ (graph m k).head e=(graph m k).head f) ∨
    ((graph m k).tail e=(graph m k).head f ∧ (graph m k).head e=(graph m k).tail f) → e=f
  group_order : Fintype.card (Equiv.Perm (Fin 2)) = 2
  faithful : Function.Injective (fun p : Equiv.Perm (Fin 2) => (automorphism m k p).vertex)
  pullback : Pullback (subdivided m k) (root m k)
  counts : ∀ (A : Type) [AddCommGroup A] [Fintype A],
    P.eval (Fintype.card A : ℝ) = Nat.card (Orbits m k A)

private theorem positive_at_three (m k : ℕ) : Flow.polynomial (m+1) k ≠ 0 := by
  intro h
  have he := congrArg (Polynomial.eval (3:ℝ)) h
  rw [Flow.eval_polynomial, Polynomial.eval_zero] at he
  unfold Flow.value Flow.base at he
  norm_num at he
  have hn : (0:ℝ) < 2^(m+1)+1 := by positivity
  exact hn.ne' he

private theorem faithful (m k : ℕ) :
    Function.Injective (fun p : Equiv.Perm (Fin 2) => (automorphism m k p).vertex) := by
  let u : {v : BaseVertex m k // v ≠ root m k} := ⟨.inr (.inl (.inr (.inl ()))),by intro h; cases h⟩
  intro p q hp
  apply Equiv.ext
  intro i
  have hh := congrArg (fun v : Equiv.Perm (Vertex m k) => v (some (i,u))) hp
  change some (p i,u) = some (q i,u) at hh
  exact congrArg Prod.fst (Option.some.inj hh)

private theorem base_count (m k : ℕ) (A : Type) [AddCommGroup A] [Fintype A] :
    Flow.base (m+1) k (Fintype.card A : ℝ) = Nat.card (Flow (subdivided m k) A) := by
  have he : Nat.card (Flow (subdivided m k) A) = Nat.card (Flow (gadget m k) A) := by
    convert Nat.card_congr (Subdivision.flowEquiv (A:=A) (gadget m k)).symm using 2
  rw [he, card_flow_gadget]
  have hq : 0 < Fintype.card A := Fintype.card_pos
  cases h : Fintype.card A with
  | zero => omega
  | succ q =>
    cases q with
    | zero => simp [Flow.base]
    | succ q =>
      simp [Flow.base,Nat.succ_eq_add_one]
      ring_nf
      simp

theorem counts (m k : ℕ) (A : Type) [AddCommGroup A] [Fintype A] :
    (Flow.polynomial (m+1) k).eval (Fintype.card A : ℝ) = Nat.card (Orbits m k A) := by
  have h := FlowCopies.factorial_mul_orbit_count (subdivided m k) A 2
  rw [← Nat.card_congr (FlowBouquet.orbitUnglue (subdivided m k) (root m k) A 2)] at h
  simp [Finset.prod_range_succ, Nat.factorial] at h
  have he := congrArg (Nat.cast : ℕ → ℝ) h
  push_cast at he
  rw [Flow.eval_polynomial,Flow.value,base_count]
  linarith only [he]

theorem realizes (m k : ℕ) : Realization m k (Flow.polynomial (m+1) k) where
  nonzero := positive_at_three m k
  connected := FlowBouquet.connected _ _ _ (Subdivision.connected _ (gadget_connected m k))
  loopless := FlowBouquet.tail_ne_head _ _ _ (Subdivision.tail_ne_head _)
  edge_unique := FlowBouquet.edge_unique _ _ _ (Subdivision.tail_ne_head _) (Subdivision.edge_unique _)
  group_order := by rw [Fintype.card_perm, Fintype.card_fin]; decide
  faithful := faithful m k
  pullback := fun A _ p f e => FlowBouquet.action_is_pullback (subdivided m k) (root m k) A 2 p f e
  counts := counts m k

/-- Cameron's problem 72(2): each nonempty open subinterval contains a
real root of a nonzero orbital flow polynomial of a connected simple graph
with a faithful two-element automorphism group and the stated counting interpretation. -/
theorem root_in_every_interval {l u : ℝ} (hl : 0 ≤ l) (hlt : l < u) (hu : u ≤ 1) :
    ∃ (m k : ℕ) (x : ℝ), l < x ∧ x < u ∧ (Flow.polynomial (m+1) k).eval x = 0 ∧
      Realization m k (Flow.polynomial (m+1) k) := by
  obtain ⟨a,b,x,hlx,hxu,hz⟩ := Flow.root_in_unit_interval hl hlt hu
  exact ⟨2*a,2*b,x,hlx,hxu,by simpa using hz,realizes _ _⟩

end CameronKayibi.OrbitalFlowTheorem
