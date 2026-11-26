import Conjectures.FlowSwapRealization
import Conjectures.FlowComplexTargets

/-! A self-contained complex density proof using connected graphs with symmetric
groups permuting identical rooted blocks. The open disk uses a single swap.
Outside the disk, a cycle and roots of negative integers suffice. -/
namespace CameronKayibi.Flow.Plane
open Polynomial FlowGraph

/-- The edge incidences of a finite oriented graph, with a distinguished root
and an ordinary polynomial that counts all nowhere-zero flows. -/
structure Block where
  V : Type
  E : Type
  [finV : Fintype V]
  [finE : Fintype E]
  [decV : DecidableEq V]
  [decE : DecidableEq E]
  edge : E
  graph : OrientedGraph V E
  root : V
  connected : (FlowBouquet.underlying graph).Connected
  poly : Polynomial ℂ
  counts : ∀ (A : Type) [AddCommGroup A] [Fintype A],
    poly.eval (Fintype.card A : ℂ) = Nat.card (Flow graph A)
  at_four : ∃ t : ℕ, 0 < t ∧ poly.eval 4 = (t : ℂ)

attribute [instance] Block.finV Block.finE Block.decV Block.decE

set_option synthInstance.maxSize 1024

/-- Subdivide every edge twice before joining copies at a common vertex. -/
abbrev model (B : Block) (d : ℕ) :=
  FlowBouquet.graph (Subdivision.graph B.graph) (.inl B.root) d

abbrev witnessGraph (B : Block) (d N : ℕ) := FlowBouquet.graph (model B d) none N

/-- The orbital polynomial counts orbits of the actual currents for all groups,
including groups whose orders share factors with the symmetry group. -/
theorem counts (B : Block) (d N : ℕ) (A : Type) [AddCommGroup A] [Fintype A] :
    (FlowCopies.orbitPolynomial B.poly d N).eval (Fintype.card A : ℂ) =
      Nat.card (FlowBouquet.Orbits (model B d) none A N) := by
  apply FlowBouquet.eval_counts
  rw [B.counts A]
  exact_mod_cast Nat.card_congr (Subdivision.flowEquiv (A:=A) B.graph)

theorem connected (B : Block) (d N : ℕ) :
    (FlowBouquet.underlying (witnessGraph B d N)).Connected :=
  FlowBouquet.connected _ _ _ (FlowBouquet.connected _ _ _ (Subdivision.connected _ B.connected))

theorem loopless (B : Block) (d N : ℕ) : ∀ e,
    (witnessGraph B d N).tail e ≠ (witnessGraph B d N).head e :=
  FlowBouquet.tail_ne_head _ _ _ (FlowBouquet.tail_ne_head _ _ _ (Subdivision.tail_ne_head _))

theorem simple (B : Block) (d N : ℕ) {e f} (h :
    ((witnessGraph B d N).tail e = (witnessGraph B d N).tail f ∧
     (witnessGraph B d N).head e = (witnessGraph B d N).head f) ∨
    ((witnessGraph B d N).tail e = (witnessGraph B d N).head f ∧
     (witnessGraph B d N).head e = (witnessGraph B d N).tail f)) : e = f := by
  exact FlowBouquet.edge_unique (model B d) none N
    (FlowBouquet.tail_ne_head _ _ _ (Subdivision.tail_ne_head B.graph))
    (FlowBouquet.edge_unique _ _ _ (Subdivision.tail_ne_head B.graph) (Subdivision.edge_unique B.graph)) h

/-- Permutations of the copies act faithfully on the edges. -/
theorem faithful (B : Block) {d : ℕ} (hd : 0 < d) (N : ℕ) :
    Function.Injective (fun p : Equiv.Perm (Fin N) => (FlowBouquet.rotation (model B d) none N p).edge) := by
  intro p q hp
  apply Equiv.ext
  intro i
  let e : Fin d × Subdivision.Edge B.E := (⟨0,hd⟩, .inl B.edge)
  exact congrArg (fun g : Equiv.Perm (Fin N × Fin d × Subdivision.Edge B.E) => (g (i,e)).1) hp

theorem nonzero (B : Block) (d N : ℕ) : FlowCopies.orbitPolynomial B.poly d N ≠ 0 := by
  obtain ⟨t,ht,hv⟩ := B.at_four
  intro h
  have he := congrArg (Polynomial.eval (4:ℂ)) h
  rw [FlowCopies.eval_orbitPolynomial, hv, Polynomial.eval_zero] at he
  apply (mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr N.factorial_ne_zero)) _) he
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact_mod_cast (show t^d+i ≠ 0 by have := pow_pos ht d; omega)

noncomputable def cycle : Block where
  V := Fin 1
  E := GadgetEdge 0 0
  finV := inferInstance
  finE := inferInstance
  decV := inferInstance
  decE := inferInstance
  edge := .inr (.inl ())
  graph := gadget 0 0
  root := 0
  connected := gadget_connected 0 0
  poly := X - 1
  counts A _ _ := by
    rw [card_flow_gadget]
    have hq : 1 ≤ Fintype.card A := Fintype.card_pos
    simp [Nat.cast_sub hq]
  at_four := ⟨3, by decide, by norm_num⟩

noncomputable def ladderBlock (m s : ℕ) : Block where
  V := Ladder.Vertex s
  E := _
  finV := inferInstance
  finE := inferInstance
  decV := inferInstance
  decE := inferInstance
  edge := .inl (.inl ())
  graph := SwapDisk.ladder m s
  root := .inl false
  connected := SwapDisk.connected m s
  poly := SwapDisk.polynomial m s
  counts A _ _ := SwapDisk.base_count m s A
  at_four := ⟨3*2*3^m, by positivity, by simp [SwapDisk.ordinary]; norm_num⟩

/-- Roots of a concrete family of nonzero, graph-realized orbital polynomials. -/
def roots : Set ℂ := {z | ∃ (B : Block) (d N : ℕ), 0 < d ∧ 2 ≤ N ∧
  (FlowCopies.orbitPolynomial B.poly d N).IsRoot z}

/-- The whole complex plane is the closure of actual orbital flow roots. -/
theorem dense_orbital_flow_roots : Dense roots := by
  have inside : Metric.ball (1:ℂ) 1 ⊆ closure roots := by
    intro z hz
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨m,s,d,hd,w,hn,hw⟩ := SwapDisk.exists_root (by simpa [Metric.mem_ball,dist_eq_norm] using hz) hε
    exact ⟨w,⟨ladderBlock m s,d,2,hd,by decide,hw⟩,hn⟩
  have closedInside : Metric.closedBall (1:ℂ) 1 ⊆ closure roots := by
    rw [← closure_ball (1:ℂ) (one_ne_zero : (1:ℝ) ≠ 0)]
    exact closure_minimal inside isClosed_closure
  intro z
  by_cases hz : ‖z-1‖ ≤ 1
  · exact closedInside (by simpa [Metric.mem_closedBall,dist_eq_norm] using hz)
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨y,⟨d,j,hd,hy⟩,hnear⟩ := Metric.mem_closure_iff.mp
    (mem_closure_powerTargets (lt_of_not_ge hz)) ε hε
  refine ⟨y+1,⟨cycle,d,j+2,hd,by omega,?_⟩,?_⟩
  · apply FlowCopies.root_of_value _ _ _ (j:=j) (by omega)
    simpa [cycle] using hy
  · simpa [dist_eq_norm,sub_add_eq_sub_sub,sub_right_comm] using hnear

end CameronKayibi.Flow.Plane
