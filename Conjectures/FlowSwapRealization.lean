import Conjectures.FlowLoops
import Conjectures.FlowConnected
import Conjectures.FlowSubdivision
import Conjectures.FlowSwapDisk

namespace CameronKayibi.Flow.SwapDisk

open FlowGraph Polynomial

abbrev ladder (m s : ℕ) := Loops.graph (Ladder.graph s) (.inl false) m

noncomputable def polynomial (m s : ℕ) : Polynomial ℂ :=
  (X-1)*(X-2)*(X-1)^m*(X-3)^s

@[simp] theorem eval_polynomial (m s : ℕ) (z : ℂ) :
    (polynomial m s).eval z = ordinary m s z := by simp [polynomial,ordinary]

theorem base_count (m s : ℕ) (A : Type) [AddCommGroup A] [Fintype A] :
    (polynomial m s).eval (Fintype.card A : ℂ) = Nat.card (Flow (ladder m s) A) := by
  rw [Loops.card_flow,Ladder.card_flow,eval_polynomial]
  have hq : 0 < Fintype.card A := Fintype.card_pos
  cases h : Fintype.card A with
  | zero => omega
  | succ q =>
    cases q with
    | zero => simp [ordinary]
    | succ q =>
      cases q with
      | zero => simp [ordinary]
      | succ q =>
        simp [ordinary,Nat.succ_eq_add_one]
        ring

theorem connected (m s : ℕ) : (FlowBouquet.underlying (ladder m s)).Connected := by
  let hom : FlowBouquet.underlying (Ladder.graph s) →g FlowBouquet.underlying (ladder m s) := {
    toFun := id
    map_rel' := by
      rintro a b ⟨hab,e,he⟩
      exact ⟨hab,.inl e,he⟩ }
  obtain ⟨o,ho⟩ := (SimpleGraph.connected_iff_exists_forall_reachable _).mp (ladder_connected s)
  exact (SimpleGraph.connected_iff_exists_forall_reachable _).mpr ⟨o,fun v => (ho v).map hom⟩

/-- The same ordinary polynomial counts flows on the simple, connected
subdivision of the ladder with extra loops. -/
theorem simple_base_count (m s : ℕ) (A : Type) [AddCommGroup A] [Fintype A] :
    (polynomial m s).eval (Fintype.card A : ℂ) =
        Nat.card (Flow (Subdivision.graph (ladder m s)) A) := by
  rw [base_count]
  norm_cast
  convert Nat.card_congr (Subdivision.flowEquiv (A:=A) (ladder m s)) using 2
  congr 1

set_option synthInstance.maxSize 512

/-- For the connected base, the polynomial counts actual orbits under
the symmetric group on two blocks. Its action interchanges two copies of the
bouquet composed of d copies of the base graph. -/
theorem swap_count (m s d : ℕ) (A : Type) [AddCommGroup A] [Fintype A] :
    (FlowCopies.orbitPolynomial (polynomial m s) d 2).eval (Fintype.card A : ℂ) =
    Nat.card (FlowBouquet.Orbits (FlowBouquet.graph (ladder m s) (.inl false) d) none A 2) := by
  exact FlowBouquet.eval_counts (ladder m s) (.inl false) A d (polynomial m s) 2 (base_count m s A)

theorem swap_connected (m s d : ℕ) :
    (FlowBouquet.underlying (FlowBouquet.graph
      (FlowBouquet.graph (ladder m s) (.inl false) d) none 2)).Connected :=
  FlowBouquet.connected _ _ _ (FlowBouquet.connected _ _ _
    (connected m s))

/-- In every neighborhood inside the disk there is a complex zero of
one of these connected-graph, fixed-involution orbital flow polynomials. -/
theorem exists_root {z : ℂ} (hz₁ : ‖z-1‖ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ m s d : ℕ, 0 < d ∧ ∃ w : ℂ, dist z w < ε ∧
      (FlowCopies.orbitPolynomial (polynomial m s) d 2).eval w = 0 := by
  by_cases he : z = 1
  · subst z
    refine ⟨0,0,1,by decide,1,by simpa using hε,
      FlowCopies.root_of_value _ _ _ (j:=0) (by decide) ?_⟩
    simp [ordinary]
  have hz₀ : 0 < ‖z-1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  obtain ⟨w,⟨m,s,d,hd,hw⟩,hdist⟩ := Metric.mem_closure_iff.mp (mem_closure hz₀ hz₁) ε hε
  refine ⟨m,s,d,hd,w,hdist,FlowCopies.root_of_value _ _ _ (j:=1) (by decide) ?_⟩
  simpa using hw

end CameronKayibi.Flow.SwapDisk
