import Conjectures.FlowPlane
import Conjectures.FlowBundles
import Conjectures.FlowSokalExterior
import Conjectures.OrbitalFlowTheorem

/-! Density on the whole complex plane with a fixed group of order two.
The witnesses come from two explicit graph families. -/
namespace CameronKayibi.Flow.Plane
open Polynomial FlowGraph

noncomputable def bundleBlock (p s : ℕ) (hs : 0 < s) : Block where
  V := Fin (p+1)
  E := Fin (p+1) × Fin s
  finV := inferInstance
  finE := inferInstance
  decV := inferInstance
  decE := inferInstance
  edge := (0,⟨0,hs⟩)
  graph := Bundles.graph p s
  root := 0
  connected := Bundles.connected p s hs
  poly := Bundles.polynomial p s
  counts := Bundles.eval_counts p s
  at_four := by
    let n := Nat.card (Flow (Bundles.graph p s) (ZMod 4))
    have he : (Bundles.polynomial p s).eval 4 = (n : ℂ) := by
      simpa [n,ZMod.card] using Bundles.eval_counts p s (ZMod 4)
    refine ⟨n,Nat.pos_of_ne_zero ?_,he⟩
    intro hn
    exact Bundles.eval_four_ne_zero p s (by simpa [hn] using he)

inductive Family : Block → Prop
  | ladder (m s : ℕ) : Family (ladderBlock m s)
  | bundle (p s : ℕ) (hs : 0 < s) : Family (bundleBlock p s hs)

/-- The witnesses are nonzero orbital polynomials of simple connected graphs.
Every action is induced by swapping two blocks. -/
structure SwapWitness (B : Block) (d : ℕ) (z : ℂ) : Prop where
  family : Family B
  copies_pos : 0 < d
  is_root : (FlowCopies.orbitPolynomial B.poly d 2).IsRoot z
  nonzero : FlowCopies.orbitPolynomial B.poly d 2 ≠ 0
  connected : (FlowBouquet.underlying (witnessGraph B d 2)).Connected
  loopless : ∀ e, (witnessGraph B d 2).tail e ≠ (witnessGraph B d 2).head e
  simple : ∀ {e f}, ((witnessGraph B d 2).tail e = (witnessGraph B d 2).tail f ∧
      (witnessGraph B d 2).head e = (witnessGraph B d 2).head f) ∨
      ((witnessGraph B d 2).tail e = (witnessGraph B d 2).head f ∧
      (witnessGraph B d 2).head e = (witnessGraph B d 2).tail f) → e = f
  group_order : Fintype.card (Equiv.Perm (Fin 2)) = 2
  faithful : Function.Injective (fun p : Equiv.Perm (Fin 2) => (FlowBouquet.rotation (model B d) none 2 p).edge)
  pullback : OrbitalFlowTheorem.Pullback (model B d) none
  counts : ∀ (A : Type) [AddCommGroup A] [Fintype A],
    (FlowCopies.orbitPolynomial B.poly d 2).eval (Fintype.card A : ℂ) =
      Nat.card (FlowBouquet.Orbits (model B d) none A 2)

private theorem witness {B : Block} {d : ℕ} {z : ℂ} (hf : Family B) (hd : 0 < d)
    (hz : (FlowCopies.orbitPolynomial B.poly d 2).IsRoot z) : SwapWitness B d z where
  family := hf
  copies_pos := hd
  is_root := hz
  nonzero := nonzero B d 2
  connected := connected B d 2
  loopless := loopless B d 2
  simple := simple B d 2
  group_order := by rw [Fintype.card_perm,Fintype.card_fin]; decide
  faithful := faithful B hd 2
  pullback := fun A _ p f e => FlowBouquet.action_is_pullback _ _ A 2 p f e
  counts := counts B d 2

/-- Every complex neighborhood contains an orbital flow root with the
specified faithful copy-swap action, using only the ladder and bundle graphs. -/
theorem dense_fixed_swap_roots : Dense {z : ℂ | ∃ B d, SwapWitness B d z} := by
  let S := {z : ℂ | ∃ B d, SwapWitness B d z}
  have inside : Metric.ball (1:ℂ) 1 ⊆ closure S := by
    intro z hz
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨m,s,d,hd,w,hn,hw⟩ := SwapDisk.exists_root
      (by simpa [Metric.mem_ball,dist_eq_norm] using hz) hε
    exact ⟨w,⟨_,_,witness (.ladder m s) hd hw⟩,hn⟩
  have closedInside : Metric.closedBall (1:ℂ) 1 ⊆ closure S := by
    rw [← closure_ball (1:ℂ) (one_ne_zero : (1:ℝ) ≠ 0)]
    exact closure_minimal inside isClosed_closure
  intro z
  by_cases hz : ‖z-1‖ ≤ 1
  · exact closedInside (by simpa [Metric.mem_closedBall,dist_eq_norm] using hz)
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨s,p,w,hs,hp,hn,hw₀,hw⟩ := Sokal.exists_theta_root
    (by simpa [norm_sub_rev] using (lt_of_not_ge hz)) hε
  cases p with
  | zero => omega
  | succ p =>
    have he := Bundles.scaled_polynomial p s w
    rw [hw,mul_zero] at he
    have hroot := (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ hw₀)
    refine ⟨w,⟨_,_,witness (.bundle p s (by omega)) (d:=1) (by decide) ?_⟩,(dist_comm w z) ▸ hn⟩
    apply FlowCopies.root_of_value _ _ _ (j:=0) (by decide)
    simpa [bundleBlock] using hroot

end CameronKayibi.Flow.Plane
