import Conjectures.FlowOrbitPolynomial
import Mathlib.Combinatorics.SimpleGraph.Path

namespace CameronKayibi.FlowBouquet
open FlowGraph

variable {V E : Type} [Fintype E] [Fintype V] [DecidableEq V]

def current {A : Type} [AddCommGroup A] (p : E → V) (f : E → A) (v : V) :=
  ∑ e, if p e = v then f e else 0

private theorem current_sum {A : Type} [AddCommGroup A] (p : E → V) (f : E → A) :
    (∑ v, current p f v) = ∑ e, f e := by
  unfold current
  rw [Finset.sum_comm]
  simp

/-- On a finite graph conservation at every vertex except possibly the root implies
conservation there as well. Loops are handled in the same sum. -/
theorem kirchhoff_except {A : Type} [AddCommGroup A] (H : OrientedGraph V E)
    (o : V) (f : E → A) (h : ∀ v, v ≠ o → current H.tail f v = current H.head f v) :
    Kirchhoff H f := by
  intro v
  by_cases hv : v = o
  · subst v
    have htot : (∑ u, current H.tail f u) = ∑ u, current H.head f u := by rw [current_sum, current_sum]
    have hrest : (∑ u ∈ Finset.univ.erase o, current H.tail f u) = ∑ u ∈ Finset.univ.erase o, current H.head f u := by
      apply Finset.sum_congr rfl
      intro u hu
      exact h u (Finset.mem_erase.mp hu).1
    rw [← Finset.sum_erase_add Finset.univ (current H.tail f) (Finset.mem_univ o), ← Finset.sum_erase_add Finset.univ (current H.head f) (Finset.mem_univ o), hrest] at htot
    exact add_left_cancel htot
  · exact h v hv

abbrev Vertex (o : V) (d : ℕ) := Option (Fin d × {v : V // v ≠ o})

/-- The embeddings of the copies identify exactly the chosen root. -/
def tag (o : V) {d : ℕ} (i : Fin d) (v : V) : Vertex o d :=
  if h : v = o then none else some (i,⟨v,h⟩)

omit [Fintype V] in
private theorem tag_some (o : V) {d : ℕ} (i k : Fin d) (v : V) (u : {v : V // v ≠ o}) :
    tag o i v = some (k,u) ↔ (i,v) = (k,u.1) := by
  by_cases hv : v=o
  · subst v; simp [tag, u.2.symm]
  · simp [tag,hv,Prod.ext_iff,Subtype.ext_iff]

omit [Fintype V] in
theorem tag_injective (o : V) {d : ℕ} (i : Fin d) : Function.Injective (tag o i) := by
  intro a b h
  by_cases ha : a=o <;> by_cases hb : b=o <;> simp_all [tag]

def graph (H : OrientedGraph V E) (o : V) (d : ℕ) : OrientedGraph (Vertex o d) (Fin d × E) where
  tail e := tag o e.1 (H.tail e.2)
  head e := tag o e.1 (H.head e.2)

private def untag (o : V) {d : ℕ} : Vertex o d → V
  | none => o
  | some ⟨_,v⟩ => v.1

omit [Fintype V] in
private theorem untag_tag (o : V) {d : ℕ} (i : Fin d) (x : V) : untag o (tag o i x) = x := by
  by_cases h : x=o <;> simp [tag,h,untag]

omit [Fintype V] in
private theorem tags_pair (o : V) {d : ℕ} {i j : Fin d} {a b c v : V} (hn : a ≠ b)
    (h₁ : tag o i a = tag o j c) (h₂ : tag o i b = tag o j v) :
    i=j ∧ a=c ∧ b=v := by
  have ac : a=c := by simpa only [untag_tag] using congrArg (untag o) h₁
  have bv : b=v := by simpa only [untag_tag] using congrArg (untag o) h₂
  subst c; subst v
  refine ⟨?_,rfl,rfl⟩
  by_cases ha : a=o
  · have hb : b≠o := fun h => hn (ha.trans h.symm)
    simpa [tag,hb] using h₂
  · simpa [tag,ha] using h₁

omit [Fintype V] [Fintype E] in
/-- Identifying one root from each copy does not create a loop. -/
theorem tail_ne_head (H : OrientedGraph V E) (o : V) (d : ℕ) (hl : ∀ e, H.tail e ≠ H.head e)
    (e : Fin d × E) : (graph H o d).tail e ≠ (graph H o d).head e :=
  fun h => hl e.2 (tag_injective o e.1 h)

omit [Fintype V] [Fintype E] in
/-- A bouquet of simple graphs has at most one edge on each unordered pair of vertices. -/
theorem edge_unique (H : OrientedGraph V E) (o : V) (d : ℕ)
    (hl : ∀ e, H.tail e ≠ H.head e)
    (hu : ∀ {e f}, (H.tail e=H.tail f ∧ H.head e=H.head f) ∨
      (H.tail e=H.head f ∧ H.head e=H.tail f) → e=f) {e f : Fin d × E}
    (h : ((graph H o d).tail e=(graph H o d).tail f ∧ (graph H o d).head e=(graph H o d).head f) ∨
      ((graph H o d).tail e=(graph H o d).head f ∧ (graph H o d).head e=(graph H o d).tail f)) : e=f := by
  rcases h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · obtain ⟨hi,ht,hh⟩ := tags_pair o (hl e.2) h₁ h₂
    exact Prod.ext hi (hu (Or.inl ⟨ht,hh⟩))
  · obtain ⟨hi,ht,hh⟩ := tags_pair o (hl e.2) h₁ h₂
    exact Prod.ext hi (hu (Or.inr ⟨ht,hh⟩))

variable (H : OrientedGraph V E) (o : V) (A : Type) [AddCommGroup A] (d : ℕ)

omit [Fintype V] in
private theorem away (p : E → V) (f : Fin d × E → A) (i : Fin d) (u : {v : V // v ≠ o}) :
    current (fun e : Fin d × E => tag o e.1 (p e.2)) f (some (i,u)) =
      current p (fun e => f (i,e)) u.1 := by
  simp only [current, tag_some]
  apply FlowDouble.tagged_sum

theorem kirchhoff_iff (f : Fin d × E → A) :
    Kirchhoff (graph H o d) f ↔ ∀ i, Kirchhoff H (fun e => f (i,e)) := by
  constructor
  · intro h i
    apply kirchhoff_except H o
    intro u hu
    have h' := h (some (i,⟨u,hu⟩))
    change current _ f _ = current _ f _ at h'
    simpa only [graph, away] using h'
  · intro h
    apply kirchhoff_except (graph H o d) none
    rintro (_ | ⟨i,u⟩) hu
    · exact (hu rfl).elim
    · simpa only [graph, away] using h i u.1

/-- Identifying the roots does not change which edge assignments are flows. -/
def unglue : Flow (graph H o d) A ≃ Flow (FlowCopies.copies H d) A where
  toFun f := ⟨f.1, f.2.1, (FlowCopies.kirchhoff_iff H A d _).2 ((kirchhoff_iff H o A d _).1 f.2.2)⟩
  invFun f := ⟨f.1, f.2.1, (kirchhoff_iff H o A d _).2 ((FlowCopies.kirchhoff_iff H A d _).1 f.2.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl



/-- Graph automorphisms permute the copies and fix the identified vertex. -/
def rotation (p : Equiv.Perm (Fin d)) : FlowDouble.Automorphism (graph H o d) where
  vertex := (p.prodCongr (Equiv.refl _)).optionCongr
  edge := p.prodCongr (Equiv.refl _)
  map_tail := by
    rintro ⟨i,e⟩
    by_cases he : H.tail e=o <;> simp [graph,tag,he]
  map_head := by
    rintro ⟨i,e⟩
    by_cases he : H.head e=o <;> simp [graph,tag,he]

instance action : MulAction (Equiv.Perm (Fin d)) (Flow (graph H o d) A) where
  smul p f := (unglue H o A d).symm (p • unglue H o A d f)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem action_is_pullback (p : Equiv.Perm (Fin d)) (f : Flow (graph H o d) A) (e : Fin d × E) :
    (p • f).1 e = f.1 ((rotation H o d p.symm).edge e) := rfl

abbrev Orbits := MulAction.orbitRel.Quotient (Equiv.Perm (Fin d)) (Flow (graph H o d) A)

def orbitUnglue : Orbits H o A d ≃ FlowCopies.Orbits H A d :=
  Quotient.congr (unglue H o A d) (by
    intro f g
    rw [MulAction.orbitRel_apply, MulAction.orbitRel_apply, MulAction.mem_orbit_iff, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨p,rfl⟩
      exact ⟨p,rfl⟩
    · rintro ⟨p,hp⟩
      exact ⟨p,(unglue H o A d).injective hp⟩)

theorem ordinary_count [Finite A] :
    Nat.card (Flow (graph H o d) A) = Nat.card (Flow H A)^d := by
  rw [Nat.card_congr (unglue H o A d), FlowCopies.ordinary_count]

theorem orbit_count [Finite A] :
    Nat.card (Orbits H o A d) = Nat.multichoose (Nat.card (Flow H A)) d := by
  rw [Nat.card_congr (orbitUnglue H o A d), FlowCopies.orbit_count]

/-- The simple undirected graph obtained by forgetting directions, loops and multiplicities. -/
def underlying (G : OrientedGraph V E) : SimpleGraph V where
  Adj v w := v ≠ w ∧ ∃ e, (G.tail e=v ∧ G.head e=w) ∨ (G.tail e=w ∧ G.head e=v)
  symm := by rintro a b ⟨hne,e,he⟩; exact ⟨hne.symm, e,he.symm⟩
  loopless := fun _ h => h.1 rfl

private def tagHom (i : Fin d) : underlying H →g underlying (graph H o d) where
  toFun := tag o i
  map_rel' := by
    rintro a b ⟨hab,e,h | h⟩
    · exact ⟨fun hx => hab ((tag_injective o i) hx), ⟨i,e⟩,Or.inl ⟨congrArg (tag o i) h.1,congrArg (tag o i) h.2⟩⟩
    · exact ⟨fun hx => hab ((tag_injective o i) hx), ⟨i,e⟩,Or.inr ⟨congrArg (tag o i) h.1,congrArg (tag o i) h.2⟩⟩

omit [Fintype V] [Fintype E] in
/-- A bouquet of connected graphs is connected, including the single-root graph for zero copies. -/
theorem connected (h : (underlying H).Connected) : (underlying (graph H o d)).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).2
  refine ⟨none, ?_⟩
  rintro (_ | ⟨i,u⟩)
  · exact SimpleGraph.Reachable.rfl
  · have hh := (h o u.1).map (tagHom H o d i)
    change (underlying (graph H o d)).Reachable (tag o i o) (tag o i u.1) at hh
    simpa [tag, u.2] using hh

/-- The normalized polynomial also counts the symmetric-copy action on a bouquet
of bouquets. When the base graph is connected, both gluings preserve connectivity. -/
theorem eval_counts [Fintype A] (P : Polynomial ℂ) (N : ℕ)
    (h : P.eval (Fintype.card A : ℂ) = Nat.card (Flow H A)) :
    (FlowCopies.orbitPolynomial P d N).eval (Fintype.card A : ℂ) =
      Nat.card (Orbits (graph H o d) none A N) := by
  rw [FlowCopies.eval_counts H A P d N h, FlowCopies.orbit_count, orbit_count,
    FlowCopies.ordinary_count, ordinary_count]

end CameronKayibi.FlowBouquet
