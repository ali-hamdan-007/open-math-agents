import Graph189HallDeficiency
import Graph189VertexMatching

open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private theorem closed_mem_end {W : Type*} {H : SimpleGraph W} {S : Set W} {a b : W}
    (closed : ∀ u∈S, ∀ v, H.Adj u v → v∈S) (walk : H.Walk a b) (ha : a∈S) : b∈S := by
  induction walk with
  | nil => exact ha
  | cons h q ih => exact ih (closed _ ha _ h)

omit [Fintype V] in
/-- A fixed exceptional barrier F can be deleted together with the Hall cut.
This supplies the contact matching for an exterior leaf block when F is its cut vertex. -/
theorem matching_at_buffered_boundary (P K F : Finset V) (apart : Disjoint P K)
    (fP : Disjoint F P) (fK : Disjoint F K)
    (boundary : ∀ u∈K, ∀ v∉K, G.Adj u v → v∈P ∨ v∈F)
    {s : ℕ} (smallP : s ≤ P.card) (smallK : s ≤ K.card)
    (connected : ∀ cut : Finset V, cut.card < s+F.card → (G.induce {u : V | u∉cut}).Connected) :
    ∃ A : Finset V, A⊆P ∧ s ≤ A.card ∧ ∃ f : A ↪ K, ∀ u, G.Adj u.val (f u).val := by
  classical
  let links := fun u : P => K.attach.filter (fun v => G.Adj u.val v.val)
  have hall (T : Finset P) : T.card ≤ (T.biUnion links).card+(Fintype.card P-s) := by
    let A := T.image (fun u : P => u.val)
    let N := T.biUnion links
    let B := N.image (fun v : K => v.val)
    let base := (P \ A) ∪ B
    let cut := base ∪ F
    have aP : A⊆P := by
      intro z hz
      obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hz
      exact u.property
    have bK : B⊆K := by
      intro z hz
      obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hz
      exact v.property
    have ca : A.card=T.card := Finset.card_image_of_injective _ Subtype.val_injective
    have cb : B.card=N.card := Finset.card_image_of_injective _ Subtype.val_injective
    have tP : T.card ≤ P.card := by simpa using T.card_le_univ
    by_contra! bad
    change (T.biUnion links).card+(Fintype.card P-s) < T.card at bad
    change N.card+(Fintype.card P-s) < T.card at bad
    simp only [Fintype.card_coe] at bad
    have shortBase : base.card < s := by
      have bound := Finset.card_union_le (P \ A) B
      rw [Finset.card_sdiff_of_subset aP,ca,cb] at bound
      change ((P \ A) ∪ B).card < s
      omega
    have short : cut.card < s+F.card := (Finset.card_union_le base F).trans_lt (Nat.add_lt_add_right shortBase _)
    obtain ⟨u,hu⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
    obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0 < (K \ B).card by
      rw [Finset.card_sdiff_of_subset bK,cb]
      omega)
    obtain ⟨vK,vB⟩ := Finset.mem_sdiff.mp hv
    have uA : u.val∈A := Finset.mem_image.mpr ⟨u,hu,rfl⟩
    have uSafe : u.val∉cut := by
      intro h
      rcases Finset.mem_union.mp h with core | barrier
      · rcases Finset.mem_union.mp core with h | h
        · exact (Finset.mem_sdiff.mp h).2 uA
        · exact Finset.disjoint_left.mp apart u.property (bK h)
      · exact Finset.disjoint_left.mp fP barrier u.property
    have vSafe : v∉cut := by
      intro h
      rcases Finset.mem_union.mp h with core | barrier
      · rcases Finset.mem_union.mp core with h | h
        · exact Finset.disjoint_left.mp apart (Finset.mem_sdiff.mp h).1 vK
        · exact vB h
      · exact Finset.disjoint_left.mp fK barrier vK
    let H := G.induce {z : V | z∉cut}
    let S : Set {z : V // z∉cut} := {z | z.val∈K}
    have closed : ∀ z∈S, ∀ w, H.Adj z w → w∈S := by
      intro z zk w edge
      change z.val∈K at zk
      change w.val∈K
      by_contra wk
      have ambient : G.Adj z.val w.val := edge
      have wp : w.val∈P := (boundary z.val zk w.val wk ambient).resolve_right
        (fun barrier => w.property (Finset.mem_union_right _ barrier))
      have wa : w.val∈A := by
        by_contra no
        exact w.property (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨wp,no⟩)))
      obtain ⟨t,ht,teq⟩ := Finset.mem_image.mp wa
      let zk' : K := ⟨z.val,zk⟩
      have hit : zk'∈N := Finset.mem_biUnion.mpr ⟨t,ht,Finset.mem_filter.mpr
        ⟨Finset.mem_attach _ _,show G.Adj t.val z.val by rw [teq]; exact ambient.symm⟩⟩
      exact z.property (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨zk',hit,rfl⟩)))
    obtain ⟨walk⟩ := (connected cut short).preconnected ⟨v,vSafe⟩ ⟨u.val,uSafe⟩
    have uk := closed_mem_end (S := S) closed walk (show (⟨v,vSafe⟩ : {z : V // z∉cut})∈S from vK)
    exact Finset.disjoint_left.mp apart u.property uk
  obtain ⟨U,wide,f,acceptable⟩ := hall_at_least links s (by simpa using smallP) hall
  let A := U.image (fun u : P => u.val)
  have fromA (z : A) : ∃ u : U, u.val.val=z.val := by
    obtain ⟨t,ht,eq⟩ := Finset.mem_image.mp z.property
    exact ⟨⟨t,ht⟩,eq⟩
  let pick := fun z : A => (fromA z).choose
  have pickEq (z : A) : (pick z).val.val=z.val := (fromA z).choose_spec
  have pi : Function.Injective pick := by
    intro z w h
    apply Subtype.ext
    exact (pickEq z).symm.trans ((congrArg (fun u : U => u.val.val) h).trans (pickEq w))
  let assign := (⟨pick,pi⟩ : A ↪ U).trans f
  refine ⟨A,?_,?_,assign,?_⟩
  · intro v hv
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hv
    exact t.property
  · simpa [A,Finset.card_image_of_injective _ Subtype.val_injective] using wide
  · intro z
    have adj := (Finset.mem_filter.mp (acceptable (pick z))).2
    change G.Adj (pick z).val.val (assign z).val at adj
    rwa [pickEq] at adj

omit [Fintype V] in
/-- If the exterior set K has no neighbor outside K and P, then genuine s-vertex
connectivity gives s pairwise disjoint contact edges between K and P. -/
theorem matching_at_component_boundary (P K : Finset V) (apart : Disjoint P K)
    (boundary : ∀ u∈K, ∀ v∉K, G.Adj u v → v∈P)
    {s : ℕ} (smallP : s ≤ P.card) (smallK : s ≤ K.card)
    (connected : ∀ cut : Finset V, cut.card < s → (G.induce {u : V | u∉cut}).Connected) :
    ∃ A : Finset V, A⊆P ∧ s ≤ A.card ∧ ∃ f : A ↪ K, ∀ u, G.Adj u.val (f u).val := by
  apply matching_at_buffered_boundary P K ∅ apart (by simp) (by simp)
    (fun u hu v hv e => Or.inl (boundary u hu v hv e)) smallP smallK
  simpa using connected

/-- An entire Hamilton-connected exterior component yields an ambient order bound
with the actual connectivity threshold. No preselected matching is required. -/
theorem whole_core_order_of_connectivity {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length ≤ p.length)
    (K : Finset V) (outside : ∀ z∈K, z∉p.support) (size : 1 < K.card)
    (boundary : ∀ u∈K, ∀ v∉K, G.Adj u v → v∈p.support)
    (hconn : ∀ a b : K, a≠b → ∃ q : (G.induce (K : Set V)).Walk a b, q.IsHamiltonian)
    {s : ℕ} (positive : 0 < s) (smallP : s ≤ p.support.length) (smallK : s ≤ K.card)
    (connected : ∀ cut : Finset V, cut.card < s → (G.induce {u : V | u∉cut}).Connected) :
    (s+2)*K.card+s ≤ Fintype.card V := by
  have apart : Disjoint p.support.toFinset K := Finset.disjoint_left.mpr (by
    intro z hz hk
    exact outside z hk (List.mem_toFinset.mp hz))
  have sizeP : s ≤ p.support.toFinset.card := by
    rwa [List.toFinset_card_of_nodup hp.support_nodup]
  obtain ⟨A,inside,wide,attach,edges⟩ := matching_at_component_boundary p.support.toFinset K apart
    (fun u hu v hv h => List.mem_toFinset.mpr (boundary u hu v hv h)) sizeP smallK connected
  have needed := exterior_vertex_matching_order p hp longest K size outside hconn A
    (Finset.card_pos.mp (by omega)) (fun z hz => List.mem_toFinset.mp (inside hz)) attach edges
  exact (Nat.add_le_add (Nat.mul_le_mul_right K.card (by omega : s+2 ≤ A.card+2)) wide).trans needed

#print axioms whole_core_order_of_connectivity
#print axioms matching_at_component_boundary
#print axioms matching_at_buffered_boundary
end Graph189ExteriorGap
