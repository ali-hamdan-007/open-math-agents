import Graph189ExteriorDegreeCycle
import Graph189CompletionConnectivity

namespace Graph189ExteriorDegreeCycle
open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

/-- Counting neighbors in an induced subgraph gives the corresponding count of
literal surviving neighbors in the original vertex type. -/
theorem degree_induce_filter {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (S : Set V) [Fintype S] [DecidablePred (· ∈ S)] (x : S) :
    (G.induce S).degree x = ((G.neighborFinset x.val).filter (fun v => v ∈ S)).card := by
  classical
  let f : S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have same : ((G.induce S).neighborFinset x).map f =
      (G.neighborFinset x.val).filter (fun y => y ∈ S) := by
    ext y
    constructor
    · intro hy
      obtain ⟨u,hu,rfl⟩ := mem_map.mp hy
      exact mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr
        (((G.induce S).mem_neighborFinset _ _).mp hu),u.property⟩
    · intro hy
      obtain ⟨he,hs⟩ := mem_filter.mp hy
      exact mem_map.mpr ⟨⟨y,hs⟩,((G.induce S).mem_neighborFinset _ _).mpr
        ((G.mem_neighborFinset _ _).mp he),rfl⟩
  have card := congrArg Finset.card same
  rwa [card_map,(G.induce S).card_neighborFinset_eq_degree] at card

theorem degree_le_deletion_add_one {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (w : V) (x : {u : V | u ≠ w}) :
    G.degree x.val ≤ (G.induce {u : V | u ≠ w}).degree x + 1 := by
  rw [degree_induce_filter,←G.card_neighborFinset_eq_degree]
  have eq : (G.neighborFinset x.val).filter (fun v => v ∈ {u : V | u ≠ w}) =
      (G.neighborFinset x.val).erase w := by ext u; simp [and_comm]
  rw [eq]
  have := pred_card_le_card_erase (a:=w) (s:=G.neighborFinset x.val)
  omega

/-- Isolated vertices can be discarded when finding cycles, so the degree bound
is required only at exterior vertices participating in an exterior edge. -/
theorem cycle_of_nonisolated_degree {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ} (two : 2 ≤ d)
    (edge : ∃ x y, G.Adj x y)
    (degree : ∀ x y, G.Adj x y → d ≤ G.degree x) :
    ∃ a, ∃ Q : G.Walk a a, Q.IsCycle ∧ d+1 ≤ Q.length := by
  classical
  let S : Set V := {v | ∃ y, G.Adj v y}
  obtain ⟨x,y,hxy⟩ := edge
  have sd (v : S) : d ≤ (G.induce S).degree v := by
    rw [degree_induce_filter]
    have eq : (G.neighborFinset v.val).filter (fun u => u ∈ S) = G.neighborFinset v.val := by
      apply filter_eq_self.mpr
      exact fun u hu => ⟨v.val,((G.mem_neighborFinset _ _).mp hu).symm⟩
    rw [eq,G.card_neighborFinset_eq_degree]
    obtain ⟨b,hb⟩ := v.property
    exact degree v.val b hb
  obtain ⟨v,Q,hQ,len⟩ := cycle_of_degree (G:=G.induce S) ⟨x,y,hxy⟩ two sd
  let f := (Embedding.induce (G:=G) S).toHom
  exact ⟨f v,Q.map f,hQ.map Subtype.val_injective,len.trans_eq (Walk.length_map f Q).symm⟩

/-- In any finite graph, not necessarily connected, a cross-contact inequality at
the outside edges supplies a long cycle disjoint from the marked path vertices. -/
theorem cycle_from_cross_contacts {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (P : Finset V) {k D d : ℕ}
    (two : 2 ≤ d) (room : k + 2*d ≤ 2*D) (bound : ∀ v, D ≤ G.degree v)
    (edge : ∃ x ∉ P, ∃ y ∉ P, G.Adj x y)
    (contacts : ∀ x ∉ P, ∀ y ∉ P, G.Adj x y →
      ((G.neighborFinset x) ∩ P).card + G.degree y ≤
        k + ((G.neighborFinset x) \ P).card) :
    ∃ a, ∃ Q : (G.induce {v : V | v ∉ P}).Walk a a, Q.IsCycle ∧ d+1 ≤ Q.length := by
  let S : Set V := {v | v ∉ P}
  apply cycle_of_nonisolated_degree two
  · obtain ⟨x,hx,y,hy,h⟩ := edge
    exact ⟨⟨x,hx⟩,⟨y,hy⟩,h⟩
  · intro x y adj
    rw [degree_induce_filter]
    have eq : (G.neighborFinset x.val).filter (fun u => u ∈ S) = G.neighborFinset x.val \ P := by
      ext u
      simp [S]
    rw [eq]
    have h := contacts x.val x.property y.val y.property adj
    have split := card_sdiff_add_card_inter (G.neighborFinset x.val) P
    rw [G.card_neighborFinset_eq_degree] at split
    have := bound x.val
    have := bound y.val
    omega

#print axioms degree_le_deletion_add_one
#print axioms cycle_of_nonisolated_degree
#print axioms cycle_from_cross_contacts
end Graph189ExteriorDegreeCycle
