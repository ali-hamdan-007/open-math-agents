import Graph189CutSides
import Graph189PrescribedBatch

open SimpleGraph Finset
namespace Graph189CleanTwoAnchorJoin

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- A spanning path of one side with two prescribed contacts uses both
separator vertices. The whole-graph loss is the loss on the other side. -/
theorem join {A B S : Finset V} (sides : Graph189CutSides.CutSides G A B S)
    {i j : V} (pair : S = {i, j}) (ne : i ≠ j) {x y u v : V}
    (p : G.Walk x y) (q : G.Walk u v) (hp : p.IsPath) (hq : q.IsPath)
    (left : ∀ w ∈ p.support, w ∈ A) (right : ∀ w ∈ q.support, w ∈ B)
    (full : p.support.length = A.card) (first : G.Adj j x) (next : G.Adj y i)
    (enter : G.Adj i u) {loss : ℕ} (near : B.card ≤ q.support.length + loss) :
    ∃ r : G.Walk j v, r.IsPath ∧ Fintype.card V ≤ r.support.length + loss := by
  classical
  have iS : i ∈ S := by simp [pair]
  have jS : j ∈ S := by simp [pair]
  have noJ : j ∉ p.support := fun h => Finset.disjoint_left.mp sides.left_cut (left _ h) jS
  have noI : i ∉ q.support := fun h => Finset.disjoint_left.mp sides.right_cut (right _ h) iS
  let p' := p.cons first
  let q' := q.cons enter
  have pathP : p'.IsPath := (Walk.cons_isPath_iff first p).mpr ⟨hp, noJ⟩
  have pathQ : q'.IsPath := (Walk.cons_isPath_iff enter q).mpr ⟨hq, noI⟩
  have apart : List.Disjoint p'.support q'.support := by
    apply List.disjoint_left.mpr
    intro w wp wq
    rcases List.mem_cons.mp (show w ∈ j::p.support from wp) with eq | wp
    · subst w
      exact (List.mem_cons.mp (show j ∈ i::q.support from wq)).elim ne.symm
        (fun seen => Finset.disjoint_left.mp sides.right_cut (right _ seen) jS)
    rcases List.mem_cons.mp (show w ∈ i::q.support from wq) with eq | wq
    · subst w
      exact Finset.disjoint_left.mp sides.left_cut (left _ wp) iS
    exact Finset.disjoint_left.mp sides.apart (left _ wp) (right _ wq)
  let r := p'.append (q'.cons next)
  have support : r.support = p'.support ++ q'.support := by simp [r,Walk.support_append]
  have pathR : r.IsPath :=
    Walk.IsPath.mk' (support ▸ pathP.support_nodup.append pathQ.support_nodup apart)
  have cover : (univ : Finset V) ⊆ (A ∪ B) ∪ S := by
    intro w _
    rcases sides.cover w with a | b | s
    · exact mem_union_left _ (mem_union_left _ a)
    · exact mem_union_left _ (mem_union_right _ b)
    · exact mem_union_right _ s
  have order := (card_le_card cover).trans (card_union_le _ _)
  have both := card_union_le A B
  have size : S.card = 2 := by simp [pair,ne]
  rw [card_univ,size] at order
  refine ⟨r,pathR,?_⟩
  rw [support,List.length_append]
  have lenP : p'.support.length = p.support.length+1 := rfl
  have lenQ : q'.support.length = q.support.length+1 := rfl
  omega

/-- A finite induced graph is complete if every pair contains a vertex
already adjacent to every other vertex. -/
theorem complete_of_max_degree [DecidableRel G.Adj] (A : Finset V)
    (large : ∀ x y : A, x ≠ y →
      A.card - 1 ≤ (G.induce (A : Set V)).degree x ∨
      A.card - 1 ≤ (G.induce (A : Set V)).degree y) :
    G.induce (A : Set V) = ⊤ := by
  classical
  let H := G.induce (A : Set V)
  have allNeighbors (x : A) (hx : A.card-1 ≤ H.degree x) :
      H.neighborFinset x = univ.erase x := by
    apply eq_of_subset_of_card_le
    · intro y hy
      exact mem_erase.mpr ⟨((H.mem_neighborFinset _ _).mp hy).ne.symm,mem_univ _⟩
    rw [H.card_neighborFinset_eq_degree,card_erase_of_mem (mem_univ x),card_univ,Fintype.card_coe]
    exact hx
  ext x y
  change H.Adj x y ↔ _
  rw [top_adj]
  refine ⟨fun e => e.ne,fun ne => ?_⟩
  rcases large x y ne with hx | hy
  · apply (H.mem_neighborFinset x y).mp
    rw [allNeighbors x hx]
    simp [ne.symm]
  have edge : H.Adj y x := by
    apply (H.mem_neighborFinset y x).mp
    rw [allNeighbors y hy]
    simp [ne]
  exact edge.symm

/-- The prescribed path on the complete side can be supplied directly as
two distinct separator contacts. -/
theorem join_complete {A B S : Finset V} (sides : Graph189CutSides.CutSides G A B S)
    {i j : V} (pair : S = {i, j}) (ne : i ≠ j) {x y u v : V}
    (xA : x ∈ A) (yA : y ∈ A) (xy : x ≠ y) (complete : G.induce (A : Set V) = ⊤)
    (first : G.Adj j x) (next : G.Adj y i)
    (q : G.Walk u v) (hq : q.IsPath) (right : ∀ w ∈ q.support, w ∈ B)
    (enter : G.Adj i u) {loss : ℕ} (near : B.card ≤ q.support.length + loss) :
    ∃ r : G.Walk j v, r.IsPath ∧ Fintype.card V ≤ r.support.length + loss := by
  classical
  let a : A := ⟨x,xA⟩
  let b : A := ⟨y,yA⟩
  have distinct : a ≠ b := fun eq => xy (congrArg Subtype.val eq)
  obtain ⟨t,ht⟩ : ∃ t : (G.induce (A : Set V)).Walk a b, t.IsHamiltonian := by
    rw [complete]
    exact Graph189TerminalLeafClosure.complete_prescribed a b distinct
  let f := (Embedding.induce (G:=G) (A : Set V)).toHom
  let p : G.Walk x y := t.map f
  have left : ∀ w ∈ p.support, w ∈ A := by
    intro w seen
    rw [show p.support = t.support.map f from Walk.support_map _ _] at seen
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp seen
    exact a.property
  have full : p.support.length = A.card := by
    rw [show p.support = t.support.map f from Walk.support_map _ _,List.length_map,ht.length_support,Fintype.card_coe]
  exact join sides pair ne p q (ht.isPath.map Subtype.val_injective) hq left right
    full first next enter near

#print axioms join
#print axioms complete_of_max_degree
#print axioms join_complete
end Graph189CleanTwoAnchorJoin
