import Graph189CommonCutLabel
import Graph189CutSides
import Graph189R1Metric

open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

namespace Graph189HighLabel

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V}
variable [DecidableRel G.Adj] {A B S : Finset V}

/-- Above both size thresholds, every label has a high small-side contact
provided the side has a high port somewhere. -/
theorem all_labels (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (smaller : ∀ T : Finset V, T.card < S.card → (G.induce {u : V | u ∉ T}).Connected)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (population : S.card * G.secondSmallestDegree < B.card)
    (order : (S.card+1)*G.secondSmallestDegree+S.card < Fintype.card V)
    (port : ∃ x ∈ A, G.secondSmallestDegree ≤ G.degree x ∧ ∃ j ∈ S, G.Adj x j)
    {i : V} (hi : i ∈ S) :
    ∃ x ∈ A, G.secondSmallestDegree ≤ G.degree x ∧ G.Adj x i := by
  classical
  by_contra refused
  obtain ⟨⟨z,hz,zi⟩,_⟩ := sides.contacts_of_minimum smaller hi
  have low : G.degree z < G.secondSmallestDegree := by
    by_contra! high
    exact refused ⟨z,hz,high,zi⟩
  have high_of_ne {v} (ne : z ≠ v) : G.secondSmallestDegree ≤ G.degree v :=
    (degree_pair (G := G) z v ne).resolve_left (not_le_of_gt low)
  have ihigh := high_of_ne zi.ne
  have within : G.neighborFinset z ∩ G.neighborFinset i ⊆ S := by
    intro v hv
    obtain ⟨zv,iv⟩ := mem_inter.mp hv
    have zv' := (G.mem_neighborFinset _ _).mp zv
    have iv' := (G.mem_neighborFinset _ _).mp iv
    rcases sides.cover v with ha | hb | hs
    · exact (refused ⟨v,ha,high_of_ne zv'.ne,iv'.symm⟩).elim
    · exact (sides.no_cross z hz v hb zv').elim
    · exact hs
  have all := Graph189CommonCutLabel.complete_label hc hi zi within cap ihigh order
  obtain ⟨x,hx,xhigh,j,hj,xj⟩ := port
  apply refused
  refine ⟨x,hx,xhigh,?_⟩
  by_cases eq : j = i
  · exact eq ▸ xj
  have ij := all j hj eq
  apply Graph189CommonCutLabel.forced_contact hc S B
    (fun hs => Finset.disjoint_left.mp sides.left_cut hx hs)
    (fun hb => Finset.disjoint_left.mp sides.apart hx hb)
    (fun y edge hy => sides.no_cross x hx y hy edge)
    (fun b hb p => sides.meets hx hb p) cap population hi hj xj ij

/-- Two-vertex-connectivity supplies the initial high port on every side
of size at least two. The only possible low vertex cannot block all exits. -/
theorem large_side_has_high_port (sides : Graph189CutSides.CutSides G A B S)
    (deletion : ∀ z : V, (G.induce {v : V | v ≠ z}).Connected)
    (size : 2 ≤ A.card) {z i : V} (hz : z ∈ A) (hi : i ∈ S) (zi : G.Adj z i) :
    ∃ x ∈ A, G.secondSmallestDegree ≤ G.degree x ∧ ∃ j ∈ S, G.Adj x j := by
  classical
  by_cases h : G.secondSmallestDegree ≤ G.degree z
  · exact ⟨z,hz,h,i,hi,zi⟩
  have sz := card_erase_of_mem hz
  obtain ⟨a,ha⟩ := card_pos.mp (by omega : 0 < (A.erase z).card)
  obtain ⟨b,hb⟩ := sides.right_nonempty
  have bn : b ≠ z := by
    rintro rfl
    exact Finset.disjoint_left.mp sides.apart hz hb
  let D : Set V := {v | v ≠ z}
  obtain ⟨walk⟩ := deletion z (⟨a,(mem_erase.mp ha).1⟩ : D) (⟨b,bn⟩ : D)
  obtain ⟨v,w,hv,hw,edge,_⟩ := Graph189CutSides.walk_exits (G := G.induce D)
    (fun t : D => t.val ∈ A) walk (mem_erase.mp ha).2
    (fun hba => Finset.disjoint_left.mp sides.apart hba hb)
  have vw : G.Adj v.val w.val := edge
  have high := (degree_pair (G := G) z v.val v.property.symm).resolve_left h
  rcases sides.cover w.val with hwa | hwb | hws
  · exact (hw hwa).elim
  · exact (sides.no_cross v.val hv w.val hwb vw).elim
  · exact ⟨v.val,hv,high,w.val,hws,vw⟩

/-- Full high-contact conclusion on every minimum separator in the large-side
branch. Uses the same deletion hypothesis as registered two-connected R2.H2. -/
theorem all_labels_of_large_side (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (deletion : ∀ z : V, (G.induce {v : V | v ≠ z}).Connected)
    (smaller : ∀ T : Finset V, T.card < S.card → (G.induce {u : V | u ∉ T}).Connected)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (population : S.card * G.secondSmallestDegree < B.card) (size : 2 ≤ A.card)
    (order : (S.card+1)*G.secondSmallestDegree+S.card < Fintype.card V)
    {i : V} (hi : i ∈ S) :
    ∃ x ∈ A, G.secondSmallestDegree ≤ G.degree x ∧ G.Adj x i := by
  obtain ⟨⟨z,hz,zi⟩,_⟩ := sides.contacts_of_minimum smaller hi
  exact all_labels hc sides smaller cap population order
    (large_side_has_high_port sides deletion size hz hi zi) hi

omit [Nontrivial V] [DecidableRel G.Adj] in
/-- A singleton side spends at most one even budget for itself and one per
separator vertex. No graph degree assumption is needed. -/
theorem singleton_side_order (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (smaller : ∀ T : Finset V, T.card < S.card → (G.induce {u : V | u ∉ T}).Connected)
    {k : ℕ} (cap : ∀ v, G.distEven v ≤ k+1) (size : A.card = 1) :
    Fintype.card V ≤ (S.card+1)*k+S.card+1 := by
  classical
  obtain ⟨z,hz⟩ := card_eq_one.mp size
  have zm : z ∈ A := hz ▸ mem_singleton_self _
  have touches (a : V) (ha : a ∈ S) : G.Adj z a := by
    obtain ⟨⟨v,hv,edge⟩,_⟩ := sides.contacts_of_minimum smaller ha
    have vz : v = z := mem_singleton.mp (hz ▸ hv)
    exact vz ▸ edge
  have bcount := Graph189SeparatorCover.of_walk_separator hc z B S S
    (fun hb => Finset.disjoint_left.mp sides.apart zm hb)
    (fun a ha hb => Finset.disjoint_left.mp sides.right_cut hb ha)
    touches (fun b hb p => sides.meets zm hb p)
    (fun a ha => ⟨a,ha,by simp [dist_eq_one_iff_adj.mpr (touches a ha)]⟩) k cap
  have cov : univ ⊆ (A ∪ B) ∪ S := by
    intro v _
    rcases sides.cover v with h | h | h
    · exact mem_union_left _ (mem_union_left _ h)
    · exact mem_union_left _ (mem_union_right _ h)
    · exact mem_union_right _ h
  have n := card_le_card cov
  rw [card_univ] at n
  have h1 := card_union_le (A ∪ B) S
  have h2 := card_union_le A B
  omega

/-- Every separator label has a real high contact under the numerical
hypotheses used by each of the terminal separator intervals. -/
theorem all_labels_in_order_range (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (deletion : ∀ z : V, (G.induce {v : V | v ≠ z}).Connected)
    (smaller : ∀ T : Finset V, T.card < S.card → (G.induce {u : V | u ∉ T}).Connected)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (population : S.card * G.secondSmallestDegree < B.card)
    (order : (S.card+1)*G.secondSmallestDegree+S.card+1 < Fintype.card V)
    {i : V} (hi : i ∈ S) :
    ∃ x ∈ A, G.secondSmallestDegree ≤ G.degree x ∧ G.Adj x i := by
  have pos : 0 < A.card := card_pos.mpr sides.left_nonempty
  have size : 2 ≤ A.card := by
    by_contra! small
    have singleton : A.card = 1 := by omega
    exact (not_lt_of_ge (singleton_side_order hc sides smaller cap singleton)) order
  exact all_labels_of_large_side hc sides deletion smaller cap population size (by omega) hi

#print axioms singleton_side_order
#print axioms all_labels_in_order_range
#print axioms all_labels
#print axioms large_side_has_high_port
#print axioms all_labels_of_large_side
end Graph189HighLabel
