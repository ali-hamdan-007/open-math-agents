import Graph189UniversalCycle
import Graph189MinimumCutOrder

namespace Graph189UniversalCycle
open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
variable {V : Type*} [Fintype V] [Nontrivial V]
variable {G : SimpleGraph V}

instance instCompleteDecidable [DecidableEq V] [DecidableRel G.Adj] {z : V} :
    DecidableRel (completeAt G z).Adj := fun a b =>
  inferInstanceAs (Decidable (G.Adj a b ∨ (a = z ∨ b = z) ∧ a ≠ b))

omit [Fintype V] [Nontrivial V] in
private theorem completion_preconnected {z : V} (S : Finset V) (hz : z ∉ S) :
    ((completeAt G z).induce {u : V | u ∉ S}).Connected := by
  let t : {u : V | u ∉ S} := ⟨z,hz⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨t,fun u => ?_⟩
  by_cases hu : u.val = z
  · have h : u = t := Subtype.ext hu
    rw [h]
  · exact (show ((completeAt G z).induce {u : V | u ∉ S}).Adj t u from
      Or.inr ⟨Or.inl rfl,Ne.symm hu⟩).reachable

omit [Fintype V] [Nontrivial V] in
private theorem completion_preserves_connected {z : V} (S : Finset V)
    (hc : (G.induce {u : V | u ∉ S}).Connected) :
    ((completeAt G z).induce {u : V | u ∉ S}).Connected := by
  have inc : G.induce {u : V | u ∉ S} ≤ (completeAt G z).induce {u : V | u ∉ S} :=
    fun _ _ h => Or.inl h
  exact hc.mono inc

private theorem connectivity_bounds (K : SimpleGraph V) (z : V) {s : ℕ}
    (hsize : s ≤ Fintype.card V - 1)
    (small : ∀ S : Finset V, S.card < s → (K.induce {u : V | u ∉ S}).Connected) :
    s ≤ K.vertexConnectivity := by
  classical
  let M : Set ℕ := {j | ∃ S : Finset V, S.card = j ∧
    (¬(K.induce ((S : Set V)ᶜ)).Connected ∨ S.card = Fintype.card V-1)}
  have hn := Fintype.one_lt_card (α := V)
  have eq : K.vertexConnectivity = sInf M := by
    unfold vertexConnectivity
    rw [if_neg (by omega : ¬Fintype.card V ≤ 1)]
  have sz : (univ.erase z).card = Fintype.card V-1 := by
    rw [card_erase_of_mem (mem_univ z),card_univ]
  have ex : M.Nonempty := ⟨_,univ.erase z,sz,Or.inr sz⟩
  rw [eq]
  obtain ⟨T,ht,htc|htc⟩ := Nat.sInf_mem ex
  · by_contra! bad
    exact htc (small T (ht ▸ bad))
  · omega

private theorem conn_le_order (K : SimpleGraph V) (z : V) :
    K.vertexConnectivity ≤ Fintype.card V - 1 := by
  classical
  have hn := Fintype.one_lt_card (α:=V)
  unfold vertexConnectivity
  rw [if_neg (by omega : ¬Fintype.card V ≤ 1)]
  have sz : (univ.erase z).card = Fintype.card V-1 := by
    rw [card_erase_of_mem (mem_univ z),card_univ]
  exact Nat.sInf_le ⟨univ.erase z,sz,Or.inr sz⟩

theorem completeAt_connectivity (z : V) :
    G.vertexConnectivity ≤ (completeAt G z).vertexConnectivity := by
  apply connectivity_bounds _ z (conn_le_order G z)
  intro S hS
  exact completion_preserves_connected S (Graph189CutSides.connected_after_smaller_deletion S hS)

/-- Raising the degree of a vertex outside every minimum separator gains one
full unit of vertex connectivity, unless the complete-graph ceiling is reached. -/
theorem completeAt_connectivity_add_one (z : V)
    (room : G.vertexConnectivity < Fintype.card V - 1)
    (no_cut : ∀ S : Finset V, S.card = G.vertexConnectivity → z ∈ S →
       (G.induce {u : V | u ∉ S}).Connected) :
    G.vertexConnectivity + 1 ≤ (completeAt G z).vertexConnectivity := by
  apply connectivity_bounds _ z (by omega)
  intro S hS
  by_cases hz : z ∈ S
  · apply completion_preserves_connected
    rcases lt_or_ge S.card G.vertexConnectivity with h|h
    · exact Graph189CutSides.connected_after_smaller_deletion S h
    · exact no_cut S (by omega) hz
  · exact completion_preconnected S hz

variable [DecidableEq V] [DecidableRel G.Adj]

omit [Nontrivial V] in
theorem degree_le_completeAt (z v : V) : G.degree v ≤ (completeAt G z).degree v := by
  rw [←G.card_neighborFinset_eq_degree,←(completeAt G z).card_neighborFinset_eq_degree]
  apply card_le_card
  intro x hx
  exact ((completeAt G z).mem_neighborFinset _ _).mpr (Or.inl ((G.mem_neighborFinset _ _).mp hx))

omit [Nontrivial V] in
theorem completeAt_degree_self (z : V) : (completeAt G z).degree z = Fintype.card V - 1 := by
  have eq : (completeAt G z).neighborFinset z = univ.erase z := by
    ext a
    simp only [SimpleGraph.mem_neighborFinset,mem_erase,mem_univ,and_true]
    constructor
    · intro h
      exact h.ne.symm
    · intro h
      exact Or.inr ⟨Or.inl rfl,h.symm⟩
  rw [←(completeAt G z).card_neighborFinset_eq_degree,eq,card_erase_of_mem (mem_univ z),card_univ]

theorem minDegree_le_completeAt (z : V) : G.minDegree ≤ (completeAt G z).minDegree := by
  obtain ⟨u,hu⟩ := (completeAt G z).exists_minimal_degree_vertex
  exact (G.minDegree_le_degree u).trans ((degree_le_completeAt z u).trans_eq hu.symm)

theorem secondDegree_le_completeAt_minDegree (z : V) (hz : G.degree z = G.minDegree) :
    G.secondSmallestDegree ≤ (completeAt G z).minDegree := by
  classical
  have high (v : V) (different : v ≠ z) : G.secondSmallestDegree ≤ G.degree v := by
    rcases degree_pair (G:=G) v z different with h|h
    · exact h
    · exact h.trans (hz ▸ G.minDegree_le_degree v)
  obtain ⟨w,hw⟩ := (completeAt G z).exists_minimal_degree_vertex
  rw [hw]
  by_cases eq : w = z
  · subst w
    rw [completeAt_degree_self]
    obtain ⟨v,hv⟩ := exists_ne z
    have := high v hv
    have := G.degree_lt_card_verts v
    omega
  · exact (high w eq).trans (degree_le_completeAt z w)

#print axioms completeAt_connectivity
#print axioms completeAt_connectivity_add_one
#print axioms minDegree_le_completeAt
#print axioms secondDegree_le_completeAt_minDegree
end Graph189UniversalCycle
