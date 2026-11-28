module

public import Graph189CutCore
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Nodup

public section

namespace Graph189InducedSide
open SimpleGraph Finset

variable {V : Type*} [DecidableEq V]

abbrev sideVerts (c : V) (A : Finset V) : Set V := ↑(insert c A)
abbrev sideGraph (G : SimpleGraph V) (c : V) (A : Finset V) := G.induce (sideVerts c A)
abbrev sideRoot (c : V) (A : Finset V) : sideVerts c A := ⟨c, Finset.mem_insert_self ..⟩

theorem degree_side [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {c : V} {A : Finset V} (hA : Graph189CutCore.Side G c A)
    (u : sideVerts c A) (hu : u ≠ sideRoot c A) :
    (sideGraph G c A).degree u = G.degree u.val := by
  have hx : u.val ≠ c := fun e => hu (Subtype.ext e)
  have ha : u.val ∈ A := (Finset.mem_insert.mp u.property).resolve_left hx
  have hsub : G.neighborSet u.val ⊆ sideVerts c A := by
    intro v hv
    by_cases hva : v ∈ A
    · exact Finset.mem_insert_of_mem hva
    · exact Finset.mem_insert.mpr (.inl (hA.exit_eq ha hv hva))
  convert SimpleGraph.degree_induce_of_neighborSet_subset (G := G) (s := sideVerts c A)
    (v := u) hsub using 1
  congr 1
  exact Subsingleton.elim _ _


theorem card_side [Fintype V] {G : SimpleGraph V} {c : V} {A : Finset V}
    (hA : Graph189CutCore.Side G c A) : Fintype.card (sideVerts c A) = A.card + 1 := by
  change Fintype.card ↥(insert c A) = _
  exact (Fintype.card_coe (insert c A)).trans (Finset.card_insert_of_notMem hA.outside)

theorem lift_rooted_list {G : SimpleGraph V} {c : V} {A : Finset V}
    (rooted : ∃ L : List (sideVerts c A), L.head? = some (sideRoot c A) ∧
      L.Nodup ∧ L.IsChain (sideGraph G c A).Adj ∧ ∀ u, u ∈ L) :
    ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ x, x ∈ L ↔ x = c ∨ x ∈ A := by
  obtain ⟨L, hhead, hn, hchain, hall⟩ := rooted
  refine ⟨L.map Subtype.val, ?_, hn.map Subtype.val_injective, ?_, ?_⟩
  · simp [List.head?_map, hhead]
  · exact (List.isChain_map Subtype.val).mpr hchain
  · intro x
    constructor
    · intro hx
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
      exact Finset.mem_insert.mp u.property
    · intro hx
      let u : sideVerts c A := ⟨x, Finset.mem_insert.mpr hx⟩
      exact List.mem_map.mpr ⟨u, hall u, rfl⟩

/-- Transport the four small-side hypotheses to the induced graph, then
lift the resulting rooted list to the ambient vertex type. -/
theorem small_side_of_induced [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {c : V} {A : Finset V} {k : ℕ} (hA : Graph189CutCore.Side G c A)
    (hconn : G.Connected) (hsize : A.card + 1 ≤ 2*k)
    (hpair : ∀ x y : V, x ≠ y → k ≤ G.degree x ∨ k ≤ G.degree y)
    (htwo : ∀ x : V, 2 ≤ G.degree x)
    (produce :
      Fintype.card (sideVerts c A) ≤ 2*k →
      (∃ u, (sideGraph G c A).Adj (sideRoot c A) u) →
      (∀ u v : sideVerts c A, u ≠ sideRoot c A → v ≠ sideRoot c A → u ≠ v →
        k ≤ (sideGraph G c A).degree u ∨ k ≤ (sideGraph G c A).degree v) →
      (∀ u : sideVerts c A, u ≠ sideRoot c A → 2 ≤ (sideGraph G c A).degree u) →
      ∃ L : List (sideVerts c A), L.head? = some (sideRoot c A) ∧ L.Nodup ∧
        L.IsChain (sideGraph G c A).Adj ∧ ∀ u, u ∈ L) :
    ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ x, x ∈ L ↔ x = c ∨ x ∈ A := by
  apply lift_rooted_list
  apply produce
  · rw [card_side hA]
    exact hsize
  · obtain ⟨x, hx, hxc⟩ := hA.contact hconn
    exact ⟨⟨x, Finset.mem_insert_of_mem hx⟩, hxc.symm⟩
  · intro u v hur hvr huv
    rw [degree_side hA u hur, degree_side hA v hvr]
    exact hpair u.val v.val (fun h => huv (Subtype.ext h))
  · intro u hur
    simpa [degree_side hA u hur] using htwo u.val

#print axioms small_side_of_induced
end Graph189InducedSide
