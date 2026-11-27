import Graph199CliqueQuotient
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace Graph199

open Finset SimpleGraph

/-- A clique with a common attachment vertex can be traversed between two
external vertices if at least one of them has an additional attachment. -/
theorem clique_branch_ports {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (C : Finset V) (hC : G.IsClique (C : Set V)) {a b r : V}
    (hr : r ∈ C) (ha : G.Adj a r) (hb : G.Adj b r)
    (hextra : ∃ v ∈ C, v ≠ r ∧ (G.Adj a v ∨ G.Adj b v)) :
    ∃ L : List V, L.Nodup ∧ L.IsChain G.Adj ∧ (∀ x, x ∈ L ↔ x ∈ C) ∧
      (∀ x ∈ L.head?, G.Adj a x) ∧ (∀ x ∈ L.getLast?, G.Adj x b) := by
  have build (x y : V) (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y)
      (hax : G.Adj a x) (hyb : G.Adj y b) :
      ∃ L : List V, L.Nodup ∧ L.IsChain G.Adj ∧ (∀ z, z ∈ L ↔ z ∈ C) ∧
        (∀ z ∈ L.head?, G.Adj a z) ∧ (∀ z ∈ L.getLast?, G.Adj z b) := by
    let middle := ((C.erase x).erase y).toList
    let L := x :: (middle ++ [y])
    have hm z : z ∈ middle ↔ z ≠ y ∧ z ≠ x ∧ z ∈ C := by simp [middle]
    have hs z : z ∈ L ↔ z ∈ C := by
      simp only [L,List.mem_cons,List.mem_append,List.not_mem_nil,or_false,hm]
      constructor
      · rintro (rfl | h | rfl)
        · exact hx
        · exact h.2.2
        · exact hy
      · intro h
        by_cases hzx : z = x
        · exact Or.inl hzx
        by_cases hzy : z = y
        · exact Or.inr (Or.inr hzy)
        exact Or.inr (Or.inl ⟨hzy,hzx,h⟩)
    have hn : L.Nodup := by
      apply List.nodup_cons.mpr
      constructor
      · simp [hm,hxy]
      · apply List.nodup_append.mpr
        refine ⟨Finset.nodup_toList _,by simp,?_⟩
        intro u hu w hw he
        have hw' : w = y := by simpa using hw
        exact ((hm u).mp hu).1 (he.trans hw')
    refine ⟨L,hn,?_,hs,?_,?_⟩
    · exact List.Pairwise.isChain (hn.imp_of_mem (fun {_ _} h1 h2 h => hC ((hs _).mp h1) ((hs _).mp h2) h))
    · simpa [L] using hax
    · simpa [L,List.getLast?_cons,List.getLast?_append] using hyb
  obtain ⟨v,hv,hne,hvA | hvB⟩ := hextra
  · exact build v r hv hr hne hvA hb.symm
  · exact build r v hr hv hne.symm ha hvB.symm

#print axioms clique_branch_ports

end Graph199
