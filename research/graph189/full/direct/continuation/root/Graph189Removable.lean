import Graph189Atom
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Max

open Finset SimpleGraph
namespace Graph189Removable
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A fragment bounds the degree of every one of its vertices by its own
order minus one plus the size of its separating cut. -/
theorem degree_in_side {A B S : Finset V} (l : Graph189CutSides.CutSides G A B S)
    {v : V} (hv : v ∈ A) : G.degree v + 1 ≤ A.card + S.card := by
  classical
  have incl : G.neighborFinset v ⊆ A.erase v ∪ S := by
    intro y hy
    have edge := (G.mem_neighborFinset _ _).mp hy
    rcases l.cover y with h | h | h
    · exact mem_union_left _ (mem_erase.mpr ⟨edge.ne.symm,h⟩)
    · exact (l.no_cross v hv y h edge).elim
    · exact mem_union_right _ h
  have h := (card_le_card incl).trans (card_union_le _ _)
  rw [G.card_neighborFinset_eq_degree] at h
  have e := card_erase_of_mem hv
  have pos := card_pos.mpr (show A.Nonempty from ⟨v,hv⟩)
  omega

/-- The finite-graph critical-connectivity bound, in the form needed for
the completion at a removable vertex. If 2(δ+1)>3s, some vertex belongs to
no minimum separator of size s. -/
theorem exists_outside_every_min_cut {s : ℕ}
    (hasCut : ∃ A B S : Finset V, S.card = s ∧ Graph189CutSides.CutSides G A B S)
    (minCut : ∀ {U W K : Finset V}, Graph189CutSides.CutSides G U W K → s ≤ K.card)
    (degree : 3*s < 2*(G.minDegree+1)) :
    ∃ v : V, ∀ {C D T : Finset V}, Graph189CutSides.CutSides G C D T → T.card = s → v ∉ T := by
  classical
  let family : Finset (Finset V) := univ.filter fun X =>
    ∃ B S : Finset V, S.card = s ∧ Graph189CutSides.CutSides G X B S
  obtain ⟨A0,B0,S0,hs0,l0⟩ := hasCut
  have h0 : A0 ∈ family := mem_filter.mpr ⟨mem_univ _,B0,S0,hs0,l0⟩
  obtain ⟨A,hA,hmin⟩ := family.exists_min_image Finset.card ⟨A0,h0⟩
  obtain ⟨B,S,hs,l⟩ := (mem_filter.mp hA).2
  obtain ⟨v,hv⟩ := l.left_nonempty
  have d := degree_in_side l hv
  have mv := G.minDegree_le_degree v
  refine ⟨v,?_⟩
  intro C D T r ht vin
  have meet : (A ∩ T).Nonempty := ⟨v,mem_inter.mpr ⟨hv,vin⟩⟩
  have atom {U W K : Finset V} (q : Graph189CutSides.CutSides G U W K)
      (eq : K.card = S.card) : A.card ≤ U.card :=
    hmin U (mem_filter.mpr ⟨mem_univ _,W,K,eq.trans hs,q⟩)
  have bound {U W K : Finset V} (q : Graph189CutSides.CutSides G U W K) : S.card ≤ K.card :=
    hs ▸ minCut q
  have half := (Graph189Atom.in_cut l r (ht.trans hs.symm) bound atom meet).2
  omega

#print axioms degree_in_side
#print axioms exists_outside_every_min_cut
end Graph189Removable
