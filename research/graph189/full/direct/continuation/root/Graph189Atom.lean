import Graph189AtomCounts
import Graph189CutCorner

open Finset SimpleGraph
namespace Graph189Atom
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable {A B S C D T : Finset V}

/-- A minimum separator meeting a minimum-order fragment contains the whole
fragment; the fragment has at most half the connectivity. -/
theorem in_cut (l : Graph189CutSides.CutSides G A B S) (r : Graph189CutSides.CutSides G C D T)
    (same : T.card = S.card)
    (minCut : ∀ {U W K : Finset V}, Graph189CutSides.CutSides G U W K → S.card ≤ K.card)
    (atom : ∀ {U W K : Finset V}, Graph189CutSides.CutSides G U W K →
      K.card = S.card → A.card ≤ U.card)
    (meet : (A ∩ T).Nonempty) : A ⊆ T ∧ 2*A.card ≤ S.card := by
  classical
  have floor {U W L M : Finset V} (left : Graph189CutSides.CutSides G U W S)
      (right : Graph189CutSides.CutSides G L M T) (h : 0 < (U ∩ L).card) :
      S.card ≤ (U ∩ T).card+(S ∩ T).card+(S ∩ L).card := by
    obtain ⟨F,c⟩ := Graph189CutCorner.corner left right (card_pos.mp h)
    simpa only [← Graph189CutCorner.boundary_card left right] using minCut c
  have strict {L M : Finset V} (right : Graph189CutSides.CutSides G L M T)
      (h : 0 < (A ∩ L).card) (hlt : (A ∩ L).card < A.card) :
      S.card < (A ∩ T).card+(S ∩ T).card+(S ∩ L).card := by
    obtain ⟨F,c⟩ := Graph189CutCorner.corner l right (card_pos.mp h)
    have lower := minCut c
    have diff : (Graph189CutCorner.boundary A S L T).card ≠ S.card :=
      fun eq => (not_lt_of_ge (atom c eq)) hlt
    rw [← Graph189CutCorner.boundary_card l right]
    omega
  have aSize := Graph189CutCorner.three_parts r A
  have sSize := Graph189CutCorner.three_parts r S
  have tSize := Graph189CutCorner.three_parts l T
  have cSize := Graph189CutCorner.three_parts l C
  have dSize := Graph189CutCorner.three_parts l D
  simp only [inter_comm T A,inter_comm T S,inter_comm T B] at tSize
  simp only [inter_comm C A,inter_comm C S,inter_comm C B] at cSize
  simp only [inter_comm D A,inter_comm D S,inter_comm D B] at dSize
  have met := card_pos.mpr meet
  obtain ⟨lac,lad,half⟩ := Graph189AtomCounts.atom_count aSize.symm sSize.symm
    (tSize.trans same).symm (cSize ▸ atom r same) (dSize ▸ atom r.swap same)
    (fun h => strict r h (by omega)) (fun h => strict r.swap h (by omega))
    (floor l.swap r) (floor l.swap r.swap)
  refine ⟨?_,half⟩
  intro x hx
  rcases r.cover x with c | d | t
  · have h := card_pos.mpr (show (A ∩ C).Nonempty from ⟨x,mem_inter.mpr ⟨hx,c⟩⟩)
    omega
  · have h := card_pos.mpr (show (A ∩ D).Nonempty from ⟨x,mem_inter.mpr ⟨hx,d⟩⟩)
    omega
  · exact t

#print axioms in_cut
end Graph189Atom
