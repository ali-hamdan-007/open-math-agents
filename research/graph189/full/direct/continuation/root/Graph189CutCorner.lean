import Graph189CutSides

namespace Graph189CutCorner
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable {A B S C D T : Finset V}

omit [Fintype V] in
theorem three_parts (l : Graph189CutSides.CutSides G A B S) (X : Finset V) :
    (X ∩ A).card + (X ∩ S).card + (X ∩ B).card = X.card := by
  have dis (P Q : Finset V) (h : Disjoint P Q) : Disjoint (X ∩ P) (X ∩ Q) :=
    Finset.disjoint_left.mpr (fun _ i j => Finset.disjoint_left.mp h (mem_inter.mp i).2 (mem_inter.mp j).2)
  have full : (X ∩ A) ∪ (X ∩ S) ∪ (X ∩ B) = X := by
    ext u
    simp only [mem_union,mem_inter]
    rcases l.cover u with hu | hu | hu <;> tauto
  rw [← card_union_of_disjoint (dis _ _ l.left_cut),
    ← card_union_of_disjoint (disjoint_union_left.mpr ⟨dis _ _ l.apart,dis _ _ l.right_cut.symm⟩),full]

def boundary (A S C T : Finset V) := ((A ∩ T) ∪ (S ∩ T)) ∪ (S ∩ C)

omit [Fintype V] in
theorem boundary_card (l : Graph189CutSides.CutSides G A B S)
    (r : Graph189CutSides.CutSides G C D T) :
    (boundary A S C T).card = (A ∩ T).card + (S ∩ T).card + (S ∩ C).card := by
  have x : Disjoint (A ∩ T) (S ∩ T) := Finset.disjoint_left.mpr (fun _ p q =>
    Finset.disjoint_left.mp l.left_cut (mem_inter.mp p).1 (mem_inter.mp q).1)
  have y : Disjoint (A ∩ T) (S ∩ C) := Finset.disjoint_left.mpr (fun _ p q =>
    Finset.disjoint_left.mp l.left_cut (mem_inter.mp p).1 (mem_inter.mp q).1)
  have z : Disjoint (S ∩ T) (S ∩ C) := Finset.disjoint_left.mpr (fun _ p q =>
    Finset.disjoint_left.mp r.left_cut (mem_inter.mp q).2 (mem_inter.mp p).2)
  rw [boundary,card_union_of_disjoint (disjoint_union_left.mpr ⟨y,z⟩),card_union_of_disjoint x]

/-- The corner of two separations is itself separated by its two cut strips
and their common square. The entire original opposite side B survives. -/
theorem corner (l : Graph189CutSides.CutSides G A B S) (r : Graph189CutSides.CutSides G C D T)
    (nonempty : (A ∩ C).Nonempty) :
    ∃ F, Graph189CutSides.CutSides G (A ∩ C) F (boundary A S C T) := by
  classical
  let U := A ∩ C
  let K := boundary A S C T
  let F := univ \ (U ∪ K)
  have bk {v} (hv : v ∈ B) : v ∉ K := by
    intro h
    rcases mem_union.mp h with h | h
    · rcases mem_union.mp h with h | h
      · exact Finset.disjoint_left.mp l.apart (mem_inter.mp h).1 hv
      · exact Finset.disjoint_left.mp l.right_cut hv (mem_inter.mp h).1
    · exact Finset.disjoint_left.mp l.right_cut hv (mem_inter.mp h).1
  obtain ⟨b,hb⟩ := l.right_nonempty
  have bu : b ∉ U := fun h => Finset.disjoint_left.mp l.apart (mem_inter.mp h).1 hb
  have ff : b ∈ F := mem_sdiff.mpr ⟨mem_univ _,fun h => (mem_union.mp h).elim bu (bk hb)⟩
  have uk : Disjoint U K := by
    apply Finset.disjoint_left.mpr
    intro v huv hkv
    obtain ⟨a,c⟩ := mem_inter.mp huv
    rcases mem_union.mp hkv with h | h
    · rcases mem_union.mp h with h | h
      · exact Finset.disjoint_left.mp r.left_cut c (mem_inter.mp h).2
      · exact Finset.disjoint_left.mp l.left_cut a (mem_inter.mp h).1
    · exact Finset.disjoint_left.mp l.left_cut a (mem_inter.mp h).1
  refine ⟨F,⟨nonempty,⟨b,ff⟩,?_,uk,?_,?_,?_⟩⟩
  · exact Finset.disjoint_left.mpr (fun _ hu hf => (mem_sdiff.mp hf).2 (mem_union_left _ hu))
  · exact Finset.disjoint_left.mpr (fun _ hf hk => (mem_sdiff.mp hf).2 (mem_union_right _ hk))
  · intro v
    by_cases hu : v ∈ U
    · exact Or.inl hu
    by_cases hk : v ∈ K
    · exact Or.inr (Or.inr hk)
    exact Or.inr (Or.inl (mem_sdiff.mpr ⟨mem_univ _,fun h => (mem_union.mp h).elim hu hk⟩))
  · intro u hu v hv edge
    obtain ⟨ua,uc⟩ := mem_inter.mp hu
    have no := (mem_sdiff.mp hv).2
    rcases l.cover v with va | vb | vs
    · rcases r.cover v with vc | vd | vt
      · exact no (mem_union_left _ (mem_inter.mpr ⟨va,vc⟩))
      · exact r.no_cross u uc v vd edge
      · exact no (mem_union_right _ (mem_union_left _ (mem_union_left _ (mem_inter.mpr ⟨va,vt⟩))))
    · exact l.no_cross u ua v vb edge
    · rcases r.cover v with vc | vd | vt
      · exact no (mem_union_right _ (mem_union_right _ (mem_inter.mpr ⟨vs,vc⟩)))
      · exact r.no_cross u uc v vd edge
      · exact no (mem_union_right _ (mem_union_left _ (mem_union_right _ (mem_inter.mpr ⟨vs,vt⟩))))

#print axioms three_parts
#print axioms boundary_card
#print axioms corner
end Graph189CutCorner
