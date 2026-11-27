import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace Graph189ExclusiveCover

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Vertices outside a private remote set that can reach it by a remote edge. -/
def boundary (R : Finset V) : Finset V :=
  (univ \ R).filter (fun x => (G.neighborFinset x ∩ R).Nonempty)

theorem exclusive_cover {U : Finset V} {R visible : Fin 3 → Finset V} {k : ℕ}
    (hTag : ∀ x ∈ U, ∃ i, x ∈ visible i ∧ ∀ j, x ∈ R j → j = i)
    (hVis : ∀ i, (visible i).card < k)
    (hDegree : ∀ x ∈ U, k ≤ (insert x (G.neighborFinset x)).card)
    (hPrivate : ∀ i y, y ∉ visible i → ∃ j, j ≠ i ∧ y ∈ R j) :
    U ⊆ univ.biUnion (fun i => boundary G (R i)) := by
  intro x hx
  obtain ⟨i,hxi,hOnly⟩ := hTag x hx
  have hlt : (visible i).card < (insert x (G.neighborFinset x)).card :=
    (hVis i).trans_le (hDegree x hx)
  obtain ⟨y,hy,hyout⟩ := exists_mem_notMem_of_card_lt_card hlt
  have hyn : y ∈ G.neighborFinset x := by
    rcases mem_insert.mp hy with rfl | hyn
    · exact (hyout hxi).elim
    · exact hyn
  obtain ⟨j,hji,hyR⟩ := hPrivate i y hyout
  have hxR : x ∉ R j := fun h => hji (hOnly j h)
  exact mem_biUnion.mpr ⟨j,mem_univ _,mem_filter.mpr
    ⟨mem_sdiff.mpr ⟨mem_univ _,hxR⟩,⟨y,mem_inter.mpr ⟨hyn,hyR⟩⟩⟩⟩

/-- The common classes and anchor edges bound the size of the exclusive remote set. -/
theorem exclusive_impossible {U : Finset V} {M : Type*} [DecidableEq M]
    {W : Finset M} {A : Fin 3 → Finset M} {R visible : Fin 3 → Finset V}
    {b : Fin 3 → ℕ} {d k : ℕ}
    (hTag : ∀ x ∈ U, ∃ i, x ∈ visible i ∧ ∀ j, x ∈ R j → j = i)
    (hVis : ∀ i, (visible i).card < k)
    (hDegree : ∀ x ∈ U, k ≤ (insert x (G.neighborFinset x)).card)
    (hPrivate : ∀ i y, y ∉ visible i → ∃ j, j ≠ i ∧ y ∈ R j)
    (hBound : ∀ i, (boundary G (R i)).card + W.card + 1 + b i ≤ k + (A i).card)
    (hCommon : ∀ i, A i ⊆ W)
    (hUnique : ∀ i j x, x ∈ A i → x ∈ A j → i = j)
    (hSize : W.card + d + 3 = k) (hAnchor : 4 ≤ ∑ i, b i)
    (hGap : k + 2*d ≤ U.card) :
    False := by
  have hUnion := card_le_card (exclusive_cover G hTag hVis hDegree hPrivate)
  have hSum : (univ.biUnion (fun i => boundary G (R i))).card ≤
      ∑ i, (boundary G (R i)).card := card_biUnion_le
  have hDisjoint : ((↑(univ : Finset (Fin 3))) : Set (Fin 3)).PairwiseDisjoint A := by
    apply pairwiseDisjoint_iff.mpr
    intro i _ j _ h
    obtain ⟨x,hx⟩ := h
    exact hUnique i j x (mem_inter.mp hx).1 (mem_inter.mp hx).2
  have hCommonCover : univ.biUnion A ⊆ W := by
    intro x hx
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hx
    exact hCommon i hi
  have hBudget := card_le_card hCommonCover
  rw [card_biUnion hDisjoint] at hBudget
  have hAll := sum_le_sum (s := (univ : Finset (Fin 3))) (fun i _ => hBound i)
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hAll
  omega

#print axioms Graph189ExclusiveCover.exclusive_cover
#print axioms Graph189ExclusiveCover.exclusive_impossible

end Graph189ExclusiveCover
