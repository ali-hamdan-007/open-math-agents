import Graph189TightProtectedGap
import Mathlib.Data.Finset.Sort

namespace Graph189ExteriorGap
open Finset

/-- The tight gap comes with its actual bounding marks, and has no mark
strictly inside it.  An absent boundary denotes the beginning or end. -/
theorem locate_tight_protected_gap {L j m : ℕ} (t : Fin L)
    (M : Finset (Fin L)) (count : M.card=j+1) (positive : 0<m)
    (prefix_pos : 0 < (M.orderEmbOfFin count 0).val)
    (suffix_pos : (M.orderEmbOfFin count (Fin.last j)).val+1 < L)
    (gap_pos : ∀ i : Fin j, (M.orderEmbOfFin count i.castSucc).val+2 ≤ (M.orderEmbOfFin count i.succ).val)
    (prefix_min : M.orderEmbOfFin count 0 ≤ t → m ≤ (M.orderEmbOfFin count 0).val)
    (suffix_min : t ≤ M.orderEmbOfFin count (Fin.last j) →
      (M.orderEmbOfFin count (Fin.last j)).val+1+m ≤ L)
    (gap_min : ∀ i : Fin j, M.orderEmbOfFin count i.succ ≤ t ∨ t ≤ M.orderEmbOfFin count i.castSucc →
      (M.orderEmbOfFin count i.castSucc).val+1+m ≤ (M.orderEmbOfFin count i.succ).val)
    (cap : L ≤ (j+1)*m+2*(j+1)) :
    ∃ lo hi, lo < hi ∧ hi ≤ L ∧ hi-lo=m ∧ (t.val < lo ∨ hi ≤ t.val) ∧
      (lo=0 ∨ ∃ i∈M, i.val+1=lo) ∧ (hi=L ∨ ∃ i∈M, i.val=hi) ∧
      (0<lo ∨ hi<L) ∧ ∀ i∈M, i.val<lo ∨ hi ≤ i.val := by
  let a := M.orderEmbOfFin count
  have marked (i : Fin (j+1)) : a i ∈ M := M.orderEmbOfFin_mem count i
  have preimage (i : Fin L) (hi : i∈M) : ∃ h, a h=i := by
    change i ∈ Set.range (M.orderEmbOfFin count)
    rwa [M.range_orderEmbOfFin]
  rcases exists_tight_protected_gap t a prefix_pos suffix_pos gap_pos prefix_min suffix_min gap_min cap
      with ⟨safe,size⟩ | ⟨safe,size⟩ | ⟨d,safe,size⟩
  · refine ⟨0,(a 0).val,by omega,(a 0).isLt.le,by omega,Or.inr safe,Or.inl rfl,
      Or.inr ⟨_,marked 0,rfl⟩,Or.inr (a 0).isLt,?_⟩
    intro i hi
    obtain ⟨d,rfl⟩ := preimage i hi
    exact Or.inr (a.monotone (Fin.zero_le d))
  · refine ⟨(a (Fin.last j)).val+1,L,by omega,le_rfl,by omega,Or.inl ?_,
      Or.inr ⟨_,marked _,rfl⟩,Or.inl rfl,Or.inl (by omega),?_⟩
    · change t.val ≤ (a (Fin.last j)).val at safe
      omega
    · intro i hi
      obtain ⟨d,rfl⟩ := preimage i hi
      exact Or.inl (Nat.lt_succ_of_le (show (a d).val ≤ (a (Fin.last j)).val from a.monotone (Fin.le_last d)))
  · refine ⟨(a d.castSucc).val+1,(a d.succ).val,by omega,(a d.succ).isLt.le,by omega,?_,
      Or.inr ⟨_,marked _,rfl⟩,Or.inr ⟨_,marked _,rfl⟩,Or.inl (by omega),?_⟩
    · rcases safe with left|right
      · exact Or.inr left
      · exact Or.inl (Nat.lt_succ_of_le right)
    · intro i hi
      obtain ⟨h,rfl⟩ := preimage i hi
      by_cases small : h ≤ d.castSucc
      · exact Or.inl (Nat.lt_succ_of_le (show (a h).val ≤ (a d.castSucc).val from a.monotone small))
      · exact Or.inr (a.monotone (show d.succ ≤ h by
          change ¬ h.val ≤ d.val at small
          change d.val+1 ≤ h.val
          omega))

#print axioms locate_tight_protected_gap
end Graph189ExteriorGap
