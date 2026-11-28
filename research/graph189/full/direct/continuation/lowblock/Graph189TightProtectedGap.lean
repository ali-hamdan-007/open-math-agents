import Graph189MatchedOrder

namespace Graph189ExteriorGap

/-- On a protected path the short interval may be the prefix, suffix, or
one internal gap. When every gap is nonempty, the order cap forces one
other interval to have exactly the size of the exterior. -/
theorem exists_tight_protected_gap {L j m : ℕ} (t : Fin L)
    (a : Fin (j+1) ↪o Fin L)
    (prefix_pos : 0 < (a 0).val)
    (suffix_pos : (a (Fin.last j)).val+1 < L)
    (gap_pos : ∀ i : Fin j, (a i.castSucc).val+2 ≤ (a i.succ).val)
    (prefix_min : a 0 ≤ t → m ≤ (a 0).val)
    (suffix_min : t ≤ a (Fin.last j) → (a (Fin.last j)).val+1+m ≤ L)
    (gap_min : ∀ i : Fin j, a i.succ ≤ t ∨ t ≤ a i.castSucc →
      (a i.castSucc).val+1+m ≤ (a i.succ).val)
    (cap : L ≤ (j+1)*m+2*(j+1)) :
    (a 0 ≤ t ∧ (a 0).val=m) ∨
    (t ≤ a (Fin.last j) ∧ (a (Fin.last j)).val+1+m=L) ∨
    ∃ i : Fin j, (a i.succ ≤ t ∨ t ≤ a i.castSucc) ∧
      (a i.castSucc).val+1+m=(a i.succ).val := by
  by_contra! fail
  obtain ⟨first,last,inside⟩ := fail
  let pos (i : Fin (j+1)) := (a i).val + if t < a i then m else 0
  have base : m+1 ≤ pos 0 := by
    by_cases h : t < a 0
    · simp only [pos,if_pos h]; omega
    have le := le_of_not_gt h
    have := first le
    have := prefix_min le
    simp only [pos,if_neg h]; omega
  have step (i : Fin j) : pos i.castSucc+(m+2) ≤ pos i.succ := by
    have ordered := a.strictMono i.castSucc_lt_succ
    by_cases l : t < a i.castSucc
    · have h : a i.succ ≤ t ∨ t ≤ a i.castSucc := Or.inr l.le
      have := gap_min i h
      have := inside i h
      simp only [pos,if_pos l,if_pos (l.trans ordered)]; omega
    by_cases r : t < a i.succ
    · have := gap_pos i
      simp only [pos,if_neg l,if_pos r]; omega
    have h : a i.succ ≤ t ∨ t ≤ a i.castSucc := Or.inl (le_of_not_gt r)
    have := gap_min i h
    have := inside i h
    simp only [pos,if_neg l,if_neg r]; omega
  have acc (i : Fin (j+1)) : m+1+i.val*(m+2) ≤ pos i := by
    induction i using Fin.induction with
    | zero => simpa using base
    | succ i ih =>
      have h := step i
      simp only [Fin.val_succ,Fin.val_castSucc,Nat.succ_mul] at ih ⊢
      omega
  have finish : pos (Fin.last j)+2 ≤ L := by
    by_cases h : t < a (Fin.last j)
    · have := suffix_min h.le
      have := last h.le
      simp only [pos,if_pos h]; omega
    · simp only [pos,if_neg h]; omega
  have lower := acc (Fin.last j)
  simp only [Fin.val_last,Nat.mul_add,Nat.succ_mul] at lower cap
  omega

#print axioms exists_tight_protected_gap
end Graph189ExteriorGap
