import Graph189GroupedContactIntervals

open Finset
namespace Graph189ContactGroupCensus

/-- Coordinates of two full unmarked intervals avoiding the protected vertex.
The i-th interval is [f i, f(i+1)-1), in zero-based path coordinates. -/
theorem two_swappable_intervals {u m L : ℕ} (f : ℕ→ℕ) (t : ℕ)
    (zero : f 0=0) (ending : f (u+1)=L+1)
    (strict : ∀ i j, i<j → j≤u+1 → f i<f j)
    (balance : u≤m) (room : L+m+2≤(u+1)*(m+1)+u)
    (lower : ∀ i≤u, t<f i ∨ f (i+1)≤t+1 → m≤f (i+1)-f i-1) :
    ∃ i j, i<j ∧ j≤u ∧ (t<f i ∨ f (i+1)≤t+1) ∧ (t<f j ∨ f (j+1)≤t+1) ∧
      f (i+1)-f i-1=m ∧ f (j+1)-f j-1=m := by
  classical
  let len := fun i => f (i+1)-f i-1
  let safe := fun i => t<f i ∨ f (i+1)≤t+1
  let A := range (u+1)
  have total := width_sum f u zero strict
  rw [ending] at total
  change (∑ i∈A,len i)+(u+1)=L+1 at total
  have capacity : (∑ i∈A,len i)+1≤u*m+u := by
    simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one] at room
    omega
  have count : A.card=u+1 := card_range _
  obtain ⟨v,hv,root⟩ : ∃ v∈A, ¬safe v := by
    by_contra! all
    have high := sum_le_sum (s:=A) (f:=fun _ => m) (g:=len)
      (fun i hi => lower i (Nat.le_of_lt_succ (mem_range.mp hi)) (all i hi))
    rw [sum_const,Nat.nsmul_eq_mul,count,Nat.add_mul,Nat.one_mul] at high
    omega
  let B := A.erase v
  have size : B.card=u := by simp [B,card_erase_of_mem hv,count]
  have insideV : f v≤t ∧ t+1<f (v+1) := by change ¬(_∨_) at root; omega
  have weight : 1≤len v := by dsimp [len]; omega
  have outside {i j : ℕ} (hi : i∈A) (hj : j∈A) (ordered : i<j) :
      safe i ∨ safe j := by
    have ord : f (i+1)≤f j := by
      rcases eq_or_lt_of_le (by omega : i+1≤j) with eq|lt
      · rw [eq]
      · exact (strict _ _ lt (Nat.le_of_lt (mem_range.mp hj))).le
    change (_∨_) ∨ (_∨_)
    omega
  have legal (i : ℕ) (hi : i∈B) : safe i := by
    obtain ⟨ne,hit⟩ := mem_erase.mp hi
    rcases lt_or_gt_of_ne ne with lt|lt
    · exact (outside hit hv lt).resolve_right root
    · exact (outside hv hit lt).resolve_left root
  have part := sum_erase_add (s:=A) len hv
  change (∑ i∈B,len i)+len v=_ at part
  obtain ⟨i,hi,j,hj,ne,li,lj⟩ := two_full_gaps B len size.ge
    (fun i h => lower i (Nat.le_of_lt_succ (mem_range.mp (mem_erase.mp h).2)) (legal i h)) (by omega)
  have ib : i≤u := Nat.le_of_lt_succ (mem_range.mp (mem_erase.mp hi).2)
  have jb : j≤u := Nat.le_of_lt_succ (mem_range.mp (mem_erase.mp hj).2)
  rcases lt_or_gt_of_ne ne with lt|lt
  · exact ⟨i,j,lt,jb,legal i hi,legal j hj,li,lj⟩
  · exact ⟨j,i,lt,ib,legal j hj,legal i hi,lj,li⟩

#print axioms two_swappable_intervals
end Graph189ContactGroupCensus
