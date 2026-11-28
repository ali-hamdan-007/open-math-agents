import Lean.Elab.Tactic.Omega

namespace Graph189RootedSplice

private theorem accumulate (f : Nat→Nat) (a t step : Nat)
    (rise : ∀ i, a≤i → i<a+t → f i+step≤f (i+1)) :
    f a+t*step≤f (a+t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have past := ih (fun i lo hi => rise i lo (by omega))
    have last := rise (a+t) (by omega) (by omega)
    rw [Nat.succ_mul]
    change _≤f (a+t+1)
    omega

/-- With at most d−1 excess positions among d+1 gaps, two distinct
gaps attain the minimum. f records the two sentinels and the shifted
positions of the d marks. No monotonicity or normalization of f needs
to be supplied separately. -/
theorem two_tight_gaps {d m : Nat} (f : Nat → Nat) (positive : 1≤m)
    (lengths : ∀ i : Fin (d+1), m≤f (i.val+1)-f i.val-1)
    (ending : f (d+1)≤(d+1)*m+2*d) :
    ∃ i j : Fin (d+1), i<j ∧ f (i.val+1)-f i.val-1=m ∧ f (j.val+1)-f j.val-1=m := by
  let gap (i : Fin (d+1)) := f (i.val+1)-f i.val-1
  have strict (i : Nat) (hi : i<d+1) (more : gap ⟨i,hi⟩≠m) :
      f i+(m+2)≤f (i+1) := by
    have low := lengths ⟨i,hi⟩
    change m≤f (i+1)-f i-1 at low
    change f (i+1)-f i-1≠m at more
    omega
  have expand : (d+1)*(m+2)=(d+1)*m+2*d+2 := by
    simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_two,Nat.two_mul]
    omega
  have first : ∃ i : Fin (d+1), gap i=m := by
    apply Classical.byContradiction
    intro noFirst
    have all (i : Fin (d+1)) : gap i ≠ m := fun eq => noFirst ⟨i,eq⟩
    have bound := accumulate f 0 (d+1) (m+2) (fun i _ hi => strict i (by omega) (all _))
    simp only [Nat.zero_add] at bound
    omega
  obtain ⟨i,hi⟩ := first
  have other : ∃ j : Fin (d+1), j≠i ∧ gap j=m := by
    apply Classical.byContradiction
    intro none
    have away (j : Nat) (hj : j<d+1) (ji : j≠i.val) : gap ⟨j,hj⟩≠m := by
      intro eq
      exact none ⟨⟨j,hj⟩,fun same => ji (congrArg Fin.val same),eq⟩
    have left := accumulate f 0 i.val (m+2)
      (fun j _ hj => strict j (by omega) (away j (by omega) (by omega)))
    simp only [Nat.zero_add] at left
    have mid : f i.val+(m+1)≤f (i.val+1) := by
      have low := lengths i
      omega
    have right := accumulate f (i.val+1) (d-i.val) (m+2)
      (fun j lo hj => strict j (by omega) (away j (by omega) (by omega)))
    have endEq : i.val+1+(d-i.val)=d+1 := by omega
    rw [endEq] at right
    have sumEq : i.val*(m+2)+(d-i.val)*(m+2)=d*(m+2) := by
      rw [← Nat.add_mul,show i.val+(d-i.val)=d by omega]
    have lastEq : d*(m+2)+(m+1)=(d+1)*m+2*d+1 := by
      simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_two,Nat.two_mul]
      omega
    omega
  obtain ⟨j,ji,hj⟩ := other
  by_cases less : j<i
  · exact ⟨j,i,less,hj,hi⟩
  · have diff : j.val≠i.val := fun eq => ji (Fin.ext eq)
    exact ⟨i,j,by change i.val<j.val; change ¬j.val<i.val at less; omega,hi,hj⟩

#print axioms two_tight_gaps
end Graph189RootedSplice
