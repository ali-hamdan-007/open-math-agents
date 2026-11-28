import Graph189ProtectedGapCount

open Finset
namespace Graph189ContactGroupCensus

/-- With sentinels before and after the path, f (i+1)-f i-1 counts unmarked
vertices in the ith gap. The q marked vertices and all gaps partition the path. -/
theorem width_sum (f : ℕ→ℕ) (q : ℕ) (zero : f 0=0)
    (strict : ∀ i j, i<j → j≤q+1 → f i<f j) :
    (∑ i∈range (q+1), (f (i+1)-f i-1))+(q+1)=f (q+1) := by
  have result (j : ℕ) (hj : j≤q+1) :
      (∑ i∈range j, (f (i+1)-f i-1))+j=f j := by
    induction j with
    | zero => simp [zero]
    | succ j ih =>
      have last := ih (by omega)
      have grow := strict j (j+1) (by omega) hj
      rw [sum_range_succ]
      omega
  exact result _ le_rfl

/-- The only permitted interval without a full detour contains t strictly
between its bounding sentinels. Consequently a grouped mark list satisfying
the local graph detours meets the global row-census budget. -/
theorem path_group_census {E : Type*} [Fintype E] [DecidableEq E]
    {q m L : ℕ} (ports : Fin q → Finset E) (f : ℕ→ℕ) (t : ℕ)
    (zero : f 0=0) (ending : f (q+1)=L+1)
    (strict : ∀ i j, i<j → j≤q+1 → f i<f j)
    (positive : 1≤m)
    (detour : ∀ i∈insert q ((beginnings ports).image Fin.val),
      t<f i ∨ f (i+1)≤t+1 → m≤f (i+1)-f i-1) :
    q+(beginnings ports).card*m+1≤L := by
  classical
  let A := (beginnings ports).image Fin.val
  let I := insert q A
  let h := fun i => f (i+1)-f i-1
  have real (i : ℕ) (member : i∈A) : i<q := by
    obtain ⟨j,_,rfl⟩ := mem_image.mp member
    exact j.isLt
  have miss : q∉A := fun member => (lt_irrefl _) (real _ member)
  have number : I.card=(beginnings ports).card+1 := by
    rw [show I=insert q A from rfl,card_insert_of_notMem miss,
      show A.card=(beginnings ports).card from card_image_of_injective _ Fin.val_injective]
  have limited {i : ℕ} (hi : i∈I) : i≤q := by
    rcases mem_insert.mp hi with rfl|inA
    · exact le_rfl
    · exact (real _ inA).le
  have contains (i : ℕ) (hi : i∈I) (small : h i<m) :
      f i≤t ∧ t+1<f (i+1) := by
    have neg : ¬(t<f i ∨ f (i+1)≤t+1) := fun safe => (not_lt_of_ge (detour i hi safe)) small
    omega
  have distinct {i j : ℕ} (hi : i∈I) (hj : j∈I) (si : h i<m) (sj : h j<m) (lt : i<j) : False := by
    have coverI := contains i hi si
    have coverJ := contains j hj sj
    have bound := limited hj
    have order : f (i+1)≤f j := by
      rcases eq_or_lt_of_le (by omega : i+1≤j) with eq|less
      · exact eq ▸ le_rfl
      · exact (strict (i+1) j less (by omega)).le
    omega
  have cost := protected_gap_sum I h number positive
    (fun i hi low => by have := contains i hi low; dsimp [h]; omega)
    (fun i hi j hj si sj => by
      rcases lt_trichotomy i j with lt|eq|lt
      · exact (distinct hi hj si sj lt).elim
      · exact eq
      · exact (distinct hj hi sj si lt).elim)
  have sub : I⊆range (q+1) := fun i hi => mem_range.mpr (by have := limited hi; omega)
  have total := sum_le_sum_of_subset_of_nonneg (f:=h) sub (fun i _ _ => Nat.zero_le _)
  have sum := width_sum f q zero strict
  rw [ending] at sum
  change (∑ i∈range (q+1),h i)+(q+1)=L+1 at sum
  omega

end Graph189ContactGroupCensus
