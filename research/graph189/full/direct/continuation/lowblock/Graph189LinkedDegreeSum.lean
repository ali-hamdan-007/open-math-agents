import Graph189UpstreamBondy

/- The connector construction and successor count are from @koolkao's
accepted Bondy proof, PR 7971. We retain the actual degrees of its distinct
successors and exterior witness in the final count. -/
open SimpleGraph Finset OMA.BondyK
namespace Graph189LinkedDegreeSum
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : ℕ} {f : ℕ → V} {H : Finset V}

private theorem successor_set (hD : Cy G c f) {q : ℕ} {s : ℕ → ℕ}
    (hs : ∀ i j, i<j → j≤q → s i<s j) (period : s q=s 0+c) :
    ∃T : Finset V, T.card=q ∧ (∑ v∈T,G.degree v)=
      (∑ i∈range q,G.degree (f (s i+1))) ∧ ∀ v∈T,∃t,f t=v := by
  let a (i : ℕ) := f (s i+1)
  have inj : Set.InjOn a (range q : Finset ℕ) := by
    intro i hi j hj eq
    have hi' := mem_range.mp hi
    have hj' := mem_range.mp hj
    have bounds {l : ℕ} (hl : l<q) : s 0+1≤s l+1 ∧ s l+1<s 0+1+c := by
      have up := hs l q hl le_rfl
      rcases Nat.eq_zero_or_pos l with rfl|pos
      · constructor <;> omega
      have lo := hs 0 l pos hl.le
      omega
    by_contra ne
    have diff : s i+1≠s j+1 := by
      rcases lt_or_gt_of_ne ne with lt|gt
      · have := hs i j lt hj'.le; omega
      · have := hs j i gt hi'.le; omega
    exact hD.ne_of_window (bounds hi').1 (bounds hi').2 (bounds hj').1 (bounds hj').2 diff eq
  refine ⟨(range q).image a,by rw [card_image_of_injOn inj,card_range],
    sum_image (fun i hi j hj eq => inj hi hj eq),?_⟩
  intro v hv
  obtain ⟨i,_,rfl⟩ := mem_image.mp hv
  exact ⟨s i+1,rfl⟩

/-- The linked-set contradiction with a degree-sum requirement on distinct
vertices. This permits one exceptional degree in the original graph. -/
theorem linked_contra_sum (hD : Cy G c f) (hC : Comp G f H) {k : ℕ}
    (hk : 1 ≤ k) (hkn : ∀ T : Finset V, T.card=k+1 → Fintype.card V+k*(k-1)≤∑ v∈T,G.degree v) (hK : KSep G k)
    {D : Finset V} (hDH : D ⊆ H) (hDk : k + 1 ≤ D.card)
    (hDl : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → ∃ X, HP G D x y X ∧ k ≤ X.length) : False := by
  set Cs := (Finset.range c).image f with hCs
  have hsepk := sep_ge hD hC hK hDH hDk
  have hHD : D.card ≤ H.card := Finset.card_le_card hDH
  have hk1 : k * (k - 1) + k = k * k := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩; simp; ring
  by_cases h : ∀ S : Finset V, (∀ l, ABP G D Cs l → ∃ x ∈ l, x ∈ S) → k + 1 ≤ S.card
  · obtain ⟨P, hP, hdisj⟩ := menger_trim D Cs (k + 1) h
    obtain ⟨s, hs, hsq, hatt, hph, -⟩ := ends_sorted hD hC hDH hDl (by omega) P hP hdisj
    have := succ_deg hD hC (q := k + 1) (by omega) hs hsq hatt
      (fun i hi j hj hij => by simpa using hph i hi j hj hij)
    obtain ⟨T,card,eq,_⟩ := successor_set hD hs hsq
    have hsum := hkn T card
    rw [eq] at hsum
    have e : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
    omega
  · push_neg at h
    obtain ⟨S, hS, hSk⟩ := h
    have hSc : S.card = k := le_antisymm (by omega) (hsepk S hS)
    obtain ⟨P, hP, hdisj⟩ := menger_trim D Cs k (fun S' hS' => hsepk S' hS')
    obtain ⟨s, hs, hsq, hatt, hph, hend⟩ := ends_sorted hD hC hDH hDl hk P hP hdisj
    -- every separator vertex lies on one of the paths
    have hmeet : ∀ i, ∃ x ∈ P i, x ∈ S := fun i => hS _ (hP i).1
    choose σ hσP hσS using hmeet
    have σinj : Function.Injective σ := by
      intro i j hij; by_contra hne; exact hdisj i j hne _ (hσP i) (hij ▸ hσP j)
    have himg : Finset.univ.image σ = S := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx; obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx; exact hσS i
      · rw [Finset.card_image_of_injective _ σinj, hSc]; simp
    have onP : ∀ x ∈ S, ∃ i, x ∈ P i := by
      intro x hx; rw [← himg] at hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx; exact ⟨i, hσP i⟩
    obtain ⟨v, hvD, hvS⟩ : ∃ v ∈ D, v ∉ S := by
      by_contra h'; push_neg at h'
      have := Finset.card_le_card (show D ⊆ S from h'); omega
    have hvH := hDH hvD
    have hN : ∀ t, G.Adj v (f t) → ∃ j < k, f t = f (s j) := by
      intro t hvt
      have hl : ABP G D Cs [v, f t] := ⟨by simp; intro h; exact hC.off v hvH t h.symm,
        by simp [hvt], ⟨v, hvD, rfl⟩, ⟨f t, hD.mem_cset t, rfl⟩⟩
      obtain ⟨x, hx, hxS⟩ := hS _ hl
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact absurd hxS hvS
      · obtain ⟨i, hi⟩ := onP _ hxS
        obtain ⟨j, hj, hjl⟩ := hend i
        refine ⟨j, hj, ?_⟩
        have hne : P i ≠ [] := by intro h; rw [h] at hi; simp at hi
        have hsplit := List.dropLast_append_getLast hne
        rw [← hsplit] at hi
        rcases List.mem_append.mp hi with h1 | h1
        · exact absurd (hD.mem_cset t) ((hP i).2.2 _ h1)
        · simp at h1
          rw [List.getLast?_eq_getLast_of_ne_nil hne] at hjl
          simp at hjl; rw [h1, hjl]
    have hv := vert_deg hD hC hvH hN
    have hsd := succ_deg hD hC (q := k) hk hs hsq hatt
      (fun i hi j hj hij => (hph i hi j hj hij).mono (by omega))
    obtain ⟨T,card,eq,on⟩ := successor_set hD hs hsq
    have absent : v∉T := fun mem => by
      obtain ⟨t,ht⟩ := on v mem
      exact hC.off v hvH t ht
    have hsum := hkn (insert v T) (by rw [card_insert_of_notMem absent,card])
    rw [sum_insert absent,eq] at hsum
    omega

#print axioms linked_contra_sum
end Graph189LinkedDegreeSum
