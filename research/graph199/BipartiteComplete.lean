import BipartiteSplice

namespace BalancedBipartite

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}

/-- A complete graph between equally sized colored parts has a cyclic
spanning vertex order. -/
theorem complete_spanning_cycle [Fintype V] [DecidableEq V]
    {r : ℕ} (hr : 2 ≤ r) {col : V → Bool}
    (hfalse : (univ.filter fun v => col v = false).card = r)
    (htrue : (univ.filter fun v => col v = true).card = r)
    (hcomplete : ∀ ⦃x y⦄, col x ≠ col y → G.Adj x y) : HasSpanningCycle G := by
  classical
  let A : Finset V := univ.filter fun v => col v = false
  let B : Finset V := univ.filter fun v => col v = true
  let left : Fin r ≃ A := (Fintype.equivFinOfCardEq ((Fintype.card_coe A).trans hfalse)).symm
  let right : Fin r ≃ B := (Fintype.equivFinOfCardEq ((Fintype.card_coe B).trans htrue)).symm
  let f (i : Fin (2*r)) : V :=
    if i.val%2=0 then left ⟨i.val/2,by have := i.isLt; omega⟩
    else right ⟨i.val/2,by have := i.isLt; omega⟩
  have hL (i : Fin r) : col (left i) = false := (mem_filter.mp (left i).property).2
  have hR (i : Fin r) : col (right i) = true := (mem_filter.mp (right i).property).2
  have color_f (i : Fin (2*r)) : col (f i) = if i.val%2=0 then false else true := by
    unfold f
    split <;> simp only [*]
  have hf : Function.Injective f := by
    intro i j hij
    have hcol := congrArg col hij
    rw [color_f,color_f] at hcol
    have hpar : i.val%2=j.val%2 := by
      by_cases hi : i.val%2=0 <;> by_cases hj : j.val%2=0 <;>
        simp [hi,hj] at hcol <;> omega
    have hdiv : i.val/2=j.val/2 := by
      by_cases hi : i.val%2=0
      · have hj : j.val%2=0 := hpar.symm.trans hi
        have he : left ⟨i.val/2,by have := i.isLt; omega⟩ =
            left ⟨j.val/2,by have := j.isLt; omega⟩ :=
          Subtype.ext (by simpa [f,hi,hj] using hij)
        exact congrArg Fin.val (left.injective he)
      · have hj : j.val%2≠0 := fun he => hi (hpar.trans he)
        have he : right ⟨i.val/2,by have := i.isLt; omega⟩ =
            right ⟨j.val/2,by have := j.isLt; omega⟩ :=
          Subtype.ext (by simpa [f,hi,hj] using hij)
        exact congrArg Fin.val (right.injective he)
    exact Fin.ext (by omega)
  have hsurj : Function.Surjective f := by
    intro v
    cases hv : col v
    · have hvA : v ∈ A := by simp [A,hv]
      obtain ⟨i,hi⟩ := left.surjective ⟨v,hvA⟩
      refine ⟨⟨2*i.val,by have := i.isLt; omega⟩,?_⟩
      have he : (2*i.val)/2=i.val := by omega
      have hz : (2*i.val)%2=0 := by omega
      simp [f,hz,he,hi]
    · have hvB : v ∈ B := by simp [B,hv]
      obtain ⟨i,hi⟩ := right.surjective ⟨v,hvB⟩
      refine ⟨⟨2*i.val+1,by have := i.isLt; omega⟩,?_⟩
      have he : (2*i.val+1)/2=i.val := by omega
      simp [f,he,hi]
  let l := List.ofFn f
  have hl : l.length=2*r := List.length_ofFn
  have hne : l ≠ [] := by
    intro he
    rw [he] at hl
    simp at hl
    omega
  have hget (i : ℕ) (hi : i<l.length) :
      l[i] = f ⟨i,by omega⟩ := by simp [l]
  have hc : l.IsChain G.Adj := by
    apply List.isChain_iff_getElem.mpr
    intro i hi
    rw [hget i (by omega),hget (i+1) hi]
    apply hcomplete
    rw [color_f,color_f]
    by_cases h : i%2=0
    · have h' : (i+1)%2≠0 := by omega
      simp [h,h']
    · have h' : (i+1)%2=0 := by omega
      simp [h,h']
  refine ⟨l,l.head hne,l.getLast hne,?_,?_,hc,
    List.head?_eq_some_head hne,List.getLast?_eq_some_getLast hne,?_⟩
  · exact List.nodup_ofFn.mpr hf
  · intro v
    obtain ⟨i,rfl⟩ := hsurj v
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  · apply hcomplete
    rw [List.getLast_eq_getElem hne,List.head_eq_getElem hne]
    rw [hget (l.length-1) (by omega),hget 0 (by omega)]
    rw [color_f,color_f]
    have ho : (l.length-1)%2≠0 := by omega
    simp [ho]

#print axioms complete_spanning_cycle

end BalancedBipartite
