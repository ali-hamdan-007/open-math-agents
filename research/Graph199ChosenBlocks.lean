import Graph199OrderedConnector

namespace Graph199
open SimpleGraph Finset
variable {V I : Type*} {G : SimpleGraph V}

/-- On a chordless sequence of separator vertices, choose one bridging component
for each pair which is not an edge. Distinct bridges are separated, and the only
separator vertices with neighbors in a bridge are its two incident centers. -/
theorem chosen_bridging_blocks {d : ℕ} (c : Fin (d+1) ↪ V) (C : I → Set V)
    (R : Fin (d+1) → Finset I)
    (touch : ∀ i k, k ∈ R i ↔ ∃ x ∈ C k, G.Adj (c i) x)
    (outside : ∀ i k, c i ∉ C k)
    (separate : ∀ i j, i ≠ j → ∀ x ∈ C i, ∀ y ∈ C j, x ≠ y ∧ ¬ G.Adj x y)
    (conn : ∀ k, (G.induce (C k)).Connected)
    (consec : ∀ j : Fin d, G.Adj (c j.castSucc) (c j.succ) ∨
      ∃ k, k ∈ R j.castSucc ∧ k ∈ R j.succ)
    (near : ∀ i j k, k ∈ R i → k ∈ R j →
      i.val ≤ j.val + 1 ∧ j.val ≤ i.val + 1) :
    ∃ B : Fin d → Set V,
      (∀ i j, c i ∉ B j) ∧
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ i j, i ≠ j → ∀ x ∈ B i, ∀ y ∈ B j, ¬ G.Adj x y) ∧
      (∀ i j, ∀ x ∈ B j, G.Adj (c i) x → i.val = j.val ∨ i.val = j.val+1) ∧
      (∀ j : Fin d, G.Adj (c j.castSucc) (c j.succ) ∨
        ((G.induce (B j)).Connected ∧ (∃ x ∈ B j, G.Adj (c j.castSucc) x) ∧
         (∃ x ∈ B j, G.Adj (c j.succ) x))) ∧
      (∀ j x, x ∈ B j → ∃ k, x ∈ C k ∧ k ∈ R j.castSucc ∧ k ∈ R j.succ) := by
  classical
  have hex (j : Fin d) : ∃ S : Set V,
      (S = ∅ ∧ G.Adj (c j.castSucc) (c j.succ)) ∨
        ∃ k, S = C k ∧ k ∈ R j.castSucc ∧ k ∈ R j.succ := by
    rcases consec j with e | ⟨k,h1,h2⟩
    · exact ⟨∅,Or.inl ⟨rfl,e⟩⟩
    · exact ⟨C k,Or.inr ⟨k,rfl,h1,h2⟩⟩
  choose B hB using hex
  have spec j x (hx : x ∈ B j) : ∃ k, x ∈ C k ∧ k ∈ R j.castSucc ∧ k ∈ R j.succ := by
    rcases hB j with ⟨h,_⟩ | ⟨k,h,h1,h2⟩
    · simp [h] at hx
    · exact ⟨k,h ▸ hx,h1,h2⟩
  have apart {i j : Fin d} (hne : i ≠ j) {x y : V} (hx : x ∈ B i) (hy : y ∈ B j) :
      x ≠ y ∧ ¬ G.Adj x y := by
    obtain ⟨k,hx,k1,k2⟩ := spec _ _ hx
    obtain ⟨l,hy,l1,l2⟩ := spec _ _ hy
    apply separate k l _ x hx y hy
    rintro rfl
    have h := near _ _ k k1 l2
    have h' := near _ _ k l1 k2
    simp only [Fin.val_castSucc,Fin.val_succ] at h h'
    exact hne (Fin.ext (by omega))
  refine ⟨B,?_,?_,?_,?_,?_,spec⟩
  · intro i j hx
    obtain ⟨k,hk,_⟩ := spec _ _ hx
    exact outside _ _ hk
  · intro i j hij
    exact Set.disjoint_left.mpr (fun _ hx hy => (apart hij hx hy).1 rfl)
  · intro i j hij x hx y hy
    exact (apart hij hx hy).2
  · intro i j x hx hadj
    obtain ⟨k,hk,h1,h2⟩ := spec _ _ hx
    have h' := (touch i k).mpr ⟨x,hk,hadj⟩
    have c1 := near _ _ _ h' h1
    have c2 := near _ _ _ h' h2
    simp only [Fin.val_castSucc,Fin.val_succ] at c1 c2
    omega
  · intro j
    rcases hB j with ⟨_,e⟩ | ⟨k,e,h1,h2⟩
    · exact Or.inl e
    · rw [e]
      exact Or.inr ⟨conn k,(touch _ k).mp h1,(touch _ k).mp h2⟩

#print axioms chosen_bridging_blocks
end Graph199
