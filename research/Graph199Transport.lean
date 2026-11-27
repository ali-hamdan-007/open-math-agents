import Graph199Reduction

namespace Graph199
open SimpleGraph Finset

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {K : SimpleGraph W}

omit [Fintype W] [DecidableEq V] [DecidableEq W] in
private theorem tree_iso_le (e : G ≃g K) :
    largestInducedTreeSize K ≤ largestInducedTreeSize G := by
  unfold largestInducedTreeSize
  apply csSup_le'
  rintro n ⟨t,rfl,ht⟩
  let s := t.map e.symm.toEquiv.toEmbedding
  have hbij : Set.BijOn e (s : Set V) (t : Set W) := by
    refine ⟨?_,e.injective.injOn,?_⟩
    · intro x hx
      rcases mem_map.mp hx with ⟨y,hy,rfl⟩
      simpa using hy
    · intro y hy
      refine ⟨e.symm y, ?_, by simp⟩
      exact mem_map.mpr ⟨y,hy,rfl⟩
  have hs := (Iso.induce e hbij).isTree_iff.mpr ht
  have hb := card_le_largestInducedTreeSize hs
  unfold largestInducedTreeSize at hb
  simpa [s] using hb

private theorem transfer_cut {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {P : SimpleGraph A} {Q : SimpleGraph B} (f : P ≃g Q) (n : ℕ)
    (hn : ∃ S : Finset A, S.card = n ∧
      (¬ (P.induce ((S : Set A)ᶜ)).Connected ∨ S.card = Fintype.card A - 1)) :
    ∃ T : Finset B, T.card = n ∧
      (¬ (Q.induce ((T : Set B)ᶜ)).Connected ∨ T.card = Fintype.card B - 1) := by
  obtain ⟨S,hS,hCut⟩ := hn
  let T := S.map f.toEquiv.toEmbedding
  have hT : T.card = S.card := card_map _
  refine ⟨T, hT.trans hS, ?_⟩
  rcases hCut with hdis | hconv
  · apply Or.inl
    have hbij : Set.BijOn f ((S : Set A)ᶜ) ((T : Set B)ᶜ) := by
      refine ⟨?_, f.injective.injOn, ?_⟩
      · intro x hx hfx
        obtain ⟨y,hy,hyx⟩ := mem_map.mp hfx
        exact hx (f.injective hyx ▸ hy)
      · intro y hy
        refine ⟨f.symm y, ?_, by simp⟩
        intro h
        apply hy
        exact mem_map.mpr ⟨f.symm y, h, by simp⟩
    exact fun ht => hdis ((Iso.induce f hbij).connected_iff.mpr ht)
  · exact Or.inr (hT.trans (hconv.trans (by rw [Fintype.card_congr f.toEquiv])))

private theorem vertexConnectivity_iso (e : G ≃g K) :
    vertexConnectivity G = vertexConnectivity K := by
  classical
  have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr e.toEquiv
  unfold vertexConnectivity
  rw [hcard]
  split_ifs
  · rfl
  · congr 1
    ext n
    constructor
    · intro hn
      have h : ∃ S : Finset V, S.card = n ∧
          (¬ (G.induce ((S : Set V)ᶜ)).Connected ∨ S.card = Fintype.card V - 1) := by
        simpa only [hcard, Set.mem_ofPred_eq] using hn
      exact transfer_cut e n h
    · intro hn
      simpa only [hcard, Set.mem_ofPred_eq] using transfer_cut e.symm n (by simpa only [Set.mem_ofPred_eq] using hn)

/-- Universe-zero instances of the two remaining steps suffice for all finite vertex types. -/
theorem conjecture199_reduction_small (h1 : TwoComponentStep.{0}) (h2 : HighConnectivityStep.{0})
    {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) (hc : G.Connected)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let e := Fintype.equivFin V
  let K : SimpleGraph (Fin (Fintype.card V)) := G.map e.toEmbedding
  let i : G ≃g K := SimpleGraph.Iso.map e G
  let _ : Nontrivial (Fin (Fintype.card V)) :=
    Fin.nontrivial_iff_two_le.mpr Fintype.one_lt_card
  have hc' := i.connected_iff.mp hc
  have ht' : largestInducedTreeSize K - 2 ≤ vertexConnectivity K := by
    rw [← vertexConnectivity_iso i]
    exact (Nat.sub_le_sub_right (tree_iso_le i) 2).trans ht
  obtain ⟨x,y,p,hp⟩ := conjecture199_reduction_local h1 h2 K hc' ht'
  exact ⟨_,_,p.map i.symm.toHom,hp.map i.symm.toHom i.symm.bijective⟩

#print axioms conjecture199_reduction_small
end Graph199
