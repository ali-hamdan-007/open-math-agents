import Graph189SmallCertificate

namespace Graph189Bipartite
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V}

omit [Nontrivial V] in
/-- A full-length chain of distinct vertices is a Hamiltonian path. -/
theorem hamiltonian_of_chain (L : List V) (hn : L ≠ []) (hc : L.IsChain G.Adj)
    (hd : L.Nodup) (hlen : L.length = Fintype.card V) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  let p := Walk.ofSupport L hn hc
  have hs : p.support = L := Walk.support_ofSupport hn hc
  refine ⟨_,_,p,Walk.isHamiltonian_iff_isPath_and_length_eq.mpr ⟨Walk.IsPath.mk' ?_,?_⟩⟩
  · rwa [hs]
  · have he := p.length_support
    rw [hs, hlen] at he
    omega

/-- Finite certification of the equal parts of size three, with the degree
hypotheses derived from the original conjecture. -/
theorem hamiltonian_balanced_three [DecidableRel G.Adj]
    (h : G.Connected) (C : G.Coloring (Fin 2))
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G)
    (h0 : (part C 0).card = 3) (h1 : (part C 1).card = 3) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  let e₀ : Fin 3 ≃ part C 0 := (Fintype.equivFinOfCardEq ((Fintype.card_coe _).trans h0)).symm
  let e₁ : Fin 3 ≃ part C 1 := (Fintype.equivFinOfCardEq ((Fintype.card_coe _).trans h1)).symm
  let l (i : Fin 3) : V := (e₀ i).val
  let r (i : Fin 3) : V := (e₁ i).val
  have hl (i : Fin 3) : l i ∈ part C 0 := (e₀ i).property
  have hr (i : Fin 3) : r i ∈ part C 1 := (e₁ i).property
  have hlinj : Function.Injective l := fun _ _ he => e₀.injective (Subtype.ext he)
  have hrinj : Function.Injective r := fun _ _ he => e₁.injective (Subtype.ext he)
  have hne (i j : Fin 3) : l i ≠ r j := by
    intro he
    have hcl := (mem_part C 0 _).mp (hl i)
    have hcr := (mem_part C 1 _).mp (hr j)
    exact (by decide : (0 : Fin 2) ≠ 1) (hcl.symm.trans (he.symm ▸ hcr))
  let φ : Six → V := Sum.elim l r
  have hφ : Function.Injective φ := by
    intro a b he
    cases a <;> cases b
    · exact congrArg Sum.inl (hlinj he)
    · exact (hne _ _ he).elim
    · exact (hne _ _ he.symm).elim
    · exact congrArg Sum.inr (hrinj he)
  let T (i j : Fin 3) := decide (G.Adj (l i) (r j))
  let opp (v : Six) : Fin 3 → V := v.elim (fun _ => r) (fun _ => l)
  have hT (v : Six) (i : Fin 3) : row3 T v i = true ↔ G.Adj (φ v) (opp v i) := by
    cases v
    · simp [T,row3,φ,opp]
    · simp [T,row3,φ,opp,adj_comm]
  have hsurj (v : Six) (y : V) (hy : G.Adj (φ v) y) : ∃ i, opp v i = y := by
    cases v with
    | inl i =>
      have hy' := neighborFinset_subset_part C (by decide : (0 : Fin 2) ≠ 1)
        (hl i) ((G.mem_neighborFinset _ _).mpr hy)
      obtain ⟨j,hj⟩ := e₁.surjective ⟨y,hy'⟩
      exact ⟨j,congrArg Subtype.val hj⟩
    | inr i =>
      have hy' := neighborFinset_subset_part C (by decide : (1 : Fin 2) ≠ 0)
        (hr i) ((G.mem_neighborFinset _ _).mpr hy)
      obtain ⟨j,hj⟩ := e₀.surjective ⟨y,hy'⟩
      exact ⟨j,congrArg Subtype.val hj⟩
  have hdeg2 : 2 ≤ secondSmallestDegree G := by
    have hcl := (mem_part C 0 _).mp (hl 0)
    have hb := (color_class_bounds h C hσ (l 0)).2
    rw [hcl] at hb
    change (part C 0).card ≤ _ at hb
    rw [h0] at hb
    omega
  have high (v : Six) (hv : secondSmallestDegree G ≤ G.degree (φ v)) : high3 T v := by
    have ht : 1 < (G.neighborFinset (φ v)).card := by
      change 1 < G.degree (φ v)
      omega
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp ht
    have ha' := (G.mem_neighborFinset _ _).mp ha
    have hb' := (G.mem_neighborFinset _ _).mp hb
    obtain ⟨i,hi⟩ := hsurj v a ha'
    obtain ⟨j,hj⟩ := hsurj v b hb'
    refine ⟨i,j,fun e => hab (hi.symm.trans (e ▸ hj)),(hT v i).mpr ?_,(hT v j).mpr ?_⟩
    · rwa [hi]
    · rwa [hj]
  have haccept : accept3 T := by
    constructor
    · intro v
      obtain ⟨y,hy⟩ := h.preconnected.exists_adj_of_nontrivial (φ v)
      obtain ⟨i,hi⟩ := hsurj v y hy
      exact ⟨i,(hT v i).mpr (hi.symm ▸ hy)⟩
    · intro v w hvw
      exact (degree_pair (φ v) (φ w) (fun he => hvw (hφ he))).imp (high v) (high w)
  obtain ⟨a,b,c,x,y,z,hab,hac,hbc,hxy,hxz,hyz,hax,hbx,hby,hcy,hcz⟩ := some_route3 T haccept
  have ha₁ : G.Adj (l a) (r x) := of_decide_eq_true hax
  have ha₂ : G.Adj (r x) (l b) := (of_decide_eq_true hbx : G.Adj (l b) (r x)).symm
  have ha₃ : G.Adj (l b) (r y) := of_decide_eq_true hby
  have ha₄ : G.Adj (r y) (l c) := (of_decide_eq_true hcy : G.Adj (l c) (r y)).symm
  have ha₅ : G.Adj (l c) (r z) := of_decide_eq_true hcz
  refine hamiltonian_of_chain [l a,r x,l b,r y,l c,r z] (by simp) ?_ ?_ ?_
  · simp [ha₁,ha₂,ha₃,ha₄,ha₅]
  · simp [hne, ne_comm, show l a ≠ l b from fun e => hab (hlinj e),
      show l a ≠ l c from fun e => hac (hlinj e), show l b ≠ l c from fun e => hbc (hlinj e),
      show r x ≠ r y from fun e => hxy (hrinj e), show r x ≠ r z from fun e => hxz (hrinj e),
      show r y ≠ r z from fun e => hyz (hrinj e)]
  · simpa [h0,h1] using part_card_sum C


/-- A connected graph on at least three vertices contains a vertex with two distinct neighbors. -/
theorem exists_degree_gt_one [DecidableRel G.Adj] (h : G.Connected)
    (hcard : 2 < Fintype.card V) : ∃ x, 1 < G.degree x := by
  by_contra! hlow
  obtain ⟨a⟩ := h.nonempty
  obtain ⟨b,hab⟩ := h.preconnected.exists_adj_of_nontrivial a
  have next {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) : v = w :=
    Finset.card_le_one.mp (hlow u) v ((G.mem_neighborFinset u v).mpr huv)
      w ((G.mem_neighborFinset u w).mpr huw)
  have stays {u v : V} (p : G.Walk u v) (hu : u = a ∨ u = b) :
      v = a ∨ v = b := by
    induction p with
    | nil => exact hu
    | @cons u w v huw p ih =>
      apply ih
      rcases hu with rfl | rfl
      · exact Or.inr (next huw hab)
      · exact Or.inl (next huw hab.symm)
  have all (v : V) : v = a ∨ v = b := by
    obtain ⟨p⟩ := h.preconnected a v
    exact stays p (Or.inl rfl)
  have huniv : Finset.univ = ({a,b} : Finset V) := by
    ext v
    simp [all v]
  have : Fintype.card V = 2 := by
    rw [← Finset.card_univ, huniv, Finset.card_pair (G.ne_of_adj hab)]
  omega

/-- The balanced four-vertex case, using connectivity to find a vertex adjacent
to both vertices of the opposite part. -/
theorem hamiltonian_balanced_two [DecidableRel G.Adj]
    (h : G.Connected) (C : G.Coloring (Fin 2))
    (h0 : (part C 0).card = 2) (h1 : (part C 1).card = 2) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have hcard : Fintype.card V = 4 := by simpa [h0,h1] using (part_card_sum C).symm
  obtain ⟨u,hu⟩ := exists_degree_gt_one h (by omega)
  let c := C u
  let d := if c = 0 then 1 else (0 : Fin 2)
  have hcd : c ≠ d := by
    dsimp [d]
    split <;> rename_i hc
    · simp [hc]
    · exact hc
  have sizes (t : Fin 2) : (part C t).card = 2 := by fin_cases t <;> assumption
  have huc : u ∈ part C c := (mem_part C c u).mpr rfl
  have hsub : G.neighborFinset u ⊆ part C d := neighborFinset_subset_part C hcd huc
  have heq : G.neighborFinset u = part C d := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [sizes]
    exact hu
  have hdouble (w : V) (hw : w ∈ part C d) : G.Adj u w :=
    (G.mem_neighborFinset u w).mp (heq ▸ hw)
  obtain ⟨q,s,hqs,heven⟩ := Finset.card_eq_two.mp (sizes c)
  have hpair : u = q ∨ u = s := by simpa [heven] using huc
  obtain ⟨v,hvc,hvu⟩ : ∃ v ∈ part C c, v ≠ u := by
    rcases hpair with he | he
    · exact ⟨s, by simp [heven], he.symm ▸ hqs.symm⟩
    · exact ⟨q, by simp [heven], he.symm ▸ hqs⟩
  obtain ⟨x,hvx⟩ := h.preconnected.exists_adj_of_nontrivial v
  have hxd : x ∈ part C d := neighborFinset_subset_part C hcd hvc
    ((G.mem_neighborFinset v x).mpr hvx)
  obtain ⟨q,s,hqs,heven⟩ := Finset.card_eq_two.mp (sizes d)
  have hpair : x = q ∨ x = s := by simpa [heven] using hxd
  obtain ⟨y,hyd,hyx⟩ : ∃ y ∈ part C d, y ≠ x := by
    rcases hpair with he | he
    · exact ⟨s, by simp [heven], he.symm ▸ hqs.symm⟩
    · exact ⟨q, by simp [heven], he.symm ▸ hqs⟩
  have hsep {a b : V} (ha : a ∈ part C c) (hb : b ∈ part C d) : a ≠ b := by
    intro he
    subst b
    exact hcd (((mem_part C c a).mp ha).symm.trans ((mem_part C d a).mp hb))
  refine hamiltonian_of_chain [y,u,x,v] (by simp) ?_ ?_ ?_
  · simp [(hdouble y hyd).symm, hdouble x hxd, hvx.symm]
  · simp [(hsep huc hyd).symm, hyx, (hsep hvc hyd).symm, hsep huc hxd,
      hvu.symm, (hsep hvc hxd).symm]
  · simp [hcard]

/-- The two-vertex case is the single edge given by connectivity. -/
theorem hamiltonian_card_two (h : G.Connected) (hcard : Fintype.card V = 2) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨a⟩ := h.nonempty
  obtain ⟨b,hab⟩ := h.preconnected.exists_adj_of_nontrivial a
  exact hamiltonian_of_chain [a,b] (by simp) (by simpa) (by simp [G.ne_of_adj hab])
    (by simp [hcard])

#print axioms hamiltonian_balanced_three
#print axioms hamiltonian_balanced_two
end Graph189Bipartite
