import Graph189TraceClosure

namespace Graph189HighMiddleClosure
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G H : SimpleGraph V}
  [DecidableRel G.Adj] [DecidableRel H.Adj]

private theorem degree_gain (hGH : G ≤ H) (x : V) (K : Finset V)
    (hK : ∀ y ∈ K, H.Adj x y ∧ ¬ G.Adj x y) :
    G.degree x + K.card ≤ H.degree x := by
  have hdis : Disjoint (G.neighborFinset x) K :=
    Finset.disjoint_left.mpr fun y hy hk => (hK y hk).2 ((G.mem_neighborFinset x y).mp hy)
  have hsub : G.neighborFinset x ∪ K ⊆ H.neighborFinset x := by
    intro y hy
    apply (H.mem_neighborFinset x y).mpr
    exact (Finset.mem_union.mp hy).elim
      (fun hh => hGH ((G.mem_neighborFinset x y).mp hh)) (fun hk => (hK y hk).1)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis] at hcard
  exact hcard

private theorem degree_mono (hGH : G ≤ H) (x : V) : G.degree x ≤ H.degree x := by
  simpa using degree_gain hGH x ∅ (by simp)

/-- Three high-degree middle vertices force complete path closure, provided
each anchor has two remote nonneighbors seeing at most one high middle vertex. -/
theorem complete_of_high_middle
    (hn : Fintype.card V = 14) (hGH : G ≤ H)
    (sat : ∀ x y, x ≠ y → 14 ≤ H.degree x + H.degree y + 1 → H.Adj x y)
    (z a b : V) (hne : a ≠ b) (haz : a ≠ z) (hbz : b ≠ z)
    (hz : 2 ≤ G.degree z) (ha : 6 ≤ G.degree a) (hb : 6 ≤ G.degree b)
    (good : ∀ x, x ≠ z → 5 ≤ G.degree x)
    (T R : Finset V) (hT : 3 ≤ T.card) (hR : R.card = 6)
    (hTR : Disjoint T R)
    (hTz : z ∉ T) (hTa : a ∉ T) (hTb : b ∉ T)
    (hRz : z ∉ R) (hRa : a ∉ R) (hRb : b ∉ R)
    (high : ∀ x ∈ T, 8 ≤ G.degree x)
    (noAnchor : ∀ r ∈ R, ¬ G.Adj a r ∧ ¬ G.Adj b r)
    (Fa Fb : Finset V) (hFa : Fa ⊆ R) (hFb : Fb ⊆ R)
    (hCa : 2 ≤ Fa.card) (hCb : 2 ≤ Fb.card)
    (hNearA : ∀ r ∈ Fa, (T ∩ G.neighborFinset r).card ≤ 1)
    (hNearB : ∀ r ∈ Fb, (T ∩ G.neighborFinset r).card ≤ 1) :
    H = ⊤ := by
  have base (x : V) (hx : x ≠ z) : 5 ≤ H.degree x := (good x hx).trans (degree_mono hGH x)
  have uni {x : V} (hx : x ≠ z) (hx8 : 8 ≤ H.degree x) (y : V) (hxy : x ≠ y) :
      H.Adj x y := by
    by_cases hy : y = z
    · subst y
      have hsub : (Finset.univ.erase x).erase z ⊆ H.neighborFinset x := by
        intro t ht
        have ht' := Finset.mem_erase.mp ht
        have ht'' := Finset.mem_erase.mp ht'.2
        exact (H.mem_neighborFinset x t).mpr (sat x t ht''.1.symm (by have := base t ht'.1; omega))
      have hd := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hx.symm,Finset.mem_univ _⟩),
        Finset.card_erase_of_mem (Finset.mem_univ x),Finset.card_univ,hn] at hd
      have hzH := hz.trans (degree_mono hGH z)
      change 14-1-1 ≤ H.degree x at hd
      exact sat x z hx (by omega)
    · exact sat x y hxy (by have := base y hy; omega)
  have tUni (x : V) (hx : x ∈ T) (y : V) (hxy : x ≠ y) : H.Adj x y :=
    uni (fun e => hTz (e ▸ hx)) ((high x hx).trans (degree_mono hGH x)) y hxy
  have reached {r : V} (hr : r ∈ R) (hc : (T ∩ G.neighborFinset r).card ≤ 1) :
      7 ≤ H.degree r := by
    let K := T \ G.neighborFinset r
    have hK : 2 ≤ K.card := by
      dsimp [K]
      rw [Finset.card_sdiff,Finset.inter_comm]
      omega
    have hh := degree_gain hGH r K (by
      intro x hx
      obtain ⟨hxT,hxG⟩ := Finset.mem_sdiff.mp hx
      refine ⟨(tUni x hxT r (fun e => Finset.disjoint_left.mp hTR (e ▸ hxT) hr)).symm,?_⟩
      exact fun e => hxG ((G.mem_neighborFinset r x).mpr e))
    have hg := good r (fun e => hRz (e ▸ hr))
    omega
  have anchorUni (u : V) (huz : u ≠ z) (huR : u ∉ R) (huD : 6 ≤ G.degree u)
      (F : Finset V) (hFR : F ⊆ R) (hF : 2 ≤ F.card)
      (hno : ∀ r ∈ R, ¬ G.Adj u r)
      (hcap : ∀ r ∈ F, (T ∩ G.neighborFinset r).card ≤ 1) :
      ∀ y, u ≠ y → H.Adj u y := by
    have hh := degree_gain hGH u F (by
      intro r hr
      have hR' := hFR hr
      have hne : u ≠ r := fun e => huR (e.symm ▸ hR')
      have hrD := reached hR' (hcap r hr)
      have hD := huD.trans (degree_mono hGH u)
      exact ⟨sat u r hne (by omega),hno r hR'⟩)
    exact uni huz (by omega)
  have aUni := anchorUni a haz hRa ha Fa hFa hCa (fun r hr => (noAnchor r hr).1) hNearA
  have bUni := anchorUni b hbz hRb hb Fb hFb hCb (fun r hr => (noAnchor r hr).2) hNearB
  have remoteDeg (r : V) (hr : r ∈ R) : 7 ≤ H.degree r := by
    have hh := degree_gain hGH r ({a,b} : Finset V) (by
      intro x hx
      rcases (show x = a ∨ x = b from by simpa using hx) with e | e
      · subst x
        exact ⟨(aUni r (fun e => hRa (e.symm ▸ hr))).symm,fun he => (noAnchor r hr).1 he.symm⟩
      · subst x
        exact ⟨(bUni r (fun e => hRb (e.symm ▸ hr))).symm,fun he => (noAnchor r hr).2 he.symm⟩)
    rw [Finset.card_pair hne] at hh
    have hg := good r (fun e => hRz (e ▸ hr))
    omega
  have rUni (r : V) (hr : r ∈ R) : ∀ y, r ≠ y → H.Adj r y := by
    have hdis : Disjoint (R.erase r) ({a,b} : Finset V) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      have hx' := Finset.mem_of_mem_erase hx
      rcases (show x = a ∨ x = b from by simpa using hy) with e | e
      · exact hRa (e ▸ hx')
      · exact hRb (e ▸ hx')
    have hsub : (R.erase r) ∪ ({a,b} : Finset V) ⊆ H.neighborFinset r := by
      intro x hx
      apply (H.mem_neighborFinset r x).mpr
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨hxr,hxR⟩ := Finset.mem_erase.mp hx
        exact sat r x hxr.symm (by have := remoteDeg r hr; have := remoteDeg x hxR; omega)
      · rcases (show x = a ∨ x = b from by simpa using hx) with e | e
        · exact e.symm ▸ (aUni r (fun e => hRa (e.symm ▸ hr))).symm
        · exact e.symm ▸ (bUni r (fun e => hRb (e.symm ▸ hr))).symm
    have hsubT : ((R.erase r) ∪ ({a,b} : Finset V)) ∪ T ⊆ H.neighborFinset r := by
      apply Finset.union_subset hsub
      intro x hx
      exact (H.mem_neighborFinset r x).mpr
        ((tUni x hx r (fun e => Finset.disjoint_left.mp hTR (e ▸ hx) hr)).symm)
    have hdisT : Disjoint ((R.erase r) ∪ ({a,b} : Finset V)) T := by
      apply Finset.disjoint_left.mpr
      intro x hx ht
      rcases Finset.mem_union.mp hx with hr' | he
      · exact Finset.disjoint_left.mp hTR ht (Finset.mem_of_mem_erase hr')
      · rcases (show x = a ∨ x = b from by simpa using he) with e | e
        · exact hTa (e ▸ ht)
        · exact hTb (e ▸ ht)
    have hl := Finset.card_le_card hsubT
    rw [Finset.card_union_of_disjoint hdisT,Finset.card_union_of_disjoint hdis,
      Finset.card_erase_of_mem hr,hR,Finset.card_pair hne] at hl
    change 6-1+2+T.card ≤ H.degree r at hl
    exact uni (fun e => hRz (e ▸ hr)) (by omega)
  have all8 (x : V) : 8 ≤ H.degree x := by
    let U := (R ∪ ({a,b} : Finset V)).erase x
    have hsub : U ⊆ H.neighborFinset x := by
      intro y hy
      obtain ⟨hxy,hy⟩ := Finset.mem_erase.mp hy
      apply (H.mem_neighborFinset x y).mpr
      rcases Finset.mem_union.mp hy with hr | hh
      · exact (rUni y hr x hxy).symm
      · rcases (show y = a ∨ y = b from by simpa using hh) with e | e
        · subst y; exact (aUni x hxy).symm
        · subst y; exact (bUni x hxy).symm
    have hsub' : U ∪ T.erase x ⊆ H.neighborFinset x := by
      apply Finset.union_subset hsub
      intro y hy
      obtain ⟨hne,hy⟩ := Finset.mem_erase.mp hy
      exact (H.mem_neighborFinset x y).mpr (tUni y hy x hne).symm
    have hd : Disjoint R ({a,b} : Finset V) := by
      apply Finset.disjoint_left.mpr
      intro y hy hh
      rcases (show y = a ∨ y = b from by simpa using hh) with e | e
      · exact hRa (e ▸ hy)
      · exact hRb (e ▸ hy)
    have hd' : Disjoint U (T.erase x) := by
      apply Finset.disjoint_left.mpr
      intro y hu ht
      have ht' := Finset.mem_of_mem_erase ht
      rcases Finset.mem_union.mp (Finset.mem_of_mem_erase hu) with hr | hh
      · exact Finset.disjoint_left.mp hTR ht' hr
      · rcases (show y = a ∨ y = b from by simpa using hh) with e | e
        · exact hTa (e ▸ ht')
        · exact hTb (e ▸ ht')
    have erase_bound (Q : Finset V) : Q.card ≤ (Q.erase x).card + 1 := by
      by_cases hx : x ∈ Q
      · rw [Finset.card_erase_of_mem hx]; omega
      · rw [Finset.erase_eq_of_notMem hx]; omega
    have hU : 7 ≤ U.card := by
      have hh := erase_bound (R ∪ ({a,b} : Finset V))
      have he : (R ∪ ({a,b} : Finset V)).card = 8 := by
        rw [Finset.card_union_of_disjoint hd,hR,Finset.card_pair hne]
      rw [he] at hh
      exact by change 7 ≤ ((R ∪ ({a,b} : Finset V)).erase x).card; omega
    have hTx : 2 ≤ (T.erase x).card := by
      have := erase_bound T
      omega
    have hh := Finset.card_le_card hsub'
    rw [Finset.card_union_of_disjoint hd'] at hh
    change U.card + (T.erase x).card ≤ H.degree x at hh
    omega
  apply le_antisymm le_top
  intro x y hxy
  exact sat x y hxy.ne (by have := all8 x; have := all8 y; omega)

private theorem top_traceable (v : V) :
    ∃ a b : V, ∃ p : (⊤ : SimpleGraph V).Walk a b, p.IsHamiltonian := by
  let L := (Finset.univ : Finset V).toList
  have hnd : L.Nodup := Finset.nodup_toList _
  have hall (x : V) : x ∈ L := by simp [L]
  have hc : L.IsChain (⊤ : SimpleGraph V).Adj := by
    exact (List.nodup_iff_pairwise_ne.mp hnd).isChain
  have hn : L ≠ [] := List.ne_nil_of_mem (hall v)
  let p := SimpleGraph.Walk.ofSupport L hn hc
  have hp : p.support = L := SimpleGraph.Walk.support_ofSupport hn hc
  exact ⟨_,_,p,(SimpleGraph.Walk.IsPath.mk' (hp.symm ▸ hnd)).isHamiltonian_of_mem
    (fun x => hp.symm ▸ hall x)⟩

/-- A graph with the stated middle and remote bounds has a Hamiltonian path. -/
theorem traceable_of_high_middle (hn : Fintype.card V = 14)
    (z a b : V) (hne : a ≠ b) (haz : a ≠ z) (hbz : b ≠ z)
    (hz : 2 ≤ G.degree z) (ha : 6 ≤ G.degree a) (hb : 6 ≤ G.degree b)
    (good : ∀ x, x ≠ z → 5 ≤ G.degree x)
    (T R : Finset V) (hT : 3 ≤ T.card) (hR : R.card = 6)
    (hTR : Disjoint T R)
    (hTz : z ∉ T) (hTa : a ∉ T) (hTb : b ∉ T)
    (hRz : z ∉ R) (hRa : a ∉ R) (hRb : b ∉ R)
    (high : ∀ x ∈ T, 8 ≤ G.degree x)
    (noAnchor : ∀ r ∈ R, ¬ G.Adj a r ∧ ¬ G.Adj b r)
    (Fa Fb : Finset V) (hFa : Fa ⊆ R) (hFb : Fb ⊆ R)
    (hCa : 2 ≤ Fa.card) (hCb : 2 ≤ Fb.card)
    (hNearA : ∀ r ∈ Fa, (T ∩ G.neighborFinset r).card ≤ 1)
    (hNearB : ∀ r ∈ Fb, (T ∩ G.neighborFinset r).card ≤ 1) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let P (K : SimpleGraph V) := ∃ a b : V, ∃ p : K.Walk a b, p.IsHamiltonian
  change P G
  by_contra hno
  obtain ⟨K,hGK,hmax⟩ := Finite.exists_le_maximal (p := fun K : SimpleGraph V => ¬ P K) hno
  have hsat (x y : V) (hxy : x ≠ y) (hsum : 14 ≤ K.degree x + K.degree y + 1) :
      K.Adj x y := by
    by_contra hna
    have hbad : ¬ P (K ⊔ SimpleGraph.edge x y) := fun hh =>
      hmax.prop (Graph189.traceable_of_sup_edge hxy hna (hn.symm ▸ hsum) hh)
    have hel := hmax.le_of_ge hbad le_sup_left
    exact hna (hel (Or.inr ((SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,hxy⟩)))
  have htop := complete_of_high_middle hn hGK hsat z a b hne haz hbz hz ha hb good T R hT hR
    hTR hTz hTa hTb hRz hRa hRb high noAnchor Fa Fb hFa hFb hCa hCb hNearA hNearB
  exact hmax.prop (htop.symm ▸ top_traceable z)

#print axioms complete_of_high_middle
#print axioms traceable_of_high_middle
end Graph189HighMiddleClosure
