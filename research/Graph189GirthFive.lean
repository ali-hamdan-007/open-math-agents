import Graph189BipartiteSmall

namespace Graph189GirthFive
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Excluding triangles and four-cycles, expressed by local adjacency. -/
structure SmallCycleFree (G : SimpleGraph V) : Prop where
  no_triangle : ∀ {a b c}, G.Adj a b → G.Adj b c → ¬ G.Adj a c
  unique_middle : ∀ {a b c d}, G.Adj a b → G.Adj a c → G.Adj b d → G.Adj c d →
    a ≠ d → b = c

variable [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem dist_two (hg : SmallCycleFree G) {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hac : a ≠ c) : G.dist a c = 2 := by
  let hp : G.Walk a c := .cons hab (.cons hbc .nil)
  have hle := G.dist_le hp
  have hpos : 0 < G.dist a c := by
    exact Nat.pos_of_ne_zero (fun h => hac ((hp.reachable.dist_eq_zero_iff).mp h))
  have hn : G.dist a c ≠ 1 := fun h => hg.no_triangle hab hbc (dist_eq_one_iff_adj.mp h)
  have hle₂ : G.dist a c ≤ 2 := by simpa [hp] using hle
  omega

private theorem branch_subset_even (hg : SmallCycleFree G) {v w : V} (hvw : G.Adj v w) :
    (G.neighborFinset w).erase v ⊆
      (Finset.univ.filter (fun x => Even (G.dist v x))).erase v := by
  intro x hx
  obtain ⟨hxv,hx⟩ := Finset.mem_erase.mp hx
  have he := dist_two hg hvw ((G.mem_neighborFinset w x).mp hx) hxv.symm
  exact Finset.mem_erase.mpr ⟨hxv,Finset.mem_filter.mpr ⟨Finset.mem_univ _, he ▸ (by decide : Even 2)⟩⟩

private theorem degree_one_branch (hg : SmallCycleFree G) {v w : V} (hvw : G.Adj v w) :
    G.degree w ≤ G.distEven v := by
  have hle := Finset.card_le_card (branch_subset_even hg hvw)
  rw [Finset.card_erase_of_mem ((G.mem_neighborFinset w v).mpr hvw.symm),
    Finset.card_erase_of_mem
      (Finset.mem_filter.mpr ⟨Finset.mem_univ v, by simp⟩)] at hle
  change G.degree w - 1 ≤ G.distEven v - 1 at hle
  have hpos : 0 < G.distEven v := Finset.card_pos.mpr
    ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp⟩⟩
  omega

private theorem degree_two_branches (hg : SmallCycleFree G) {v w t : V}
    (hvw : G.Adj v w) (hvt : G.Adj v t) (hwt : w ≠ t) :
    (G.degree w - 1) + (G.degree t - 1) ≤ G.distEven v - 1 := by
  let A := (G.neighborFinset w).erase v
  let B := (G.neighborFinset t).erase v
  have hdis : Disjoint A B := Finset.disjoint_left.mpr (by
    intro d hdA hdB
    obtain ⟨hdv,hdw⟩ := Finset.mem_erase.mp hdA
    have hdt := Finset.mem_of_mem_erase hdB
    exact hwt (hg.unique_middle hvw hvt ((G.mem_neighborFinset w d).mp hdw)
      ((G.mem_neighborFinset t d).mp hdt) hdv.symm))
  have hle := Finset.card_le_card (Finset.union_subset (branch_subset_even hg hvw)
    (branch_subset_even hg hvt))
  change (A ∪ B).card ≤ _ at hle
  rw [Finset.card_union_of_disjoint hdis] at hle
  dsimp [A,B] at hle
  rw [Finset.card_erase_of_mem ((G.mem_neighborFinset w v).mpr hvw.symm),
    Finset.card_erase_of_mem ((G.mem_neighborFinset t v).mpr hvt.symm),
    Finset.card_erase_of_mem
      (Finset.mem_filter.mpr ⟨Finset.mem_univ v, by simp⟩)] at hle
  exact hle

private theorem two_good [Nontrivial V] {z : V} (hz : 3 ≤ G.degree z) :
    ∃ a b, G.Adj z a ∧ G.Adj z b ∧ a ≠ b ∧
      G.secondSmallestDegree ≤ G.degree a ∧ G.secondSmallestDegree ≤ G.degree b := by
  let N := G.neighborFinset z
  have hc : 3 ≤ N.card := hz
  have htwo : 1 < N.card := by omega
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp htwo
  have hc' : 1 < (N.erase a).card := by rw [Finset.card_erase_of_mem ha]; omega
  obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hc'
  have hua : u ≠ a := Finset.ne_of_mem_erase hu
  have hva : v ≠ a := Finset.ne_of_mem_erase hv
  have hmem (x : V) (hx : x ∈ N) : G.Adj z x := (G.mem_neighborFinset z x).mp hx
  have hq := Graph189Bipartite.degree_pair (G := G)
  by_cases hau : G.secondSmallestDegree ≤ G.degree a
  · rcases hq u v huv with hgood | hgood
    · exact ⟨a,u,hmem a ha,hmem u (Finset.mem_of_mem_erase hu),hua.symm,hau,hgood⟩
    · exact ⟨a,v,hmem a ha,hmem v (Finset.mem_of_mem_erase hv),hva.symm,hau,hgood⟩
  · exact ⟨u,v,hmem u (Finset.mem_of_mem_erase hu),hmem v (Finset.mem_of_mem_erase hv),huv,
      (hq u a hua).resolve_right hau,(hq v a hva).resolve_right hau⟩

/-- The exact distance/degree inequality from conjecture 189 forces all degrees
to be at most two when triangles and four-cycles are excluded. -/
theorem degree_le_two [Nontrivial V] (h : G.Connected) (hg : SmallCycleFree G)
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + G.secondSmallestDegree) :
    ∀ z, G.degree z ≤ 2 := by
  have heven (v : V) : G.distEven v ≤ 1 + G.secondSmallestDegree :=
    (Finset.le_max' _ _ (Finset.mem_image.mpr ⟨v,Finset.mem_univ _, rfl⟩)).trans hσ
  have hs : G.secondSmallestDegree ≤ 2 := by
    by_contra! hs
    obtain ⟨z⟩ := h.nonempty
    obtain ⟨w,hzw⟩ := h.preconnected.exists_adj_of_nontrivial z
    obtain ⟨v,hv⟩ : ∃ v, G.secondSmallestDegree ≤ G.degree v :=
      (Graph189Bipartite.degree_pair z w (G.ne_of_adj hzw)).elim
        (fun hz => ⟨z,hz⟩) (fun hw => ⟨w,hw⟩)
    obtain ⟨a,b,ha,hb,hab,hga,hgb⟩ := two_good (G := G) (by omega : 3 ≤ G.degree v)
    have hsum := degree_two_branches hg ha hb hab
    have hv' := heven v
    omega
  intro z
  by_contra! hz
  obtain ⟨a,b,ha,hb,hab,hga,hgb⟩ := two_good (G := G) (by omega : 3 ≤ G.degree z)
  have hasum := degree_one_branch hg ha.symm
  have hEa := heven a
  have hs₂ : G.secondSmallestDegree = 2 := by omega
  have other {v : V} (hv : G.Adj z v) (hvg : G.secondSmallestDegree ≤ G.degree v) :
      ∃ u, G.Adj v u ∧ G.degree u ≤ 1 := by
    have hv₂ : 1 < (G.neighborFinset v).card := by
      change 1 < G.degree v
      omega
    have hne : 0 < ((G.neighborFinset v).erase z).card := by
      rw [Finset.card_erase_of_mem ((G.mem_neighborFinset v z).mpr hv.symm)]
      omega
    obtain ⟨u,hu⟩ := Finset.card_pos.mp hne
    have hvu := (G.mem_neighborFinset v u).mp (Finset.mem_of_mem_erase hu)
    have hsum := degree_two_branches hg hv.symm hvu (Finset.ne_of_mem_erase hu).symm
    have hEv := heven v
    exact ⟨u,hvu,by omega⟩
  obtain ⟨u,hau,hu⟩ := other ha hga
  obtain ⟨v,hbv,hv⟩ := other hb hgb
  have he : u = v := by
    by_contra hne
    rcases Graph189Bipartite.degree_pair (G := G) u v hne with hh | hh <;> omega
  subst v
  exact hab (Finset.card_le_one.mp hu a ((G.mem_neighborFinset u a).mpr hau.symm)
    b ((G.mem_neighborFinset u b).mpr hbv.symm))


/-- A longest path in a connected graph of maximum degree two is spanning. -/
theorem traceable_of_degree_le_two (h : G.Connected) (hd : ∀ x, G.degree x ≤ 2) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let Good (n : ℕ) := ∃ L : List V, L.length = n ∧ L.Nodup ∧ L.IsChain G.Adj
  let n := Nat.findGreatest Good (Fintype.card V)
  obtain ⟨a⟩ := h.nonempty
  have ga : Good 1 := ⟨[a],rfl,by simp,by simp⟩
  have one_le : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨a⟩
  have hn : 1 ≤ n := Nat.le_findGreatest one_le ga
  obtain ⟨L,hLn,hLnodup,hLchain⟩ := Nat.findGreatest_spec one_le ga
  change L.length = n at hLn
  have length_le (M : List V) (hM : M.Nodup) : M.length ≤ Fintype.card V := by
    rw [← M.toFinset_card_of_nodup hM, ← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  have maxLen (M : List V) (hM : M.Nodup) (hc : M.IsChain G.Adj) : M.length ≤ n :=
    Nat.le_findGreatest (length_le M hM) (show Good M.length from ⟨M,rfl,hM,hc⟩)
  have hne : L ≠ [] := by intro he; simp [he] at hLn; omega
  have hcross {u v : V} (p : G.Walk u v) (hu : u ∈ L) (hv : v ∉ L) :
      ∃ x ∈ L, ∃ y ∉ L, G.Adj x y := by
    induction p with
    | nil => exact (hv hu).elim
    | @cons u w v huw p ih =>
      by_cases hw : w ∈ L
      · exact ih hw hv
      · exact ⟨u,hu,w,hw,huw⟩
  have covers (v : V) : v ∈ L := by
    by_contra hv
    obtain ⟨p⟩ := h.preconnected (L.head hne) v
    obtain ⟨x,hx,y,hy,hxy⟩ := hcross p (List.head_mem hne) hv
    obtain ⟨A,B,hAB⟩ := List.mem_iff_append.mp hx
    have hnAB : (A ++ x :: B).Nodup := hAB ▸ hLnodup
    have hcAB : (A ++ x :: B).IsChain G.Adj := hAB ▸ hLchain
    by_cases hA : A = []
    · have he : L = x :: B := by simpa [hA] using hAB
      have hm := maxLen (y :: L) (List.nodup_cons.mpr ⟨hy,hLnodup⟩)
        (hLchain.cons (by simpa [he] using hxy.symm))
      simp only [List.length_cons, hLn] at hm
      omega
    cases B with
    | nil =>
      have he : L.getLast? = some x := by simp [hAB]
      have hm : (L ++ [y]).length ≤ n := maxLen _ (by
        simp [List.nodup_append, hLnodup]
        exact fun b hb heq => hy (heq ▸ hb))
        (hLchain.append (by simp) (by simpa [he] using hxy))
      simp only [List.length_append, List.length_singleton, hLn] at hm
      omega
    | cons b B =>
      let z := A.getLast hA
      have hzA : z ∈ A := List.getLast_mem hA
      obtain ⟨_,hcb,hjoin⟩ := List.isChain_append.mp hcAB
      have hzx : G.Adj z x := hjoin z (by rw [List.getLast?_eq_some_getLast hA]; simp [z]) x (by simp)
      have hxb : G.Adj x b := (List.isChain_cons_cons.mp hcb).1
      have hzb : z ≠ b := (List.nodup_append.mp hnAB).2.2 z hzA b (by simp)
      have hzL : z ∈ L := hAB.symm ▸ List.mem_append_left _ hzA
      have hbL : b ∈ L := hAB.symm ▸ List.mem_append_right _ (by simp)
      have hzy : z ≠ y := fun he => hy (he ▸ hzL)
      have hby : b ≠ y := fun he => hy (he ▸ hbL)
      have hs : ({z,b,y} : Finset V) ⊆ G.neighborFinset x := by
        intro w hw
        rcases (show w = z ∨ w = b ∨ w = y from by simpa using hw) with h₁ | h₂ | h₃
        · subst w; exact (G.mem_neighborFinset x z).mpr hzx.symm
        · subst w; exact (G.mem_neighborFinset x b).mpr hxb
        · subst w; exact (G.mem_neighborFinset x y).mpr hxy
      have hct := Finset.card_le_card hs
      simp [Finset.card_insert_of_notMem, hzb, hzy, hby] at hct
      exact (Nat.not_succ_le_self 2) (hct.trans (hd x))
  have huniv : L.toFinset = Finset.univ := by ext v; simp [covers]
  have hlen : L.length = Fintype.card V := by
    rw [← List.toFinset_card_of_nodup hLnodup, huniv, Finset.card_univ]
  exact Graph189Bipartite.hamiltonian_of_chain L hne hLchain hLnodup hlen

/-- Conjecture 189 holds for every graph with no triangles or four-cycles. -/
theorem hamiltonian [Nontrivial V] (h : G.Connected) (hg : SmallCycleFree G)
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + G.secondSmallestDegree) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian :=
  traceable_of_degree_le_two h (degree_le_two h hg hσ)

#print axioms degree_le_two
#print axioms hamiltonian
end Graph189GirthFive
