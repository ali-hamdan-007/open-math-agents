import OMAReductions.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1_H2_R1

namespace Graph199BipartiteOrder

open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1
open OMA.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1_H2_R1

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem bool_eq_of_ne_same {a b c : Bool} (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- Common neighbors of the endpoints of a two-edge path leave a bound
on their private neighborhoods, by adjoining those leaves to the path. -/
theorem private_neighbors_le_of_common {col : V → Bool}
    (hcol : ∀ ⦃x y⦄, G.Adj x y → col x ≠ col y)
    {x y z : V} (hxy : x ≠ y) (hxz : G.Adj x z) (hyz : G.Adj y z) :
    ((G.neighborFinset x) \ G.neighborFinset y).card +
      ((G.neighborFinset y) \ G.neighborFinset x).card + 3 ≤ largestInducedTreeSize G := by
  classical
  have hxyCol : col x = col y := bool_eq_of_ne_same (hcol hxz) (hcol hyz)
  have hno : ¬ G.Adj x y := fun h => hcol h hxyCol
  have hsingleton : (G.induce ({z} : Set V)).Connected := by
    let : Nonempty ↥({z} : Set V) := ⟨⟨z, by simp⟩⟩
    let : Subsingleton ↥({z} : Set V) := ⟨fun a b => Subtype.ext
      ((Set.mem_singleton_iff.mp a.property).trans (Set.mem_singleton_iff.mp b.property).symm)⟩
    exact Connected.of_subsingleton
  obtain ⟨B,hBcard,hxB,hyB,hBinside,hB⟩ := connector_tree_of_common_component x y {z}
    hxy hno hsingleton ⟨z,by simp,hxz⟩ ⟨z,by simp,hyz⟩
  let S := G.neighborFinset x \ G.neighborFinset y
  let T := G.neighborFinset y \ G.neighborFinset x
  have hadjS {v : V} (h : v ∈ S) : G.Adj v x :=
    ((G.mem_neighborFinset x v).mp (mem_sdiff.mp h).1).symm
  have hadjT {v : V} (h : v ∈ T) : G.Adj v y :=
    ((G.mem_neighborFinset y v).mp (mem_sdiff.mp h).1).symm
  have hnS {v : V} (h : v ∈ S) : ¬ G.Adj v y :=
    fun he => (mem_sdiff.mp h).2 ((G.mem_neighborFinset y v).mpr he.symm)
  have hnT {v : V} (h : v ∈ T) : ¬ G.Adj v x :=
    fun he => (mem_sdiff.mp h).2 ((G.mem_neighborFinset x v).mpr he.symm)
  have hsDis : Disjoint S B := by
    refine Finset.disjoint_left.mpr ?_
    intro v hv hBv
    rcases hBinside v hBv with rfl | rfl | he
    · exact (hadjS hv).ne rfl
    · exact hno (hadjS hv).symm
    · have he' := Set.mem_singleton_iff.mp he
      exact hnS hv (he'.symm ▸ hyz.symm)
  have htDis : Disjoint T B := by
    refine Finset.disjoint_left.mpr ?_
    intro v hv hBv
    rcases hBinside v hBv with rfl | rfl | he
    · exact hno (hadjT hv)
    · exact (hadjT hv).ne rfl
    · have he' := Set.mem_singleton_iff.mp he
      exact hnT hv (he'.symm ▸ hxz.symm)
  have hsInd : G.IsIndepSet (S : Set V) := by
    intro u hu v hv _ huv
    exact hcol huv (bool_eq_of_ne_same (hcol (hadjS hu)) (hcol (hadjS hv)))
  have htInd : G.IsIndepSet (T : Set V) := by
    intro u hu v hv _ huv
    exact hcol huv (bool_eq_of_ne_same (hcol (hadjT hu)) (hcol (hadjT hv)))
  have hST : ∀ u ∈ S, ∀ v ∈ T, u ≠ v ∧ ¬ G.Adj u v := by
    intro u hu v hv
    refine ⟨fun e => hnT hv (e ▸ hadjS hu), fun he => hcol he ?_⟩
    have hx := hcol (hadjS hu)
    rw [hxyCol] at hx
    exact bool_eq_of_ne_same hx (hcol (hadjT hv))
  have hsu : ∀ v ∈ S, ∀ w ∈ B, G.Adj v w → w = x := by
    intro v hv w hw he
    rcases hBinside _ hw with rfl | rfl | he'
    · rfl
    · exact (hnS hv he).elim
    · have hc := bool_eq_of_ne_same (hcol (hadjS hv)) (hcol hxz.symm)
      exact (hcol he ((Set.mem_singleton_iff.mp he').symm ▸ hc)).elim
  have htv : ∀ v ∈ T, ∀ w ∈ B, G.Adj v w → w = y := by
    intro v hv w hw he
    rcases hBinside _ hw with rfl | rfl | he'
    · exact (hnT hv he).elim
    · rfl
    · have hc := bool_eq_of_ne_same (hcol (hadjT hv)) (hcol hyz.symm)
      exact (hcol he ((Set.mem_singleton_iff.mp he').symm ▸ hc)).elim
  have htree := leaf_sets_on_induced_tree B S T x y hB hxB hyB hsDis htDis hsInd htInd hST
    (fun _ h => hadjS h) (fun _ h => hadjT h) hsu htv
  change S.card + T.card + 3 ≤ largestInducedTreeSize G
  omega

/-- In a bipartite graph with tree order at most k+2 and degree at least k,
two length-two connections sharing a vertex can be shortened to one. -/
theorem common_neighbors_trans {col : V → Bool}
    (hcol : ∀ ⦃x y⦄, G.Adj x y → col x ≠ col y) {k : ℕ}
    (hmin : ∀ x, k ≤ G.degree x) (ht : largestInducedTreeSize G ≤ k+2) :
    ∀ ⦃x y z : V⦄,
      (x = y ∨ (G.neighborFinset x ∩ G.neighborFinset y).Nonempty) →
      (y = z ∨ (G.neighborFinset y ∩ G.neighborFinset z).Nonempty) →
      (x = z ∨ (G.neighborFinset x ∩ G.neighborFinset z).Nonempty) := by
  intro x y z hxy hyz
  rcases hxy with rfl | hxy
  · exact hyz
  rcases hyz with rfl | hyz
  · exact Or.inr hxy
  by_cases hxe : x = y
  · subst x
    exact Or.inr hyz
  by_cases hze : y = z
  · subst z
    exact Or.inr hxy
  obtain ⟨u,hu⟩ := hxy
  obtain ⟨v,hv⟩ := hyz
  have Hxy := private_neighbors_le_of_common hcol hxe
    ((G.mem_neighborFinset x u).mp (mem_inter.mp hu).1)
    ((G.mem_neighborFinset y u).mp (mem_inter.mp hu).2)
  have Hyz := private_neighbors_le_of_common hcol hze
    ((G.mem_neighborFinset y v).mp (mem_inter.mp hv).1)
    ((G.mem_neighborFinset z v).mp (mem_inter.mp hv).2)
  have ha := card_sdiff_add_card_inter (G.neighborFinset x) (G.neighborFinset y)
  have hb := card_sdiff_add_card_inter (G.neighborFinset y) (G.neighborFinset x)
  have hc := card_sdiff_add_card_inter (G.neighborFinset y) (G.neighborFinset z)
  have hd := card_sdiff_add_card_inter (G.neighborFinset z) (G.neighborFinset y)
  rw [inter_comm (G.neighborFinset y) (G.neighborFinset x)] at hb
  rw [inter_comm (G.neighborFinset z) (G.neighborFinset y)] at hd
  rw [G.card_neighborFinset_eq_degree] at ha hb hc hd
  have hx := hmin x
  have hz := hmin z
  have hsum : (G.neighborFinset y).card <
      (G.neighborFinset x ∩ G.neighborFinset y).card +
      (G.neighborFinset y ∩ G.neighborFinset z).card := by
    rw [G.card_neighborFinset_eq_degree]
    omega
  obtain ⟨w,hw⟩ := inter_nonempty_of_card_lt_card_add_card inter_subset_right inter_subset_left hsum
  obtain ⟨hw₁,hw₂⟩ := mem_inter.mp hw
  exact Or.inr ⟨w,mem_inter.mpr ⟨(mem_inter.mp hw₁).1,(mem_inter.mp hw₂).2⟩⟩

/-- In the same bipartite setting, every distinct same-color pair has a
common neighbor. -/
theorem same_color_common_neighbors {col : V → Bool}
    (hcol : ∀ ⦃x y⦄, G.Adj x y → col x ≠ col y)
    (hG : G.Connected) {k : ℕ} (hmin : ∀ x, k ≤ G.degree x)
    (ht : largestInducedTreeSize G ≤ k+2) {x y : V} (hxy : x ≠ y) (hxyCol : col x = col y) :
    (G.neighborFinset x ∩ G.neighborFinset y).Nonempty := by
  let R (a b : V) := a = b ∨ (G.neighborFinset a ∩ G.neighborFinset b).Nonempty
  have colR {a b : V} (h : R a b) : col a = col b := by
    rcases h with rfl | ⟨v,hv⟩
    · rfl
    · exact bool_eq_of_ne_same (hcol ((G.mem_neighborFinset a v).mp (mem_inter.mp hv).1))
        (hcol ((G.mem_neighborFinset b v).mp (mem_inter.mp hv).2))
  have whe {a b : V} (p : G.Walk a b) : R a b ∨ ∃ c, G.Adj a c ∧ R c b := by
    induction p with
    | nil => exact Or.inl (Or.inl rfl)
    | @cons a c b hac p ih =>
      rcases ih with hcb | ⟨d,hcd,hdb⟩
      · exact Or.inr ⟨c,hac,hcb⟩
      · have had : R a d := Or.inr ⟨c,mem_inter.mpr
          ⟨(G.mem_neighborFinset a c).mpr hac,(G.mem_neighborFinset d c).mpr hcd.symm⟩⟩
        exact Or.inl (common_neighbors_trans hcol hmin ht had hdb)
  obtain ⟨p⟩ := hG.preconnected x y
  rcases whe p with h | ⟨v,hxv,hvy⟩
  · exact h.resolve_left hxy
  · exact (hcol hxv (hxyCol.trans (colR hvy).symm)).elim

theorem vertexConnectivity_le_degree (v : V) :
    vertexConnectivity G ≤ G.degree v := by
  classical
  unfold vertexConnectivity
  split_ifs
  · omega
  apply csInf_le'
  refine ⟨G.neighborFinset v,G.card_neighborFinset_eq_degree v,?_⟩
  by_cases hall : ∀ u, u ≠ v → G.Adj v u
  · right
    have he : G.neighborFinset v = univ.erase v := by
      ext u
      constructor
      · intro hu
        exact mem_erase.mpr ⟨((G.mem_neighborFinset v u).mp hu).ne.symm,mem_univ u⟩
      · intro hu
        exact (G.mem_neighborFinset v u).mpr (hall u (mem_erase.mp hu).1)
    rw [he,card_erase_of_mem (mem_univ v),card_univ]
  · left
    push Not at hall
    obtain ⟨u,huv,hu⟩ := hall
    intro hG
    let S := ((G.neighborFinset v : Finset V) : Set V)ᶜ
    let a : S := ⟨v, by simp [S]⟩
    let b : S := ⟨u, fun h => hu ((G.mem_neighborFinset v u).mp h)⟩
    have hne : a ≠ b := fun h => huv (congrArg Subtype.val h).symm
    let : Nontrivial S := ⟨⟨a,b,hne⟩⟩
    obtain ⟨c,hc⟩ := hG.preconnected.exists_adj_of_nontrivial a
    exact c.property ((G.mem_neighborFinset v c).mpr (induce_adj.mp hc))

private theorem degree_le_tree_order {col : V → Bool}
    (hcol : ∀ ⦃x y⦄, G.Adj x y → col x ≠ col y) (v : V) :
    G.degree v + 1 ≤ largestInducedTreeSize G := by
  have h := star_bound v (G.neighborFinset v) (by
    intro x hx y hy _ hxy
    have hvx := (G.mem_neighborFinset v x).mp hx
    have hvy := (G.mem_neighborFinset v y).mp hy
    exact hcol hxy (bool_eq_of_ne_same (hcol hvx.symm) (hcol hvy.symm)))
    (fun w hw => (G.mem_neighborFinset v w).mp hw)
  rwa [G.card_neighborFinset_eq_degree] at h

private theorem common_degree_count {col : V → Bool}
    (hcol : ∀ ⦃x y⦄, G.Adj x y → col x ≠ col y)
    (hG : G.Connected) {k : ℕ} (hmin : ∀ x, k ≤ G.degree x)
    (ht : largestInducedTreeSize G ≤ k+2) {x y : V} (hxy : x ≠ y) (hxyCol : col x = col y) :
    G.degree x + G.degree y + 1 ≤ k + 2*(G.neighborFinset x ∩ G.neighborFinset y).card := by
  obtain ⟨z,hz⟩ := same_color_common_neighbors hcol hG hmin ht hxy hxyCol
  have h := private_neighbors_le_of_common hcol hxy
    ((G.mem_neighborFinset x z).mp (mem_inter.mp hz).1)
    ((G.mem_neighborFinset y z).mp (mem_inter.mp hz).2)
  have ha := card_sdiff_add_card_inter (G.neighborFinset x) (G.neighborFinset y)
  have hb := card_sdiff_add_card_inter (G.neighborFinset y) (G.neighborFinset x)
  rw [inter_comm (G.neighborFinset y) (G.neighborFinset x)] at hb
  rw [G.card_neighborFinset_eq_degree] at ha hb
  omega

private theorem neighborhood_incidence_count {k : ℕ}
    (hmax : ∀ x, G.degree x ≤ k+1) {X : Finset V} {v : V} :
    (∑ x ∈ X.erase v, (G.neighborFinset v ∩ G.neighborFinset x).card) ≤
      G.degree v * k := by
  classical
  let N := G.neighborFinset v
  have hn : N.card = G.degree v := G.card_neighborFinset_eq_degree v
  have hcol (w : V) (hw : w ∈ N) :
      (((X.erase v).filter fun x => G.Adj x w).card) ≤ k := by
    have hsub : (X.erase v).filter (fun x => G.Adj x w) ⊆ (G.neighborFinset w).erase v := by
      intro a ha
      obtain ⟨ha',haw⟩ := mem_filter.mp ha
      exact mem_erase.mpr ⟨(mem_erase.mp ha').1,(G.mem_neighborFinset w a).mpr haw.symm⟩
    have hcard := card_le_card hsub
    have he := card_erase_add_one ((G.mem_neighborFinset w v).mpr
      ((G.mem_neighborFinset v w).mp hw).symm)
    rw [G.card_neighborFinset_eq_degree] at he
    have hd := hmax w
    omega
  change (∑ x ∈ X.erase v, (N ∩ G.neighborFinset x).card) ≤ _
  calc
    (∑ x ∈ X.erase v, (N ∩ G.neighborFinset x).card)
        = ∑ x ∈ X.erase v, ∑ w ∈ N, if G.Adj x w then (1 : ℕ) else 0 := by
      apply sum_congr rfl
      intro x _
      rw [sum_boole]
      congr 1
      ext w
      simp [G.mem_neighborFinset]
    _ = ∑ w ∈ N, ∑ x ∈ X.erase v, if G.Adj x w then (1 : ℕ) else 0 := sum_comm
    _ = ∑ w ∈ N, ((X.erase v).filter fun x => G.Adj x w).card := by simp [sum_boole]
    _ ≤ ∑ w ∈ N, k := sum_le_sum hcol
    _ = G.degree v * k := by simp [hn]

/-- Every side of a bipartition has at most twice the vertex connectivity
minus one under the induced-tree bound of Graph 199. -/
theorem bipartition_size_le {col : V → Bool}
    (hcol : ∀ ⦃x y⦄, G.Adj x y → col x ≠ col y)
    (hG : G.Connected) (hk : 3 ≤ vertexConnectivity G)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) (c : Bool) :
    (univ.filter (fun v => col v = c)).card ≤ 2 * vertexConnectivity G - 1 := by
  classical
  let k := vertexConnectivity G
  let X := univ.filter (fun v => col v = c)
  have hmin (v : V) : k ≤ G.degree v := vertexConnectivity_le_degree v
  have ht' : largestInducedTreeSize G ≤ k+2 := by
    change largestInducedTreeSize G - 2 ≤ k at ht
    omega
  have hmax (v : V) : G.degree v ≤ k+1 := by
    have h := degree_le_tree_order hcol v
    omega
  change 3 ≤ k at hk
  change X.card ≤ 2*k-1
  by_contra! hbad
  have pack (v : V) (hv : v ∈ X) (j : ℕ)
      (h : ∀ x ∈ X.erase v, j ≤ 2*(G.neighborFinset v ∩ G.neighborFinset x).card) :
      (2*k-1)*j ≤ 2*(G.degree v*k) := by
    have hbig : 2*k-1 ≤ (X.erase v).card := by
      have hcard := card_erase_add_one hv
      omega
    have hupper := neighborhood_incidence_count (X := X) (v := v) hmax
    calc
      (2*k-1)*j ≤ (X.erase v).card*j := Nat.mul_le_mul_right j hbig
      _ = ∑ x ∈ X.erase v, j := by simp
      _ ≤ ∑ x ∈ X.erase v, 2*(G.neighborFinset v ∩ G.neighborFinset x).card := sum_le_sum h
      _ = _ := by rw [mul_sum]
      _ ≤ 2*(G.degree v*k) := Nat.mul_le_mul_left 2 hupper
  have same (x v : V) (hx : x ∈ X) (hv : v ∈ X) : col v = col x :=
    (mem_filter.mp hv).2.trans (mem_filter.mp hx).2.symm
  by_cases hsmall : ∃ v ∈ X, G.degree v = k
  · obtain ⟨v,hv,hdeg⟩ := hsmall
    have h := pack v hv (k+1) (by
      intro x hx
      obtain ⟨hne, hx'⟩ := mem_erase.mp hx
      have hcount := common_degree_count hcol hG hmin ht' hne.symm (same x v hx' hv)
      have hd := hmin x
      omega)
    rw [hdeg] at h
    have hs : 2*k-1 + 1 = 2*k := by omega
    have h' : 2*k*(k+1) ≤ 2*(k*k)+(k+1) := by
      rw [← hs, Nat.add_mul]
      omega
    nlinarith
  · obtain ⟨v,hv⟩ := card_pos.mp (show 0 < X.card by omega)
    have exactDeg (x : V) (hx : x ∈ X) : G.degree x = k+1 := by
      have lo := hmin x
      have hi := hmax x
      have hne : G.degree x ≠ k := fun e => hsmall ⟨x,hx,e⟩
      omega
    have h := pack v hv (k+3) (by
      intro x hx
      obtain ⟨hne,hx'⟩ := mem_erase.mp hx
      have hcount := common_degree_count hcol hG hmin ht' hne.symm (same x v hx' hv)
      rw [exactDeg v hv, exactDeg x hx'] at hcount
      omega)
    rw [exactDeg v hv] at h
    have hs : 2*k-1 + 1 = 2*k := by omega
    have h' : 2*k*(k+3) ≤ 2*((k+1)*k)+(k+3) := by
      rw [← hs, Nat.add_mul]
      omega
    nlinarith

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The separator premise of the remaining Graph 199 child gives part
sizes differing by at most one. -/
theorem bipartition_balance_of_separator {col : V → Bool}
    (hcol : ∀ ⦃x y⦄, G.Adj x y → col x ≠ col y)
    (hsep : ∀ U : Finset V,
      Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent ≤ U.card + 1)
    (c : Bool) :
    (univ.filter (fun v => col v = c)).card ≤
      (univ.filter (fun v => col v = !c)).card + 1 := by
  classical
  let U := univ.filter (fun v => col v = !c)
  let W := univ.filter (fun v => col v = c)
  let T := (U : Set V)ᶜ
  let H := G.induce T
  have hT : T = (W : Set V) := by
    ext v
    simp only [T,U,W,Set.mem_compl_iff,mem_coe,mem_filter,mem_univ,true_and]
    cases c <;> cases col v <;> decide
  have hedge : H = ⊥ := by
    ext x y
    change G.Adj (x : V) (y : V) ↔ False
    refine ⟨fun h => ?_,False.elim⟩
    have hx : (x : V) ∈ W := by
      change (x : V) ∈ (W : Set V)
      rw [← hT]
      exact x.property
    have hy : (y : V) ∈ W := by
      change (y : V) ∈ (W : Set V)
      rw [← hT]
      exact y.property
    exact hcol h ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm)
  have hinj : Function.Injective H.connectedComponentMk := by
    intro x y he
    have hr := ConnectedComponent.exact he
    rw [hedge] at hr
    exact reachable_bot.mp hr
  have hsurj : Function.Surjective H.connectedComponentMk := by
    intro p
    induction p using ConnectedComponent.ind with
    | h x => exact ⟨x,rfl⟩
  let equiv : T ≃ H.ConnectedComponent := Equiv.ofBijective H.connectedComponentMk ⟨hinj,hsurj⟩
  have hcard : Nat.card H.ConnectedComponent = W.card := by
    rw [← Nat.card_congr equiv, hT]
    change Nat.card ↥W = W.card
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  change W.card ≤ U.card + 1
  rw [← hcard]
  exact hsep U

end Graph199BipartiteOrder

#print axioms Graph199BipartiteOrder.private_neighbors_le_of_common
#print axioms Graph199BipartiteOrder.common_neighbors_trans

#print axioms Graph199BipartiteOrder.bipartition_size_le
#print axioms Graph199BipartiteOrder.same_color_common_neighbors

#print axioms Graph199BipartiteOrder.bipartition_balance_of_separator
