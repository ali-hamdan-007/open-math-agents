import Graph199Independent

namespace Graph199

open Finset SimpleGraph

private theorem clique_list {V : Type*} [Fintype V] {G : SimpleGraph V}
    {S : Set V} (hS : S.Nonempty) (hc : G.IsClique S) :
    ∃ L : List V, L ≠ [] ∧ L.Nodup ∧ L.IsChain G.Adj ∧ (∀ x, x ∈ L ↔ x ∈ S) := by
  classical
  let L := S.toFinset.toList
  have hm (x : V) : x ∈ L ↔ x ∈ S := by simp [L]
  have hn : L.Nodup := nodup_toList _
  obtain ⟨x, hx⟩ := hS
  refine ⟨L, List.ne_nil_of_mem ((hm x).mpr hx), hn, List.Pairwise.isChain ?_, hm⟩
  apply List.pairwise_iff_get.mpr
  intro i j hij
  exact hc ((hm _).mp (List.get_mem _ _)) ((hm _).mp (List.get_mem _ _))
    (List.pairwise_iff_get.mp hn i j hij)

private theorem two_chains {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hV : ∃ a b : V, a ≠ b) (hα : G.indepNum ≤ 2) :
    ∃ L R : List V, L ≠ [] ∧ R ≠ [] ∧ (L ++ R).Nodup ∧
      L.IsChain G.Adj ∧ R.IsChain G.Adj ∧ (∀ x, x ∈ L ++ R) := by
  classical
  obtain ⟨a, b, hab⟩ := hV
  by_cases hc : G.Connected
  · obtain ⟨s, t, p, hp⟩ := conjecture199_of_indepNum_le_two hc hα
    cases hL : p.support with
    | nil => exact (p.support_ne_nil hL).elim
    | cons x R =>
      have hm (y : V) : y ∈ x :: R := hL ▸ hp.mem_support y
      have hR : R ≠ [] := by
        intro hr
        have ha : a = x := by simpa [hr] using hm a
        have hb : b = x := by simpa [hr] using hm b
        exact hab (ha.trans hb.symm)
      have hchain : (x :: R).IsChain G.Adj := hL ▸ p.isChain_adj_support
      exact ⟨[x], R, by simp, hR, by simpa [hL] using hp.isPath.support_nodup, by simp, hchain.tail, hm⟩
  · let A : Set V := {x | G.Reachable a x}
    have ha : a ∈ A := Reachable.rfl
    have hB : Aᶜ.Nonempty := by
      by_contra hn
      apply hc
      have hreach (x : V) : G.Reachable a x := by
        by_contra hx
        exact hn ⟨x, hx⟩
      let _ : Nonempty V := ⟨a⟩
      exact ⟨fun x y => (hreach x).symm.trans (hreach y)⟩
    obtain ⟨c, hc⟩ := hB
    have hcross (x y : V) (hx : x ∈ A) (hy : y ∈ Aᶜ) : ¬ G.Adj x y :=
      fun h => hy (hx.trans h.reachable)
    have emptyTriple (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
        (hnxy : ¬ G.Adj x y) (hnxz : ¬ G.Adj x z) (hnyz : ¬ G.Adj y z) : False := by
      have hind : G.IsIndepSet ((↑({x,y,z} : Finset V)) : Set V) := by
        intro i hi j hj hne
        simp only [mem_coe, mem_insert, mem_singleton] at hi hj
        rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
          first | contradiction | exact hnxy | exact hnxz | exact hnyz
                | exact (fun h => hnxy h.symm) | exact (fun h => hnxz h.symm)
                | exact (fun h => hnyz h.symm)
      have hcard := hind.card_le_indepNum
      rw [card_insert_of_notMem (by simp [hxy,hxz]), card_insert_of_notMem (by simp [hyz]),
        card_singleton] at hcard
      omega
    have hclA : G.IsClique A := by
      intro x hx y hy hxy
      by_contra hn
      exact emptyTriple x y c hxy (fun h => hc (h ▸ hx)) (fun h => hc (h ▸ hy))
        hn (hcross x c hx hc) (hcross y c hy hc)
    have hclB : G.IsClique Aᶜ := by
      intro x hx y hy hxy
      by_contra hn
      exact emptyTriple a x y (fun h => hx (h ▸ ha)) (fun h => hy (h ▸ ha)) hxy
        (hcross a x ha hx) (hcross a y ha hy) hn
    obtain ⟨L, hLe, hLn, hLc, hLm⟩ := clique_list ⟨a, ha⟩ hclA
    obtain ⟨R, hRe, hRn, hRc, hRm⟩ := clique_list ⟨c, hc⟩ hclB
    refine ⟨L, R, hLe, hRe, List.nodup_append.mpr ⟨hLn, hRn, ?_⟩, hLc, hRc, ?_⟩
    · rintro x hx y hy rfl
      exact (hRm x).mp hy ((hLm x).mp hx)
    · intro x
      by_cases hx : x ∈ A
      · exact List.mem_append_left _ ((hLm x).mpr hx)
      · exact List.mem_append_right _ ((hRm x).mpr hx)

/-- If two disjoint blocks are joined completely, a nonempty clique block can
be inserted between two spanning chains of a block with independence at most two. -/
theorem block_path {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {S T : Set V} (hS : ∃ a ∈ S, ∃ b ∈ S, a ≠ b) (hT : T.Nonempty)
    (hST : Disjoint S T) (hα : (G.induce S).indepNum ≤ 2) (hclique : G.IsClique T)
    (hjoin : ∀ a ∈ S, ∀ b ∈ T, G.Adj a b) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ L : List V, L.head? = some a ∧ L.getLast? = some b ∧
      L.Nodup ∧ L.IsChain G.Adj ∧ (∀ x, x ∈ L ↔ x ∈ S ∪ T) := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := hS
  obtain ⟨L₀,R₀,hL₀,hR₀,hnd,hLc,hRc,hm⟩ :=
    two_chains (G := G.induce S)
      ⟨⟨a,ha⟩, ⟨b,hb⟩, fun he => hab (congrArg Subtype.val he)⟩ hα
  obtain ⟨M,hMe,hMn,hMc,hMm⟩ := clique_list hT hclique
  let L := L₀.map Subtype.val
  let R := R₀.map Subtype.val
  have hl : L ≠ [] := by cases L₀ <;> simp_all [L]
  have hr : R ≠ [] := by cases R₀ <;> simp_all [R]
  have hmS (x : V) : x ∈ L ++ R ↔ x ∈ S := by
    change x ∈ L₀.map Subtype.val ++ R₀.map Subtype.val ↔ _
    rw [← List.map_append, List.mem_map]
    constructor
    · rintro ⟨y,_,rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x,hx⟩, hm _, rfl⟩
  have hnLR : (L ++ R).Nodup := by
    change (L₀.map Subtype.val ++ R₀.map Subtype.val).Nodup
    rw [← List.map_append]
    exact hnd.map Subtype.val_injective
  have lim (x : V) (hx : x ∈ L) : x ∈ S := (hmS x).mp (List.mem_append_left _ hx)
  have rim (x : V) (hx : x ∈ R) : x ∈ S := (hmS x).mp (List.mem_append_right _ hx)
  have lc : L.IsChain G.Adj :=
    List.isChain_map_of_isChain Subtype.val (fun _ _ h => induce_adj.mp h) hLc
  have rc : R.IsChain G.Adj :=
    List.isChain_map_of_isChain Subtype.val (fun _ _ h => induce_adj.mp h) hRc
  let W := L ++ (M ++ R)
  refine ⟨L.head hl, lim _ (List.head_mem hl), R.getLast hr, rim _ (List.getLast_mem hr), W,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [W, List.head?_eq_some_head hl]
  · simp [W, List.getLast?_eq_some_getLast hr]
  · have hLR := List.nodup_append.mp hnLR
    have hMr : (M ++ R).Nodup := by
      refine List.nodup_append.mpr ⟨hMn,hLR.2.1,?_⟩
      rintro x hx y hy rfl
      exact Set.disjoint_left.mp hST (rim x hy) ((hMm x).mp hx)
    refine List.nodup_append.mpr ⟨hLR.1,hMr,?_⟩
    intro x hx y hy
    rcases List.mem_append.mp hy with hy | hy
    · rintro rfl
      exact Set.disjoint_left.mp hST (lim x hx) ((hMm x).mp hy)
    · exact hLR.2.2 x hx y hy
  · have hMR : (M ++ R).IsChain G.Adj := by
      apply hMc.append rc
      intro x hx y hy
      exact (hjoin y (rim y (List.mem_of_mem_head? hy)) x ((hMm x).mp
        (List.mem_of_mem_getLast? hx))).symm
    apply lc.append hMR
    intro x hx y hy
    rw [List.head?_append_of_ne_nil _ hMe] at hy
    exact hjoin x (lim x (List.mem_of_mem_getLast? hx)) y ((hMm y).mp
      (List.mem_of_mem_head? hy))
  · intro x
    have h := hmS x
    simp only [List.mem_append] at h
    simp only [W, List.mem_append, Set.mem_union, ← h, hMm]
    tauto

private theorem spare_cover {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {S : Set V} (hα : (G.induce S).indepNum ≤ 2) :
    ∃ P R : List V, (P ++ R).Nodup ∧ P.IsChain G.Adj ∧ R.IsChain G.Adj ∧
      (∀ x, x ∈ P ++ R ↔ x ∈ S) := by
  classical
  by_cases hpair : ∃ a ∈ S, ∃ b ∈ S, a ≠ b
  · obtain ⟨a, ha, b, hb, hab⟩ := hpair
    obtain ⟨P, R, _, _, hn, hp, hr, hm⟩ :=
      two_chains (G := G.induce S)
        ⟨⟨a,ha⟩, ⟨b,hb⟩, fun he => hab (congrArg Subtype.val he)⟩ hα
    refine ⟨P.map Subtype.val, R.map Subtype.val, ?_, ?_, ?_, ?_⟩
    · rw [← List.map_append]
      exact hn.map Subtype.val_injective
    · exact List.isChain_map_of_isChain Subtype.val (fun _ _ h => induce_adj.mp h) hp
    · exact List.isChain_map_of_isChain Subtype.val (fun _ _ h => induce_adj.mp h) hr
    · intro x
      rw [← List.map_append, List.mem_map]
      constructor
      · rintro ⟨y, _, rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x,hx⟩, hm _, rfl⟩
  · by_cases hS : S.Nonempty
    · obtain ⟨a, ha⟩ := hS
      refine ⟨[a], [], by simp, by simp, by simp, ?_⟩
      intro x
      simp only [List.append_nil, List.mem_singleton]
      exact ⟨fun h => h.symm ▸ ha, fun hx => by
        by_contra hn
        exact hpair ⟨x, hx, a, ha, hn⟩⟩
    · refine ⟨[], [], by simp, by simp, by simp, ?_⟩
      intro x
      simp only [List.nil_append, List.not_mem_nil, false_iff]
      exact fun hx => hS ⟨x,hx⟩

/-- An ordered anchor path survives insertion of a disjoint spare set with
independence number at most two when both anchor endpoints see every spare vertex. -/
theorem spare_sandwich {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {S U : Set V} {L : List V} {a b : V}
    (hhead : L.head? = some a) (htail : L.getLast? = some b)
    (hn : L.Nodup) (hc : L.IsChain G.Adj) (hm : ∀ x, x ∈ L ↔ x ∈ U)
    (hSU : Disjoint S U) (hα : (G.induce S).indepNum ≤ 2)
    (ha : ∀ x ∈ S, G.Adj a x) (hb : ∀ x ∈ S, G.Adj b x) :
    ∃ c ∈ S ∪ ({a,b} : Set V), ∃ d ∈ S ∪ ({a,b} : Set V), ∃ W : List V,
      W.head? = some c ∧ W.getLast? = some d ∧ W.Nodup ∧ W.IsChain G.Adj ∧
      (∀ x, x ∈ W ↔ x ∈ S ∪ U) := by
  obtain ⟨P,R,hnPR,hPc,hRc,hmS⟩ := spare_cover (G := G) hα
  have hP (x : V) (hx : x ∈ P) : x ∈ S := (hmS x).mp (List.mem_append_left _ hx)
  have hR (x : V) (hx : x ∈ R) : x ∈ S := (hmS x).mp (List.mem_append_right _ hx)
  have hePL : (P ++ L).getLast? = some b := by simp [htail]
  have hWc : ((P ++ L) ++ R).IsChain G.Adj := by
    apply (hPc.append hc ?_).append hRc
    · intro x hx y hy
      have hbx : b = x := by simpa [hePL] using hx
      exact hbx ▸ hb y (hR y (List.mem_of_mem_head? hy))
    · intro x hx y hy
      have hay : a = y := by simpa [hhead] using hy
      exact hay ▸ (ha x (hP x (List.mem_of_mem_getLast? hx))).symm
  have hWn : ((P ++ L) ++ R).Nodup := by
    have hnd := List.nodup_append.mp hnPR
    have hPL : (P ++ L).Nodup := by
      refine List.nodup_append.mpr ⟨hnd.1, hn, ?_⟩
      rintro x hx y hy rfl
      exact Set.disjoint_left.mp hSU (hP x hx) ((hm x).mp hy)
    refine List.nodup_append.mpr ⟨hPL, hnd.2.1, ?_⟩
    intro x hx y hy
    rcases List.mem_append.mp hx with hx | hx
    · exact hnd.2.2 x hx y hy
    · rintro rfl
      exact Set.disjoint_left.mp hSU (hR x hy) ((hm x).mp hx)
  let W := (P ++ L) ++ R
  have hWe : W ≠ [] := List.ne_nil_of_mem
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_of_mem_head? hhead)))
  refine ⟨W.head hWe, ?_, W.getLast hWe, ?_, W, List.head?_eq_some_head hWe,
    List.getLast?_eq_some_getLast hWe, hWn, hWc, ?_⟩
  · by_cases hp : P = []
    · have he : W.head? = some a := by simp [W, hp, hhead]
      exact Or.inr (by simp [List.head_of_head?_eq_some he])
    · have he : W.head? = some (P.head hp) := by
        simp [W, List.head?_eq_some_head hp]
      exact Or.inl (by rw [List.head_of_head?_eq_some he]; exact hP _ (List.head_mem hp))
  · by_cases hr : R = []
    · have he : W.getLast? = some b := by simp [W, hr, htail]
      exact Or.inr (by simp [List.getLast_of_getLast?_eq_some he])
    · have he : W.getLast? = some (R.getLast hr) := by
        simp [W, List.getLast?_eq_some_getLast hr]
      exact Or.inl (by rw [List.getLast_of_getLast?_eq_some he]; exact hR _ (List.getLast_mem hr))
  · intro x
    have h := hmS x
    simp only [List.mem_append] at h
    simp only [W, List.mem_append, Set.mem_union, ← h, hm]
    tauto

#print axioms block_path
#print axioms spare_sandwich
end Graph199
