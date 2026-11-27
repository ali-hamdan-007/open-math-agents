import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Degrees
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance
import Mathlib.Combinatorics.SimpleGraph.Diam
import Graph189BipartiteSmall

namespace Graph189LowDegreeTwo
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem two_edges {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hne : a ≠ c) (hn : ¬ G.Adj a c) : G.dist a c = 2 := by
  let p : G.Walk a c := .cons hab (.cons hbc .nil)
  have hp : G.dist a c ≤ 2 := by simpa [p] using G.dist_le p
  have hpos : 0 < G.dist a c := Nat.pos_of_ne_zero
    (fun h => hne (p.reachable.dist_eq_zero_iff.mp h))
  have hone : G.dist a c ≠ 1 := fun h => hn (dist_eq_one_iff_adj.mp h)
  omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem split_two (h : G.Connected) {a c : V} (hd : G.dist a c = 2) :
    ∃ b, G.Adj a b ∧ G.Adj b c := by
  obtain ⟨p,hp⟩ := h.exists_walk_length_eq_dist a c
  rw [hd] at hp
  have h1 := p.adj_getVert_succ (i := 0) (by omega)
  have h2 := p.adj_getVert_succ (i := 1) (by omega)
  rw [Walk.getVert_zero] at h1
  rw [show 1+1 = p.length by omega, Walk.getVert_length] at h2
  exact ⟨p.getVert 1,h1,h2⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem split_three (h : G.Connected) {a c : V} (hd : G.dist a c = 3) :
    ∃ b, G.dist a b = 2 ∧ G.Adj b c := by
  obtain ⟨p,hp⟩ := h.exists_walk_length_eq_dist a c
  rw [hd] at hp
  let b := p.getVert 2
  have hstep := p.adj_getVert_succ (i := 2) (by omega)
  rw [show 2+1 = p.length by omega, Walk.getVert_length] at hstep
  have hle : G.dist a b ≤ 2 := (G.dist_le (p.take 2)).trans (by simp [Walk.take_length])
  have htri := h.dist_triangle (u := a) (v := b) (w := c)
  rw [hd,dist_eq_one_iff_adj.mpr hstep] at htri
  exact ⟨b,by omega,hstep⟩

/-- A degree-two vertex and a uniform cap of two vertices at distance two
bound the order of a connected graph of diameter at most three. -/
theorem layer_bounds (h : G.Connected) (hd : G.diam ≤ 3)
    (hcap : ∀ x, (Finset.univ.filter (fun v => G.dist x v = 2)).card ≤ 2)
    (z : V) (hz : G.degree z = 2) :
    (Finset.univ.filter (fun v => G.dist z v = 2)).card +
        (Finset.univ.filter (fun v => G.dist z v = 3)).card + 3 = Fintype.card V ∧
      (Finset.univ.filter (fun v => G.dist z v = 3)).card ≤ 2 := by
  classical
  have := h.nonempty
  let W := Finset.univ.filter (fun v => G.dist z v = 2)
  let R := Finset.univ.filter (fun v => G.dist z v = 3)
  have hW : W.card ≤ 2 := hcap z
  have hmemW (w : V) : w ∈ W ↔ G.dist z w = 2 := by simp [W]
  have hmemR (r : V) : r ∈ R ↔ G.dist z r = 3 := by simp [R]
  have hR : R.card ≤ 2 := by
    by_contra! hR
    have reachW (r : V) (hr : r ∈ R) : ∃ w ∈ W, G.Adj w r := by
      obtain ⟨w,hw,he⟩ := split_three h ((hmemR r).mp hr)
      exact ⟨w,(hmemW w).mpr hw,he⟩
    obtain ⟨w,hw,r₁,hr₁,r₂,hr₂,hrne,hw₁,hw₂⟩ :
        ∃ w ∈ W, ∃ r₁ ∈ R, ∃ r₂ ∈ R, r₁ ≠ r₂ ∧ G.Adj w r₁ ∧ G.Adj w r₂ := by
      by_contra! hn
      let f (r : V) := if hr : r ∈ R then (reachW r hr).choose else z
      have hf (r : V) (hr : r ∈ R) : f r ∈ W ∧ G.Adj (f r) r := by
        simpa [f,hr] using (reachW r hr).choose_spec
      have hle : R.card ≤ W.card := Finset.card_le_card_of_injOn f
        (fun r hr => (hf r hr).1) (by
          intro r₁ hr₁ r₂ hr₂ he
          by_contra hne
          exact hn _ (hf r₁ hr₁).1 _ hr₁ _ hr₂ hne (hf r₁ hr₁).2
            (he.symm ▸ (hf r₂ hr₂).2))
      omega
    obtain ⟨a,hza,haw⟩ := split_two h ((hmemW w).mp hw)
    let A := G.neighborFinset z
    have ha : a ∈ A := (G.mem_neighborFinset z a).mpr hza
    have hA : A.card = 2 := hz
    have hnA : 0 < (A.erase a).card := by rw [Finset.card_erase_of_mem ha,hA]; decide
    obtain ⟨b,hb⟩ := Finset.card_pos.mp hnA
    have hba : b ≠ a := Finset.ne_of_mem_erase hb
    have hbA : b ∈ A := Finset.mem_of_mem_erase hb
    have hzb := (G.mem_neighborFinset z b).mp hbA
    have hAE : ({a,b} : Finset V) = A := Finset.eq_of_subset_of_card_le
      (by intro x hx; rcases (show x = a ∨ x = b from by simpa using hx) with rfl | rfl
          · exact ha
          · exact hbA)
      (by rw [hA,Finset.card_pair hba.symm])
    let D := Finset.univ.filter (fun r => G.dist a r = 2)
    have hD : D.card ≤ 2 := hcap a
    have from_edge (r : V) (hr : r ∈ R) (y : V) (hay : G.Adj a y) (hyr : G.Adj y r) :
        r ∈ D := by
      have hrd := (hmemR r).mp hr
      have hnadj : ¬ G.Adj a r := by
        intro har
        have htri := h.dist_triangle (u := z) (v := a) (w := r)
        rw [hrd,dist_eq_one_iff_adj.mpr hza,dist_eq_one_iff_adj.mpr har] at htri
        omega
      have hne : a ≠ r := by
        intro he
        rw [← he,dist_eq_one_iff_adj.mpr hza] at hrd
        contradiction
      have hdist := two_edges hay hyr hne hnadj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hdist⟩
    have hDE : ({r₁,r₂} : Finset V) = D := Finset.eq_of_subset_of_card_le
      (by intro r hr; rcases (show r = r₁ ∨ r = r₂ from by simpa using hr) with e | e
          · subst r; exact from_edge r₁ hr₁ w haw hw₁
          · subst r; exact from_edge r₂ hr₂ w haw hw₂)
      (by simpa [Finset.card_pair hrne] using hD)
    have onlyR {x : V} (hx : G.dist a x = 2) : x ∈ R := by
      have hD' : x ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩
      rw [← hDE] at hD'
      rcases (show x = r₁ ∨ x = r₂ from by simpa using hD') with he | he
      · exact he.symm ▸ hr₁
      · exact he.symm ▸ hr₂
    have hab : G.Adj a b := by
      by_contra hn
      have hBR := (hmemR b).mp (onlyR (two_edges hza.symm hzb hba.symm hn))
      rw [dist_eq_one_iff_adj.mpr hzb] at hBR
      contradiction
    have allW (y : V) (hy : y ∈ W) : G.Adj a y := by
      obtain ⟨u,hzu,huy⟩ := split_two h ((hmemW y).mp hy)
      have hu : u ∈ A := (G.mem_neighborFinset z u).mpr hzu
      rw [← hAE] at hu
      rcases (show u = a ∨ u = b from by simpa using hu) with rfl | rfl
      · exact huy
      · by_contra hn
        have hy' := (hmemW y).mp hy
        have hne : a ≠ y := by
          intro he
          rw [← he,dist_eq_one_iff_adj.mpr hza] at hy'
          contradiction
        have hyR := (hmemR y).mp (onlyR (two_edges hab huy hne hn))
        omega
    have hsub : R ⊆ D := by
      intro r hr
      obtain ⟨y,hy,hyr⟩ := reachW r hr
      exact from_edge r hr y (allW y hy) hyr
    exact (Nat.not_lt_of_ge ((Finset.card_le_card hsub).trans hD)) hR
  have hU : Finset.univ = insert z (G.neighborFinset z ∪ W ∪ R) := by
    ext x
    simp only [Finset.mem_univ,Finset.mem_insert,Finset.mem_union,true_iff]
    have hle := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp h) (u := z) (v := x)).trans hd
    have hcases : G.dist z x = 0 ∨ G.dist z x = 1 ∨ G.dist z x = 2 ∨ G.dist z x = 3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · exact Or.inl (((h.preconnected z x).dist_eq_zero_iff.mp h0).symm)
    · exact Or.inr (Or.inl (Or.inl ((G.mem_neighborFinset z x).mpr (dist_eq_one_iff_adj.mp h1))))
    · exact Or.inr (Or.inl (Or.inr ((hmemW x).mpr h2)))
    · exact Or.inr (Or.inr ((hmemR x).mpr h3))
  have hzNot : z ∉ (G.neighborFinset z ∪ W ∪ R) := by
    simp [hmemW,hmemR]
  have hDisW : Disjoint (G.neighborFinset z) W := by
    refine Finset.disjoint_left.mpr ?_
    intro v hn hw
    have hd₁ := dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset z v).mp hn)
    have hd₂ := (hmemW v).mp hw
    omega
  have hDisR : Disjoint (G.neighborFinset z ∪ W) R := by
    refine Finset.disjoint_left.mpr ?_
    intro v hv hr
    have hd₃ := (hmemR v).mp hr
    rcases Finset.mem_union.mp hv with ha | hw
    · have hd₁ := dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset z v).mp ha)
      omega
    · have hd₂ := (hmemW v).mp hw
      omega
  have hun := congrArg Finset.card hU
  rw [Finset.card_univ, Finset.card_insert_of_notMem hzNot,
    Finset.card_union_of_disjoint hDisR, Finset.card_union_of_disjoint hDisW] at hun
  have hn : (G.neighborFinset z).card = 2 := hz
  change W.card + R.card + 3 = Fintype.card V ∧ R.card ≤ 2
  exact ⟨by omega,hR⟩

theorem order_le_seven (h : G.Connected) (hd : G.diam ≤ 3)
    (hcap : ∀ x, (Finset.univ.filter (fun v => G.dist x v = 2)).card ≤ 2)
    (z : V) (hz : G.degree z = 2) : Fintype.card V ≤ 7 := by
  obtain ⟨hn,hR⟩ := layer_bounds h hd hcap z hz
  have hW := hcap z
  omega

/-- The conjecture's even-distance bound supplies the distance-two cap when the
second-smallest degree is two. -/
theorem distance_two_cap [Nontrivial V]
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + G.secondSmallestDegree)
    (hs : G.secondSmallestDegree = 2) :
    ∀ x, (Finset.univ.filter (fun v => G.dist x v = 2)).card ≤ 2 := by
  intro x
  have hE := (Finset.le_max' _ _ (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩)).trans hσ
  rw [hs] at hE
  let D := Finset.univ.filter (fun v => G.dist x v = 2)
  have hsub : insert x D ⊆ Finset.univ.filter (fun v => Even (G.dist x v)) := by
    intro v hv
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rcases Finset.mem_insert.mp hv with rfl | hmem
    · simp
    · have hh := (Finset.mem_filter.mp hmem).2
      exact hh ▸ (by decide : Even 2)
  have hne : x ∉ D := by simp [D]
  have hle := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hne] at hle
  change D.card + 1 ≤ G.distEven x at hle
  change D.card ≤ 2
  omega


theorem order_le_seven_of_secondSmallestDegree_eq_two [Nontrivial V]
    (h : G.Connected) (hd : G.diam ≤ 3)
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + G.secondSmallestDegree)
    (hs : G.secondSmallestDegree = 2) (z : V) (hz : G.degree z = 2) :
    Fintype.card V ≤ 7 :=
  order_le_seven h hd (distance_two_cap hσ hs) z hz

omit [Fintype V] in
private theorem other_of_card_two {S : Finset V} {x : V} (hx : x ∈ S) (hc : S.card = 2) :
    ∃ y ∈ S, y ≠ x ∧ S = {x,y} := by
  have he : 0 < (S.erase x).card := by rw [Finset.card_erase_of_mem hx,hc]; decide
  obtain ⟨y,hy⟩ := Finset.card_pos.mp he
  have hxy := Finset.ne_of_mem_erase hy
  have hyS := Finset.mem_of_mem_erase hy
  refine ⟨y,hyS,hxy,?_⟩
  symm
  apply Finset.eq_of_subset_of_card_le _ (by simp [hc, Finset.card_pair hxy.symm])
  intro v hv
  rcases (show v = x ∨ v = y from by simpa using hv) with e | e
  · exact e.symm ▸ hx
  · exact e.symm ▸ hyS

/-- Small distance layers around a degree-two vertex can be joined to form a
Hamiltonian path. The degree condition is used only through the distance-two cap. -/
theorem traceable_of_degree_two_of_cap (h : G.Connected) (hd : G.diam ≤ 3)
    (hmin : ∀ x, 2 ≤ G.degree x) (hlarge : 6 ≤ Fintype.card V)
    (hcap : ∀ x, (Finset.univ.filter (fun v => G.dist x v = 2)).card ≤ 2)
    (z : V) (hz : G.degree z = 2) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have := h.nonempty
  let W := Finset.univ.filter (fun v => G.dist z v = 2)
  let R := Finset.univ.filter (fun v => G.dist z v = 3)
  let A := G.neighborFinset z
  obtain ⟨horder,hR⟩ := layer_bounds h hd hcap z hz
  change W.card + R.card + 3 = Fintype.card V at horder
  change R.card ≤ 2 at hR
  have hW : W.card ≤ 2 := hcap z
  have hA : A.card = 2 := hz
  have hE (x : V) : x = z ∨ x ∈ A ∨ x ∈ W ∨ x ∈ R := by
    have hle := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp h) (u := z) (v := x)).trans hd
    have hcases : G.dist z x = 0 ∨ G.dist z x = 1 ∨ G.dist z x = 2 ∨ G.dist z x = 3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · exact Or.inl ((h.preconnected z x).dist_eq_zero_iff.mp h0).symm
    · exact Or.inr (Or.inl ((G.mem_neighborFinset z x).mpr (dist_eq_one_iff_adj.mp h1)))
    · exact Or.inr (Or.inr (Or.inl (by simp [W,h2])))
    · exact Or.inr (Or.inr (Or.inr (by simp [R,h3])))
  have memA (x : V) : x ∈ A ↔ G.Adj z x := G.mem_neighborFinset z x
  have memW (x : V) : x ∈ W ↔ G.dist z x = 2 := by simp [W]
  have memR (x : V) : x ∈ R ↔ G.dist z x = 3 := by simp [R]
  have reachA (w : V) (hw : w ∈ W) : ∃ a ∈ A, G.Adj a w := by
    obtain ⟨a,ha,haw⟩ := split_two h ((memW w).mp hw)
    exact ⟨a,(memA a).mpr ha,haw⟩
  have reachW (r : V) (hr : r ∈ R) : ∃ w ∈ W, G.Adj w r := by
    obtain ⟨w,hw,hwr⟩ := split_three h ((memR r).mp hr)
    exact ⟨w,(memW w).mpr hw,hwr⟩
  have remote_neighbors (r : V) (hr : r ∈ R) (v : V) (hv : G.Adj r v) :
      v ∈ W ∨ v ∈ R := by
    have hrd := (memR r).mp hr
    rcases hE v with he | ha | hw | hR'
    · subst v
      rw [dist_eq_one_iff_adj.mpr hv.symm] at hrd
      contradiction
    · have htri := h.dist_triangle (u := z) (v := v) (w := r)
      rw [hrd,dist_eq_one_iff_adj.mpr ((memA v).mp ha),dist_eq_one_iff_adj.mpr hv.symm] at htri
      omega
    · exact Or.inl hw
    · exact Or.inr hR'
  have neighbor_rest (v w : V) (hw : G.Adj v w) : ∃ x, x ≠ w ∧ G.Adj v x := by
    have hne : 0 < ((G.neighborFinset v).erase w).card := by
      rw [Finset.card_erase_of_mem ((G.mem_neighborFinset v w).mpr hw)]
      have hv : 2 ≤ (G.neighborFinset v).card := hmin v
      omega
    obtain ⟨x,hx⟩ := Finset.card_pos.mp hne
    exact ⟨x,Finset.ne_of_mem_erase hx,(G.mem_neighborFinset v x).mp (Finset.mem_of_mem_erase hx)⟩
  have build (L : List V) (hlen : L.length = Fintype.card V)
      (hc : L.IsChain G.Adj) (hcover : ∀ x, x ∈ L) :
      ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
    have hne : L ≠ [] := List.ne_nil_of_mem (hcover z)
    have huniv : L.toFinset = Finset.univ := by ext x; simp [hcover]
    have hL : (L : Multiset V).Nodup := Multiset.toFinset_card_eq_card_iff_nodup.mp (by
      change L.toFinset.card = L.length
      rw [huniv,Finset.card_univ,hlen])
    exact Graph189Bipartite.hamiltonian_of_chain L hne hc hL hlen
  have attach (w : V) (hw : w ∈ W) (T : List V) (hh : T.head? = some w)
      (hc : T.IsChain G.Adj) (hl : T.length = W.card + R.card)
      (hcov : ∀ x, x ∈ W ∨ x ∈ R → x ∈ T) :
      ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
    obtain ⟨a,ha,haw⟩ := reachA w hw
    obtain ⟨b,hb,_,heA⟩ := other_of_card_two ha hA
    have hca : (a :: T).IsChain G.Adj := hc.cons (by simpa [hh] using haw)
    have hzA := (memA a).mp ha
    have hzB := (memA b).mp hb
    refine build (b :: z :: a :: T) (by simp only [List.length_cons,hl]; omega)
      (hca.cons (by simp [hzA]) |>.cons (by simp [hzB.symm])) ?_
    intro x
    have hx : x = z ∨ x = a ∨ x = b ∨ x ∈ W ∨ x ∈ R := by simpa [heA,or_assoc] using hE x
    rcases hx with e | e | e | he | he
    · simp [e]
    · simp [e]
    · simp [e]
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hcov _ (Or.inl he))))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hcov _ (Or.inr he))))
  have shape : (W.card = 1 ∧ R.card = 2) ∨ (W.card = 2 ∧ R.card = 1) ∨
      (W.card = 2 ∧ R.card = 2) := by omega
  rcases shape with ⟨hW₁,hR₂⟩ | ⟨hW₂,hR₁⟩ | ⟨hW₂,hR₂⟩
  · obtain ⟨w,hew⟩ := Finset.card_eq_one.mp hW₁
    obtain ⟨r,s,hrs,hers⟩ := Finset.card_eq_two.mp hR₂
    have hr : r ∈ R := by simp [hers]
    have hs : s ∈ R := by simp [hers]
    have hw : w ∈ W := by simp [hew]
    obtain ⟨y,hy,hyr⟩ := reachW r hr
    have hyw : y = w := by simpa [hew] using hy
    subst y
    obtain ⟨t,ht,htr⟩ := neighbor_rest r w hyr.symm
    have hts : t = s := by
      have htR := remote_neighbors r hr t htr
      have htne : t ≠ r := G.ne_of_adj htr.symm
      simpa [hew,hers,ht,htne] using htR
    refine attach w hw [w,r,s] rfl (by simp [hyr,hts ▸ htr]) (by simp [hW₁,hR₂]) ?_
    intro x hx
    simpa [hew,hers,or_assoc] using hx
  · obtain ⟨w,v,hwv,hew⟩ := Finset.card_eq_two.mp hW₂
    obtain ⟨r,her⟩ := Finset.card_eq_one.mp hR₁
    have hw : w ∈ W := by simp [hew]
    have hr : r ∈ R := by simp [her]
    have full {x : V} (hx : x ∈ W) : G.Adj r x := by
      have hsub : G.neighborFinset r ⊆ W := by
        intro y hy
        have hadj := (G.mem_neighborFinset r y).mp hy
        rcases remote_neighbors r hr y hadj with h | h
        · exact h
        · have hy' : y = r := by simpa [her] using h
          exact (G.ne_of_adj hadj hy'.symm).elim
      have hle : W.card ≤ (G.neighborFinset r).card := by rw [hW₂]; exact hmin r
      exact (G.mem_neighborFinset r x).mp ((Finset.eq_of_subset_of_card_le hsub hle).symm ▸ hx)
    have hv : v ∈ W := by simp [hew]
    refine attach w hw [w,r,v] rfl (by simp [(full hw).symm,full hv])
      (by simp [hW₂,hR₁]) ?_
    intro x hx
    have hh : x = w ∨ x = v ∨ x = r := by simpa [hew,her,or_assoc] using hx
    simpa [or_comm,or_left_comm,or_assoc] using hh
  · obtain ⟨r,s,hrs,hers⟩ := Finset.card_eq_two.mp hR₂
    have hr : r ∈ R := by simp [hers]
    have hs : s ∈ R := by simp [hers]
    obtain ⟨w,hw,hwr⟩ := reachW r hr
    obtain ⟨v,hv,hvw,hew⟩ := other_of_card_two hw hW₂
    have cover (x : V) (hx : x ∈ W ∨ x ∈ R) : x = w ∨ x = v ∨ x = r ∨ x = s :=
      by simpa [hew,hers,or_assoc] using hx
    by_cases hrsAdj : G.Adj r s
    · by_cases hvs : G.Adj v s
      · refine attach w hw [w,r,s,v] rfl (by simp [hwr,hrsAdj,hvs.symm])
          (by simp [hW₂,hR₂]) ?_
        intro x hx
        simpa [or_comm,or_left_comm,or_assoc] using cover x hx
      · obtain ⟨y,hy,hys⟩ := reachW s hs
        have hwy : G.Adj w s := by
          have hy' : y = w ∨ y = v := by simpa [hew] using hy
          rcases hy' with e | e
          · exact e ▸ hys
          · exact (hvs (e ▸ hys)).elim
        by_cases hvr : G.Adj v r
        · refine attach w hw [w,s,r,v] rfl (by simp [hwy,hrsAdj.symm,hvr.symm])
            (by simp [hW₂,hR₂]) ?_
          intro x hx
          simpa [or_comm,or_left_comm,or_assoc] using cover x hx
        · by_cases hvwAdj : G.Adj v w
          · refine attach v hv [v,w,r,s] rfl (by simp [hvwAdj,hwr,hrsAdj])
              (by simp [hW₂,hR₂]) ?_
            intro x hx
            simpa [or_comm,or_left_comm,or_assoc] using cover x hx
          · have hvsub : G.neighborFinset v ⊆ A := by
              intro x hx
              have h := (G.mem_neighborFinset v x).mp hx
              rcases hE x with e | he | he | he
              · have hvd := (memW v).mp hv
                rw [e] at h
                rw [dist_eq_one_iff_adj.mpr h.symm] at hvd
                contradiction
              · exact he
              · have hx' : x = w ∨ x = v := by simpa [hew] using he
                rcases hx' with e | e
                · exact (hvwAdj (e ▸ h)).elim
                · exact (G.ne_of_adj h e.symm).elim
              · have hx' : x = r ∨ x = s := by simpa [hers] using he
                rcases hx' with e | e
                · exact (hvr (e ▸ h)).elim
                · exact (hvs (e ▸ h)).elim
            have heN : G.neighborFinset v = A :=
              Finset.eq_of_subset_of_card_le hvsub (hA.symm ▸ hmin v)
            have hvA (x : V) (hx : x ∈ A) : G.Adj v x :=
              (G.mem_neighborFinset v x).mp (heN ▸ hx)
            obtain ⟨a,ha,haw⟩ := reachA w hw
            obtain ⟨b,hb,_,hab⟩ := other_of_card_two ha hA
            have hzb := (memA b).mp hb
            refine build [z,b,v,a,w,r,s] (by simp; omega)
              (by simp [hzb,(hvA b hb).symm,hvA a ha,haw,hwr,hrsAdj]) ?_
            intro x
            simpa [hab,hew,hers,or_comm,or_assoc,or_left_comm] using hE x
    · have full {x y : V} (hx : x ∈ R) (hy : y ∈ W) : G.Adj x y := by
        have hsub : G.neighborFinset x ⊆ W := by
          intro u hu
          have he := (G.mem_neighborFinset x u).mp hu
          rcases remote_neighbors x hx u he with h | huR
          · exact h
          · have hxx : x = r ∨ x = s := by simpa [hers] using hx
            have huu : u = r ∨ u = s := by simpa [hers] using huR
            rcases hxx with e | e <;> rcases huu with e' | e'
            · exact (G.ne_of_adj he (e.trans e'.symm)).elim
            · exact (hrsAdj (e ▸ e' ▸ he)).elim
            · exact (hrsAdj (e' ▸ e ▸ he.symm)).elim
            · exact (G.ne_of_adj he (e.trans e'.symm)).elim
        have hle : W.card ≤ (G.neighborFinset x).card := by rw [hW₂]; exact hmin x
        exact (G.mem_neighborFinset x y).mp ((Finset.eq_of_subset_of_card_le hsub hle).symm ▸ hy)
      refine attach w hw [w,r,v,s] rfl (by simp [hwr,full hr hv,(full hs hv).symm])
        (by simp [hW₂,hR₂]) ?_
      intro x hx
      simpa [or_comm,or_left_comm,or_assoc] using cover x hx

/-- The diameter-three residual of conjecture 189 is traceable when both the
minimum and the second-smallest degree are two. -/
theorem traceable_min_two_sigma_two [Nontrivial V] (h : G.Connected) (hd : G.diam ≤ 3)
    (hsmall : G.minDegree = 2) (hsecond : G.secondSmallestDegree = 2)
    (hgap : G.minDegree + G.secondSmallestDegree + 1 < Fintype.card V)
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + G.secondSmallestDegree) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  exact traceable_of_degree_two_of_cap h hd
    (fun x => hsmall ▸ G.minDegree_le_degree x) (by omega) (distance_two_cap hσ hsecond)
    z (hz.symm.trans hsmall)

#print axioms traceable_min_two_sigma_two
#print axioms order_le_seven_of_secondSmallestDegree_eq_two
#print axioms traceable_of_degree_two_of_cap
end Graph189LowDegreeTwo
