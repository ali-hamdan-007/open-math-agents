import Graph189DegreeTwoNearSaturation

namespace Graph189EccFour
open SimpleGraph Graph189LowDegreeTwo Graph189DegreeTwoNearSaturation
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem cap_on (s : ℕ)
    (cap : ∀ x : V, (Finset.univ.filter (fun y => G.dist x y = 2)).card ≤ s)
    {x : V} (S : Finset V) (h : ∀ y ∈ S, G.dist x y = 2) : S.card ≤ s :=
  (Finset.card_le_card (show S ⊆ Finset.univ.filter (fun y => G.dist x y = 2) from
    fun y hy => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h y hy⟩)).trans (cap x)

omit [DecidableRel G.Adj] in
/-- The common middle-layer vertex cannot meet both private middle-layer vertices
once the union of the exclusive remote sets and the root exceeds the even cap. -/
theorem empty_overlap_impossible (s : ℕ) (hs : 4 ≤ s)
    (cap : ∀ x : V, (Finset.univ.filter (fun y => G.dist x y = 2)).card ≤ s)
    (P Q : Finset V) (hp : P.card + 1 ≤ s) (hq : Q.card + 1 ≤ s)
    (hlarge : 2*s-3 ≤ P.card+Q.card)
    (hPQ : Disjoint P Q) {c p q z : V}
    (hzP : z ∉ P) (hzQ : z ∉ Q) (hcP : c ∉ P) (hcQ : c ∉ Q)
    (hcp : G.Adj c p) (hcq : G.Adj c q) (hcz : G.dist c z = 2)
    (hP : ∀ x ∈ P, G.Adj p x ∧ ¬ G.Adj c x)
    (hQ : ∀ x ∈ Q, G.Adj q x ∧ ¬ G.Adj c x) : False := by
  have hp' : P.card ≥ s-2 := by omega
  have hq' : Q.card ≥ s-2 := by omega
  have hcap := cap_on s cap (x := c) (insert z (P ∪ Q)) (by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hcz
    rcases Finset.mem_union.mp hx with hx | hx
    · exact two_edges hcp (hP x hx).1 (fun e => hcP (e ▸ hx)) (hP x hx).2
    · exact two_edges hcq (hQ x hx).1 (fun e => hcQ (e ▸ hx)) (hQ x hx).2)
  rw [Finset.card_insert_of_notMem (fun h => (Finset.mem_union.mp h).elim hzP hzQ),
    Finset.card_union_of_disjoint hPQ] at hcap
  omega

/-- The saturated one-overlap configuration is impossible. Here the common
middle-layer vertex sees p, misses q, and sees the overlap remote t. -/
theorem single_overlap_direction_impossible (s : ℕ) (hs : 4 ≤ s)
    (cap : ∀ x : V, (Finset.univ.filter (fun y => G.dist x y = 2)).card ≤ s)
    (P Q : Finset V) (hP : P.card = s-2) (hQ : Q.card = s-2)
    (hPQ : Disjoint P Q) (z a c p q t f : V)
    (hqP : q ∉ P) (hzP : z ∉ P) (hzQ : z ∉ Q) (haQ : a ∉ Q)
    (hfQ : f ∉ Q) (htP : t ∉ P) (htQ : t ∉ Q)
    (hcP : c ∉ P) (hcQ : c ∉ Q) (hpQ : p ∉ Q)
    (hqz : q ≠ z) (haz : a ≠ z) (hfz : f ≠ z) (hfa : f ≠ a)
    (hcqne : c ≠ q) (hpfne : p ≠ f)
    (hcz : G.dist c z = 2) (hpz : G.dist p z = 2) (hpa : G.dist p a = 2)
    (hcp : G.Adj c p) (hcq : ¬ G.Adj c q) (hcmeet : ∃ b, G.Adj c b ∧ G.Adj b q)
    (hct : G.Adj c t) (hpf : ¬ G.Adj p f)
    (hpP : ∀ x ∈ P, G.Adj p x ∧ ¬ G.Adj c x)
    (hqQ : ∀ x ∈ Q, G.Adj q x ∧ ¬ G.Adj c x ∧ ¬ G.Adj p x)
    (hdegQ : ∀ y ∈ Q, s ≤ G.degree y)
    (hNbrQ : ∀ y ∈ Q, G.neighborFinset y ⊆ insert q (insert f (insert t (P ∪ Q))))
    (hdegF : s ≤ G.degree f)
    (hNbrF : G.neighborFinset f ⊆ insert t (P ∪ Q)) : False := by
  obtain ⟨b,hcb,hbq⟩ := hcmeet
  have hcq₂ : G.dist c q = 2 := two_edges hcb hbq hcqne hcq
  have no_tQ : ∀ y ∈ Q, ¬ G.Adj t y := by
    intro y hy hty
    have hcy : G.dist c y = 2 :=
      two_edges hct hty (fun e => hcQ (e ▸ hy)) (hqQ y hy).2.1
    have hyP : y ∉ P := fun hyP => Finset.disjoint_left.mp hPQ hyP hy
    have hsub : ∀ x ∈ insert y (insert z (insert q P)), G.dist c x = 2 := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hcy
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hcz
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hcq₂
      exact two_edges hcp (hpP x hx).1 (fun e => hcP (e ▸ hx)) (hpP x hx).2
    have hc := cap_on s cap _ hsub
    have hz : z ∉ insert q P := fun h => (Finset.mem_insert.mp h).elim hqz.symm hzP
    have hy' : y ∉ insert z (insert q P) := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun e => hzQ (e ▸ hy), fun e => (G.ne_of_adj (hqQ y hy).1) e.symm, hyP⟩
    rw [Finset.card_insert_of_notMem hy', Finset.card_insert_of_notMem hz,
      Finset.card_insert_of_notMem hqP, hP] at hc
    omega
  have sees_P (y : V) (hy : y ∈ Q) : ∃ x ∈ P, G.Adj y x := by
    by_contra! hn
    have hsub : G.neighborFinset y ⊆ insert q (insert f (Q.erase y)) := by
      intro x hx
      have had := (G.mem_neighborFinset y x).mp hx
      rcases Finset.mem_insert.mp (hNbrQ y hy hx) with rfl | hx
      · simp
      rcases Finset.mem_insert.mp hx with rfl | hx
      · simp
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact (no_tQ y hy had.symm).elim
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (hn x hx had).elim
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨(G.ne_of_adj had).symm,hx⟩))
    have hnq := Finset.card_le_card hsub
    have hd := hdegQ y hy
    rw [← G.card_neighborFinset_eq_degree] at hd
    have h₁ := Finset.card_insert_le q (insert f (Q.erase y))
    have h₂ := Finset.card_insert_le f (Q.erase y)
    rw [Finset.card_erase_of_mem hy,hQ] at h₂
    omega
  have f_sees_P : ∃ x ∈ P, G.Adj f x := by
    by_contra! hn
    have hsub : G.neighborFinset f ⊆ insert t Q := by
      intro x hx
      rcases Finset.mem_insert.mp (hNbrF hx) with rfl | hx
      · simp
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (hn x hx ((G.mem_neighborFinset f x).mp ‹x ∈ G.neighborFinset f›)).elim
      exact Finset.mem_insert_of_mem hx
    have hnq := Finset.card_le_card hsub
    have hd := hdegF
    rw [← G.card_neighborFinset_eq_degree] at hd
    have h₁ := Finset.card_insert_le t Q
    omega
  obtain ⟨x,hx,hfx⟩ := f_sees_P
  have hpf₂ : G.dist p f = 2 := two_edges (hpP x hx).1 hfx.symm hpfne hpf
  have hsub : ∀ y ∈ insert f (insert a (insert z Q)), G.dist p y = 2 := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hpf₂
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hpa
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hpz
    obtain ⟨r,hr,hyr⟩ := sees_P y hy
    exact two_edges (hpP r hr).1 hyr.symm (fun e => hpQ (e ▸ hy)) (hqQ y hy).2.2
  have hc := cap_on s cap _ hsub
  have ha : a ∉ insert z Q := fun h => (Finset.mem_insert.mp h).elim haz haQ
  have hf : f ∉ insert a (insert z Q) := by simp [hfa,hfz,hfQ]
  rw [Finset.card_insert_of_notMem hf, Finset.card_insert_of_notMem ha,
    Finset.card_insert_of_notMem hzQ, hQ] at hc
  omega

omit [Fintype V] in
/-- With two anchor-visible remote sets each of size at most (s-1), a union
of size at least (2s-3) has overlap at most one. In the one-overlap case
both exclusive parts have size exactly (s-2). -/
theorem exclusive_counts (s : ℕ) (A B : Finset V)
    (ha : A.card + 1 ≤ s) (hb : B.card + 1 ≤ s)
    (hsize : 2*s-3 ≤ (A ∪ B).card) :
    (A ∩ B).card ≤ 1 ∧
      ((A ∩ B).card = 1 → (A \ B).card = s-2 ∧ (B \ A).card = s-2) := by
  have h := Finset.card_union_add_card_inter A B
  have h₁ := Finset.card_sdiff_add_card_inter A B
  have h₂ := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at h₂
  omega

omit [Fintype V] [DecidableRel G.Adj] in
/-- If the ordinary possible neighbors fit into (s-2) slots, degree (s)
forces at least two of the three exceptional neighbors. -/
theorem two_of_three {s : ℕ} (N D : Finset V) (p q t : V)
    (hD : D.card + 2 ≤ s) (hN : s ≤ N.card)
    (hsub : N ⊆ insert p (insert q (insert t D))) :
    (p ∈ N ∧ q ∈ N) ∨ (p ∈ N ∧ t ∈ N) ∨ (q ∈ N ∧ t ∈ N) := by
  classical
  have one (x : V) (hx : N ⊆ insert x D) : False := by
    have h₁ := Finset.card_le_card hx
    have h₂ := Finset.card_insert_le x D
    omega
  by_cases hp : p ∈ N <;> by_cases hq : q ∈ N <;> by_cases ht : t ∈ N
  all_goals first
    | exact Or.inl ⟨hp,hq⟩
    | exact Or.inr (Or.inl ⟨hp,ht⟩)
    | exact Or.inr (Or.inr ⟨hq,ht⟩)
    | exact (one p (fun x hx => by have hs := hsub hx; simp only [Finset.mem_insert] at hs ⊢; grind)).elim
    | exact (one q (fun x hx => by have hs := hsub hx; simp only [Finset.mem_insert] at hs ⊢; grind)).elim

/-- The complete hard count for the one-miss, one-far-vertex layer layout.
The sets P and Q are exclusive remotes and T is the common visible part.
The common middle vertex c has ordinary neighbors only in D, with s-2 slots. -/
theorem large_remote_layer_impossible (s : ℕ) (hs : 4 ≤ s)
    (cap : ∀ x : V, (Finset.univ.filter (fun y => G.dist x y = 2)).card ≤ s)
    (P Q T D : Finset V)
    (hPcap : P.card + T.card + 1 ≤ s) (hQcap : Q.card + T.card + 1 ≤ s)
    (hlarge : 2*s-3 ≤ P.card+Q.card+T.card) (hD : D.card + 2 ≤ s)
    (hPQ : Disjoint P Q) (hPT : Disjoint P T) (hQT : Disjoint Q T)
    (z a b c p q f : V)
    (hzP : z ∉ P) (hzQ : z ∉ Q) (haQ : a ∉ Q) (hbP : b ∉ P)
    (hfP : f ∉ P) (hfQ : f ∉ Q) (hcP : c ∉ P) (hcQ : c ∉ Q)
    (hpQ : p ∉ Q) (hqP : q ∉ P)
    (hpzNe : p ≠ z) (hqzNe : q ≠ z) (haz : a ≠ z) (hbz : b ≠ z)
    (hfz : f ≠ z) (hfa : f ≠ a) (hfb : f ≠ b)
    (hcpNe : c ≠ p) (hcqNe : c ≠ q) (hpfNe : p ≠ f) (hqfNe : q ≠ f)
    (hcz : G.dist c z = 2) (hpz : G.dist p z = 2) (hqz : G.dist q z = 2)
    (hpa : G.dist p a = 2) (hqb : G.dist q b = 2)
    (hpm : ∃ u, G.Adj c u ∧ G.Adj u p) (hqm : ∃ u, G.Adj c u ∧ G.Adj u q)
    (hpf : ¬ G.Adj p f) (hqf : ¬ G.Adj q f)
    (hP : ∀ x ∈ P, G.Adj p x ∧ ¬ G.Adj c x ∧ ¬ G.Adj q x)
    (hQ : ∀ x ∈ Q, G.Adj q x ∧ ¬ G.Adj c x ∧ ¬ G.Adj p x)
    (hdegC : s ≤ G.degree c)
    (hNbrC : G.neighborFinset c ⊆ insert p (insert q (D ∪ T)))
    (hdegP : ∀ x ∈ P, s ≤ G.degree x) (hdegQ : ∀ x ∈ Q, s ≤ G.degree x)
    (hNbrP : ∀ x ∈ P, G.neighborFinset x ⊆ insert p (insert f (T ∪ (P ∪ Q))))
    (hNbrQ : ∀ x ∈ Q, G.neighborFinset x ⊆ insert q (insert f (T ∪ (P ∪ Q))))
    (hdegF : s ≤ G.degree f)
    (hNbrF : G.neighborFinset f ⊆ T ∪ (P ∪ Q)) : False := by
  classical
  have hT : T.card ≤ 1 := by omega
  have hcN : s ≤ (G.neighborFinset c).card := by simpa using hdegC
  have hP' (x : V) (hx : x ∈ P) : G.Adj p x ∧ ¬ G.Adj c x := ⟨(hP x hx).1,(hP x hx).2.1⟩
  have hQ' (x : V) (hx : x ∈ Q) : G.Adj q x ∧ ¬ G.Adj c x := ⟨(hQ x hx).1,(hQ x hx).2.1⟩
  by_cases hTe : T = ∅
  · have hsub : G.neighborFinset c ⊆ insert p (insert q (insert c D)) := by
      intro x hx
      have h := hNbrC hx
      simp only [hTe, Finset.union_empty,Finset.mem_insert] at h ⊢
      tauto
    have hcc : c ∉ G.neighborFinset c := by simp
    have hboth := two_of_three (G.neighborFinset c) D p q c hD hcN hsub
    obtain ⟨hp,hq⟩ := hboth.resolve_right (by tauto)
    have hz : T.card = 0 := by simp [hTe]
    exact empty_overlap_impossible s hs cap P Q (by omega) (by omega) (by omega) hPQ
      hzP hzQ hcP hcQ ((G.mem_neighborFinset c p).1 hp) ((G.mem_neighborFinset c q).1 hq)
      hcz hP' hQ'
  · have hTc : T.card = 1 := by
      have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hTe)
      omega
    obtain ⟨t, rfl⟩ := Finset.card_eq_one.mp hTc
    have htP : t ∉ P := fun h => Finset.disjoint_left.mp hPT h (by simp)
    have htQ : t ∉ Q := fun h => Finset.disjoint_left.mp hQT h (by simp)
    have hPc : P.card = s-2 := by omega
    have hQc : Q.card = s-2 := by omega
    have hsub : G.neighborFinset c ⊆ insert p (insert q (insert t D)) := by
      intro x hx
      have h := hNbrC hx
      simp only [Finset.mem_union,Finset.mem_singleton,Finset.mem_insert] at h ⊢
      tauto
    have hOne := two_of_three (G.neighborFinset c) D p q t hD hcN hsub
    have noBoth (hp : G.Adj c p) (hq : G.Adj c q) : False :=
      shared_excessive s hs cap P Q hPc hQc hPQ hzP hzQ hcP hcQ hp hq hcz hP' hQ'
    simp only [G.mem_neighborFinset] at hOne
    rcases hOne with ⟨hp,hq⟩ | ⟨hp,ht⟩ | ⟨hq,ht⟩
    · exact noBoth hp hq
    · exact single_overlap_direction_impossible s hs cap P Q hPc hQc hPQ z a c p q t f
        hqP hzP hzQ haQ hfQ htP htQ hcP hcQ hpQ hqzNe haz hfz hfa hcqNe hpfNe
        hcz hpz hpa hp (fun hq => noBoth hp hq) hqm ht hpf hP' hQ hdegQ
        (by simpa only [Finset.singleton_union] using hNbrQ) hdegF
        (by simpa only [Finset.singleton_union] using hNbrF)
    · exact single_overlap_direction_impossible s hs cap Q P hQc hPc hPQ.symm z b c q p t f
        hpQ hzQ hzP hbP hfP htQ htP hcQ hcP hqP hpzNe hbz hfz hfb hcpNe hqfNe
        hcz hqz hqb hq (fun hp => noBoth hp hq) hpm ht hqf hQ' hP hdegP
        (by simpa only [Finset.singleton_union, Finset.union_comm P Q] using hNbrP) hdegF
        (by simpa only [Finset.singleton_union, Finset.union_comm P Q] using hNbrF)

#print axioms large_remote_layer_impossible
#print axioms exclusive_counts
#print axioms two_of_three
#print axioms empty_overlap_impossible
#print axioms single_overlap_direction_impossible
end Graph189EccFour
