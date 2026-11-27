import Graph199Cut
import Graph199MinimumCut

namespace Graph199
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Deleting any one vertex forces each of the two cut vertices to meet each side. -/
private theorem two_clique_meets (u v : V) (huv : u ≠ v) (A B : Set V)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (houtA : u ∉ A ∧ v ∉ A) (houtB : u ∉ B ∧ v ∉ B)
    (hs : ∀ a ∈ A, ∀ b ∈ B, a ≠ b ∧ ¬ G.Adj a b)
    (hcover : ∀ x, x ≠ u → x ≠ v → x ∈ A ∨ x ∈ B)
    (hκ : 2 ≤ vertexConnectivity G) : ∃ a ∈ A, G.Adj u a := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  let S : Finset V := {u,v}
  have hS : S.card ≤ vertexConnectivity G := by
    change ({u,v} : Finset V).card ≤ _
    rw [card_insert_of_notMem (show u ∉ ({v} : Finset V) from by simpa using huv), card_singleton]
    exact hκ
  have hbA : b ∉ A := fun he => (hs b he b hb).1 rfl
  obtain ⟨x, hx, _, hux⟩ := minCut_adj_side S u (by simp [S]) hS A
    ⟨a, ha, by simpa [S] using (show a ≠ u ∧ a ≠ v from
      ⟨fun e => houtA.1 (e ▸ ha), fun e => houtA.2 (e ▸ ha)⟩)⟩
    ⟨b, hbA, by simpa [S] using (show b ≠ u ∧ b ≠ v from
      ⟨fun e => houtB.1 (e ▸ hb), fun e => houtB.2 (e ▸ hb)⟩)⟩ (by
        intro x hx y hy _ hyS
        have hy' : y ≠ u ∧ y ≠ v := by simpa [S] using hyS
        exact (hs x hx y ((hcover y hy'.1 hy'.2).resolve_left hy)).2)
  exact ⟨x, hx, hux⟩

private theorem two_clique_middle_attachments (u v : V) (A B : Set V)
    (houtB : u ∉ B ∧ v ∉ B)
    (hs : ∀ a ∈ A, ∀ b ∈ B, a ≠ b ∧ ¬ G.Adj a b)
    (hcover : ∀ x, x ≠ u → x ≠ v → x ∈ A ∨ x ∈ B)
    (hκ : 2 ≤ vertexConnectivity G)
    (hu : ∃ b ∈ B, G.Adj u b) (hv : ∃ b ∈ B, G.Adj v b) :
    ∃ b c, b ∈ B ∧ c ∈ B ∧ G.Adj u b ∧ G.Adj v c ∧ (b ≠ c ∨ B = {b}) := by
  obtain ⟨b, hb, hub⟩ := hu
  obtain ⟨c, hc, hvc⟩ := hv
  by_cases hne : b ≠ c
  · exact ⟨b,c,hb,hc,hub,hvc,Or.inl hne⟩
  have he : b = c := by simpa using hne
  subst c
  by_cases hB : B = {b}
  · exact ⟨b,b,hb,hb,hub,hvc,Or.inr hB⟩
  by_contra hn
  have hou (x : V) (hx : x ∈ B) (hxb : x ≠ b) : ¬ G.Adj u x :=
    fun h => hn ⟨x,b,hx,hb,h,hvc,Or.inl hxb⟩
  have hov (x : V) (hx : x ∈ B) (hxb : x ≠ b) : ¬ G.Adj v x :=
    fun h => hn ⟨b,x,hb,hx,hub,h,Or.inl hxb.symm⟩
  have hG : (G.induce ({b} : Set V)ᶜ).Connected := by
    have h := connected_of_card_lt_vertexConnectivity (G := G) ({b} : Finset V)
      (by simpa using Nat.lt_of_lt_of_le (by decide : 1 < 2) hκ)
    rwa [coe_singleton] at h
  let W := ↥(({b} : Set V)ᶜ)
  classical
  let T : Finset W := univ.filter fun x => x.val ∈ B
  have hT : T.Nonempty := by
    have hbad : ∃ x ∈ B, x ≠ b := by
      by_contra! h
      exact hB (Set.Subset.antisymm (fun x hx => Set.mem_singleton_iff.mpr (h x hx))
        (Set.singleton_subset_iff.mpr hb))
    obtain ⟨x,hx,hxb⟩ := hbad
    exact ⟨⟨x, fun he => hxb (Set.mem_singleton_iff.mp he)⟩, mem_filter.mpr ⟨mem_univ _, hx⟩⟩
  have hTu : T ≠ univ := by
    intro he
    let z : W := ⟨u, fun h => houtB.1 ((Set.mem_singleton_iff.mp h).symm ▸ hb)⟩
    have h : z ∈ T := he ▸ mem_univ z
    exact houtB.1 (mem_filter.mp h).2
  obtain ⟨y, hy, x, hx, hyx⟩ := hG.exists_adj_finset_compl hT hTu
  have hxB : x.val ∈ B := (mem_filter.mp hx).2
  have hxb : x.val ≠ b := fun h => x.property (Set.mem_singleton_iff.mpr h)
  have hyB : y.val ∉ B := fun h => hy (mem_filter.mpr ⟨mem_univ _, h⟩)
  have hxy : G.Adj y.val x.val := induce_adj.mp hyx
  by_cases hyu : y.val = u
  · exact hou x.val hxB hxb (hyu ▸ hxy)
  by_cases hyv : y.val = v
  · exact hov x.val hxB hxb (hyv ▸ hxy)
  exact (hs _ ((hcover y.val hyu hyv).resolve_right hyB) _ hxB).2 hxy


omit [Fintype V] [DecidableEq V] in
private theorem chain_of_clique (A : Set V)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → G.Adj x y)
    (L : List V) (hn : L.Nodup) (hmem : ∀ x ∈ L, x ∈ A) : L.IsChain G.Adj := by
  apply List.Pairwise.isChain
  apply List.pairwise_iff_get.mpr
  intro i j hij
  exact hA _ (hmem _ (List.get_mem _ _)) _ (hmem _ (List.get_mem _ _))
    (List.pairwise_iff_get.mp hn i j hij)

/-- A two-vertex cut with two separated clique components yields a Hamiltonian path
when deleting any single vertex preserves connectivity. -/
theorem hamiltonian_of_two_clique_components (u v : V) (huv : u ≠ v) (A B : Set V)
    (hAn : A.Nonempty) (hBn : B.Nonempty)
    (houtA : u ∉ A ∧ v ∉ A) (houtB : u ∉ B ∧ v ∉ B)
    (hs : ∀ a ∈ A, ∀ b ∈ B, a ≠ b ∧ ¬ G.Adj a b)
    (hcover : ∀ x, x ≠ u → x ≠ v → x ∈ A ∨ x ∈ B)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → G.Adj x y)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → G.Adj x y)
    (hκ : 2 ≤ vertexConnectivity G) :
    ∃ s t : V, ∃ p : G.Walk s t, p.IsHamiltonian := by
  classical
  have hs' : ∀ b ∈ B, ∀ a ∈ A, b ≠ a ∧ ¬ G.Adj b a :=
    fun b hb a ha => ⟨(hs a ha b hb).1.symm, fun h => (hs a ha b hb).2 h.symm⟩
  obtain ⟨a, ha, hua⟩ := two_clique_meets u v huv A B hAn hBn houtA houtB hs hcover hκ
  have hub := two_clique_meets u v huv B A hBn hAn houtB houtA hs'
    (fun x hx hy => (hcover x hx hy).symm) hκ
  have hvb := two_clique_meets v u huv.symm B A hBn hAn houtB.symm houtA.symm hs'
    (fun x hx hy => (hcover x hy hx).symm) hκ
  obtain ⟨b, c, hb, hc, hub, hvc, hbc⟩ :=
    two_clique_middle_attachments u v A B houtB hs hcover hκ hub hvb
  let L := (A.toFinset.erase a).toList ++ [a]
  have hLn : L.Nodup := by
    refine List.nodup_append.mpr ⟨nodup_toList _, by simp, ?_⟩
    intro x hx y hy
    have hya : y = a := by simpa using hy
    subst y
    exact (mem_erase.mp (mem_toList.mp hx)).1
  have hLm (x : V) : x ∈ L ↔ x ∈ A := by
    by_cases hx : x = a <;> simp [L, hx, ha]
  have hLl : L.getLast? = some a := by simp [L]
  have hM : ∃ M : List V, M.Nodup ∧ (∀ x, x ∈ M ↔ x ∈ B) ∧
      M.head? = some b ∧ M.getLast? = some c := by
    rcases hbc with hn | hs
    · let M := b :: ((B.toFinset.erase b |>.erase c).toList ++ [c])
      refine ⟨M, ?_, ?_, by simp [M], ?_⟩
      · apply List.nodup_cons.mpr
        refine ⟨by simp [hn], List.nodup_append.mpr ⟨nodup_toList _, by simp, ?_⟩⟩
        intro x hx y hy
        have hyc : y = c := by simpa using hy
        subst y
        exact (mem_erase.mp (mem_toList.mp hx)).1
      · intro x
        by_cases hxb : x = b
        · simp [M, hxb, hb]
        by_cases hxc : x = c
        · simp [M, hxc, hc]
        · simp [M, hxb, hxc]
      · change ((b :: ((B.toFinset.erase b).erase c).toList) ++ [c]).getLast? = some c
        simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or]
    · have he : c = b := Set.mem_singleton_iff.mp (hs ▸ hc)
      subst c
      exact ⟨[b], by simp, by intro x; simp [hs], by simp, by simp⟩
  obtain ⟨M, hMn, hMm, hMh, hMl⟩ := hM
  let W := L ++ u :: (M ++ [v])
  have hlast : (M ++ [v]).IsChain G.Adj := by
    apply (chain_of_clique B hB M hMn (fun x hx => (hMm x).mp hx)).append
      (List.IsChain.singleton v)
    intro x hx y hy
    have hx' : c = x := by simpa [hMl] using hx
    have hy' : v = y := by simpa using hy
    subst x
    subst y
    exact hvc.symm
  have hmid : (u :: (M ++ [v])).IsChain G.Adj := by
    apply hlast.cons
    intro x hx
    have hMne : M ≠ [] := by
      intro he
      simp [he] at hMh
    rw [List.head?_append_of_ne_nil _ hMne, hMh] at hx
    have he : b = x := by simpa using hx
    exact he ▸ hub
  have hWc : W.IsChain G.Adj := by
    apply (chain_of_clique A hA L hLn (fun x hx => (hLm x).mp hx)).append hmid
    intro x hx y hy
    have he : a = x := by simpa [hLl] using hx
    have he' : u = y := by simpa using hy
    subst x
    subst y
    exact hua.symm
  have huM : u ∉ M := fun h => houtB.1 ((hMm u).mp h)
  have hvM : v ∉ M := fun h => houtB.2 ((hMm v).mp h)
  have hWn : W.Nodup := by
    refine List.nodup_append.mpr ⟨hLn, ?_, ?_⟩
    · apply List.nodup_cons.mpr
      refine ⟨by simp [huv, huM], List.nodup_append.mpr ⟨hMn, by simp, ?_⟩⟩
      intro x hx y hy
      have hyv : y = v := by simpa using hy
      subst y
      exact fun he => hvM (he ▸ hx)
    · intro x hx y hy
      have hxA := (hLm x).mp hx
      rcases List.mem_cons.mp hy with rfl | hy
      · exact fun he => houtA.1 (he ▸ hxA)
      rcases List.mem_append.mp hy with hy | hy
      · exact (hs x hxA y ((hMm y).mp hy)).1
      · have he : y = v := by simpa using hy
        exact fun h => houtA.2 ((h.trans he) ▸ hxA)
  have hWm (x : V) : x ∈ W := by
    by_cases hu : x = u
    · simp [W, hu]
    by_cases hv : x = v
    · simp [W, hv]
    rcases hcover x hu hv with h | h
    · exact List.mem_append_left _ ((hLm x).mpr h)
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ ((hMm x).mpr h)))
  have hWe : W ≠ [] := List.ne_nil_of_mem (hWm u)
  let p := Walk.ofSupport W hWe hWc
  have hp : p.support = W := Walk.support_ofSupport hWe hWc
  have hpath : p.IsPath := by
    apply Walk.IsPath.mk'
    rwa [hp]
  exact ⟨_, _, p, hpath.isHamiltonian_of_mem (fun x => by rw [hp]; exact hWm x)⟩

#print axioms hamiltonian_of_two_clique_components
end Graph199
