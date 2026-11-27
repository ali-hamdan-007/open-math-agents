import Graph199Block

namespace Graph199
open Finset SimpleGraph

private theorem chain_of_clique_list {V : Type*} {G : SimpleGraph V}
    {S : Set V} (hc : G.IsClique S) {L : List V} (hn : L.Nodup)
    (hm : ∀ x ∈ L, x ∈ S) : L.IsChain G.Adj := by
  apply List.Pairwise.isChain
  apply List.pairwise_iff_get.mpr
  intro i j hij
  exact hc (hm _ (List.get_mem _ _)) (hm _ (List.get_mem _ _))
    (List.pairwise_iff_get.mp hn i j hij)

/-- Enumerate a clique as a path ending at the prescribed vertex. -/
theorem clique_list_ending {V : Type*} [Fintype V] {G : SimpleGraph V}
    {S : Set V} {x : V} (hx : x ∈ S) (hc : G.IsClique S) :
    ∃ L : List V, L.getLast? = some x ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      (∀ y, y ∈ L ↔ y ∈ S) := by
  classical
  let L := (S.toFinset.erase x).toList ++ [x]
  have hm (y : V) : y ∈ L ↔ y ∈ S := by
    by_cases h : y = x <;> simp [L, h, hx]
  have hn : L.Nodup := by
    refine List.nodup_append.mpr ⟨nodup_toList _, by simp, ?_⟩
    rintro a ha b hb rfl
    have hax : a = x := by simpa using hb
    exact (mem_erase.mp (mem_toList.mp ha)).1 hax
  exact ⟨L, by simp [L], hn, chain_of_clique_list hc hn (fun y hy => (hm y).mp hy), hm⟩

/-- Enumerate a clique as a path starting at the prescribed vertex. -/
theorem clique_list_starting {V : Type*} [Fintype V] {G : SimpleGraph V}
    {S : Set V} {x : V} (hx : x ∈ S) (hc : G.IsClique S) :
    ∃ L : List V, L.head? = some x ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      (∀ y, y ∈ L ↔ y ∈ S) := by
  obtain ⟨L, hlast, hn, _, hm⟩ := clique_list_ending hx hc
  have hnr : L.reverse.Nodup := List.nodup_reverse.mpr hn
  have hmr (y : V) : y ∈ L.reverse ↔ y ∈ S := by simpa using hm y
  exact ⟨L.reverse, by simpa [List.head?_reverse] using hlast, hnr,
    chain_of_clique_list hc hnr (fun y hy => (hmr y).mp hy), hmr⟩

/-- Join two outside vertices through a nonempty clique to which both are complete. -/
theorem clique_bridge {V : Type*} [Fintype V] {G : SimpleGraph V}
    (w v : V) {B : Set V} (hwv : w ≠ v) (hw : w ∉ B) (hv : v ∉ B)
    (hB : B.Nonempty) (hc : G.IsClique B)
    (hwb : ∀ b ∈ B, G.Adj w b) (hvb : ∀ b ∈ B, G.Adj v b) :
    ∃ L : List V, L.head? = some w ∧ L.getLast? = some v ∧ L.Nodup ∧
      L.IsChain G.Adj ∧ (∀ x, x ∈ L ↔ x ∈ insert w (insert v B)) := by
  obtain ⟨b, hb⟩ := hB
  obtain ⟨M, hlast, hn, hmc, hm⟩ := clique_list_ending hb hc
  have hMe : M ≠ [] := by
    intro h
    simp [h] at hlast
  have hMV : (M ++ [v]).IsChain G.Adj := by
    apply hmc.append (List.IsChain.singleton v)
    intro x hx y hy
    have hbx : b = x := by simpa [hlast] using hx
    have hvy : v = y := by simpa using hy
    exact hbx ▸ hvy ▸ (hvb b hb).symm
  refine ⟨w :: (M ++ [v]), by simp, ?_, ?_, hMV.cons ?_, ?_⟩
  · change ((w :: M) ++ [v]).getLast? = some v
    rw [List.getLast?_append, List.getLast?_singleton, Option.some_or]
  · refine List.nodup_cons.mpr ⟨?_, List.nodup_append.mpr ⟨hn, by simp, ?_⟩⟩
    · intro h
      rcases List.mem_append.mp h with h | h
      · exact hw ((hm w).mp h)
      · exact hwv (List.mem_singleton.mp h)
    · rintro x hx y hy rfl
      have hxv : x = v := List.mem_singleton.mp hy
      exact hv (hxv ▸ (hm x).mp hx)
  · intro x hx
    rw [List.head?_append_of_ne_nil _ hMe] at hx
    exact hwb x ((hm x).mp (List.mem_of_mem_head? hx))
  · intro x
    simp [hm]
    tauto

/-- Start with a clique ending at a prescribed neighbour of w, then traverse
the clique bridge from w to v. -/
theorem clique_prefix_bridge {V : Type*} [Fintype V] {G : SimpleGraph V}
    (w v : V) {B : Set V} (hwv : w ≠ v) (hw : w ∉ B) (hv : v ∉ B)
    (hB : B.Nonempty) (hc : G.IsClique B)
    (hwb : ∀ b ∈ B, G.Adj w b) (hvb : ∀ b ∈ B, G.Adj v b)
    {T : Set V} {x : V} (hx : x ∈ T) (hTc : G.IsClique T)
    (hTw : w ∉ T) (hTv : v ∉ T) (hTB : Disjoint T B) (hxw : G.Adj x w) :
    ∃ L : List V, L ≠ [] ∧ L.getLast? = some v ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      (∀ y, y ∈ L ↔ y ∈ T ∪ insert w (insert v B)) := by
  obtain ⟨M, hlast, hMn, hMc, hMm⟩ := clique_list_ending hx hTc
  obtain ⟨N, hNhead, hNtail, hNn, hNc, hNm⟩ := clique_bridge w v hwv hw hv hB hc hwb hvb
  have hlast' : (M ++ N).getLast? = some v := by simp [hNtail]
  refine ⟨M ++ N, ?_, hlast', ?_, ?_, ?_⟩
  · exact List.ne_nil_of_mem (List.mem_of_mem_getLast? hlast')
  · refine List.nodup_append.mpr ⟨hMn, hNn, ?_⟩
    rintro a ha b hb rfl
    have haT := (hMm a).mp ha
    have haB := (hNm a).mp hb
    simp only [Set.mem_insert_iff] at haB
    rcases haB with rfl | rfl | h
    · exact hTw haT
    · exact hTv haT
    · exact Set.disjoint_left.mp hTB haT h
  · apply hMc.append hNc
    intro a ha b hb
    have hxa : x = a := by simpa [hlast] using ha
    have hwb' : w = b := by simpa [hNhead] using hb
    exact hxa ▸ hwb' ▸ hxw
  · intro y
    simp [hMm, hNm]
    tauto

#print axioms clique_list_ending
#print axioms clique_list_starting
#print axioms clique_bridge
#print axioms clique_prefix_bridge
end Graph199
