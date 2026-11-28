import Graph189TriangleOddCycle
import Graph189ShortestOdd

namespace Graph189TriangleTransversal

open SimpleGraph

/-- A nonbipartite graph has an odd closed walk, also for disconnected graphs. -/
private theorem odd_closed_of_nonbipartite {W : Type*} (H : SimpleGraph W)
    (hn : ¬H.IsBipartite) : ∃ a : W, ∃ p : H.Walk a a, p.length % 2 = 1 := by
  classical
  by_contra! none
  have reps (c : H.ConnectedComponent) : ∃ w, H.connectedComponentMk w = c := by
    induction c using ConnectedComponent.ind with
    | h w => exact ⟨w, rfl⟩
  let root (c : H.ConnectedComponent) := Classical.choose (reps c)
  have reach (v : W) : H.Reachable (root (H.connectedComponentMk v)) v :=
    ConnectedComponent.exact (Classical.choose_spec (reps _))
  let col (v : W) : Fin 2 := ⟨H.dist (root (H.connectedComponentMk v)) v % 2, by omega⟩
  apply hn
  refine ⟨Coloring.mk col ?_⟩
  intro x y hxy hc
  have hr : root (H.connectedComponentMk x) = root (H.connectedComponentMk y) :=
    congrArg root (ConnectedComponent.sound hxy.reachable)
  have hreach : H.Reachable (root (H.connectedComponentMk x)) y := hr.symm ▸ reach y
  obtain ⟨p,hp⟩ := (reach x).exists_walk_length_eq_dist
  obtain ⟨q,hq⟩ := hreach.exists_walk_length_eq_dist
  have h := none _ ((p.concat hxy).append q.reverse)
  rw [Walk.length_append, Walk.length_concat, Walk.length_reverse, hp, hq] at h
  have he : H.dist (root (H.connectedComponentMk x)) x % 2 =
      H.dist (root (H.connectedComponentMk y)) y % 2 := congrArg Fin.val hc
  rw [← hr] at he
  omega

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Removing a triangle transversal of size at most (k−3)/3 makes the graph
bipartite when at most one vertex falls below degree k and second neighborhoods
have size at most k. No connectivity of the induced graph is required. -/
theorem induce_bipartite_of_two_cap (X : Finset V) {k : ℕ} (ht : MeetsEveryTriangle G X)
    (cap : ∀ a, (Finset.univ.filter (fun u => G.dist a u = 2)).card ≤ k)
    (hk : 3*X.card+3 ≤ k) (pair : ∀ u v : V, u ≠ v → k ≤ G.degree u ∨ k ≤ G.degree v) :
    (G.induce {v | v ∉ X}).IsBipartite := by
  classical
  let H := G.induce {v | v ∉ X}
  change H.IsBipartite
  by_contra hn
  obtain ⟨a,p,hodd⟩ := odd_closed_of_nonbipartite H hn
  let P (n : ℕ) := ∃ a, ∃ p : H.Walk a a, p.length = n ∧ p.length % 2 = 1
  have hP : ∃ n, P n := ⟨p.length,a,p,rfl,hodd⟩
  obtain ⟨b,w,hlen,hwo⟩ := Nat.find_spec hP
  have minimal (c) (v : H.Walk c c) (ho : v.length % 2 = 1) : w.length ≤ v.length :=
    hlen.symm ▸ Nat.find_min' hP ⟨c,v,rfl,ho⟩
  have inj := Graph189ShortestOdd.shortest_index_injective w hwo minimal
  have triH : ∀ {i j l}, H.Adj i j → H.Adj j l → ¬H.Adj i l := by
    intro i j l hij hjl
    exact ht i.property j.property l.property hij hjl
  have size := Graph189ShortestOdd.odd_ge_five w hwo triH
  let m := w.length / 2
  have len : 2*m+1 = w.length := by dsimp [m]; omega
  let f (i : ℕ) : V := (w.getVert i).val
  have outs (i : ℕ) (_ : i ≤ 2*m) : f i ∉ X := (w.getVert i).property
  have edg (i : ℕ) (hi : i < 2*m) : G.Adj (f i) (f (i+1)) :=
    w.adj_getVert_succ (by omega : i < w.length)
  have last : G.Adj (f (2*m)) (f 0) := by
    have e := w.adj_getVert_succ (i := 2*m) (by omega)
    rw [len, Walk.getVert_length] at e
    change H.Adj (w.getVert (2*m)) (w.getVert 0)
    rw [Walk.getVert_zero]
    exact e
  have exq : ∃ q ≤ 2*m, ∀ i ≤ 2*m, i ≠ q → k ≤ G.degree (f i) := by
    by_cases low : ∃ q ≤ 2*m, G.degree (f q) < k
    · obtain ⟨q,hq,hlo⟩ := low
      refine ⟨q,hq,?_⟩
      intro i hi hne
      have distinct : f i ≠ f q := by
        intro he
        have hsub : w.getVert i = w.getVert q := Subtype.ext he
        have hfin := @inj ⟨i,by omega⟩ ⟨q,by omega⟩ hsub
        exact hne (congrArg Fin.val hfin)
      exact (pair (f i) (f q) distinct).resolve_right (by omega)
    · exact ⟨0, by omega, fun i hi _ => Nat.le_of_not_gt (fun hl => low ⟨i,hi,hl⟩)⟩
  obtain ⟨q,hq,high⟩ := exq
  exact no_odd_cycle_one_low G X ht cap hk f (by omega) hq outs high edg last

/-- The conjecture's exact ambient even-distance and degree conditions imply
bipartiteness of the induced graph after deleting a small triangle transversal. -/
theorem induce_bipartite_of_conjecture189 [Nontrivial V] (X : Finset V)
    (ht : MeetsEveryTriangle G X) (hk : 3*X.card+3 ≤ G.secondSmallestDegree)
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G) :
    (G.induce {v | v ∉ X}).IsBipartite := by
  classical
  apply induce_bipartite_of_two_cap G X ht _ hk (Graph189Bipartite.degree_pair (G := G))
  intro a
  let S := Finset.univ.filter (fun u => G.dist a u = 2)
  have nmem : a ∉ S := by simp [S]
  have hsub : insert a S ⊆ Finset.univ.filter (fun u => Even (G.dist a u)) := by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · simp
    · have he := (Finset.mem_filter.mp (show u ∈ S from hu)).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he ▸ (by decide : Even 2)⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem nmem] at hcard
  have bound := (Finset.le_max' _ _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)).trans hσ
  change S.card ≤ _
  change (Finset.univ.filter (fun u => Even (G.dist a u))).card ≤ _ at bound
  omega

end Graph189TriangleTransversal
