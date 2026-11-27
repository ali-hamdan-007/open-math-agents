import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Card

namespace Graph189SaturatedDistance

open SimpleGraph Finset Classical

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- The even-distance count used in Graph Conjecture 189 includes the center. -/
noncomputable def evenBall (a : V) : Finset V :=
  univ.filter (fun v => G.dist a v % 2 = 0)

/-- A center and (k) distance-two vertices consume all (k+1) even-distance slots. -/
theorem evenBall_eq_insert_of_saturation {a : V} {S : Finset V} {k : ℕ}
    (hS : ∀ v ∈ S, G.dist a v = 2) (hcard : S.card = k)
    (hcap : (evenBall G a).card ≤ k + 1) :
    evenBall G a = insert a S := by
  classical
  have ha : a ∉ S := by
    intro h
    simpa using hS a h
  symm
  apply eq_of_subset_of_card_le
  · intro v hv
    rw [mem_insert] at hv
    rcases hv with rfl | hv
    · simp [evenBall]
    · simp [evenBall, hS v hv]
  · simpa [card_insert_of_notMem ha, hcard] using hcap

/-- An outside vertex at distance between three and four from a saturated center
has a geodesic predecessor among the specified distance-two witnesses. -/
theorem exists_predecessor_of_saturation {a m : V} {S : Finset V} {k : ℕ}
    (hS : ∀ v ∈ S, G.dist a v = 2) (hcard : S.card = k)
    (hcap : (evenBall G a).card ≤ k + 1)
    (hfar : 3 ≤ G.dist a m) (hnear : G.dist a m ≤ 4) :
    G.dist a m = 3 ∧ ∃ p ∈ S, G.Adj p m := by
  classical
  have hsaturated := evenBall_eq_insert_of_saturation G hS hcard hcap
  have hthree : G.dist a m = 3 := by
    by_contra hne
    have hfour : G.dist a m = 4 := by omega
    have hm : m ∈ evenBall G a := by simp [evenBall, hfour]
    rw [hsaturated, mem_insert] at hm
    rcases hm with rfl | hm
    · simp at hfour
    · have := hS m hm
      omega
  refine ⟨hthree, ?_⟩
  have hreverse : G.dist m a = 3 := by rwa [dist_comm]
  have hreach : G.Reachable m a := Reachable.of_dist_ne_zero (by omega)
  obtain ⟨walk, hlen⟩ := hreach.exists_walk_length_eq_dist
  cases walk with
  | nil => simp at hthree
  | cons hmp tail =>
    rename_i p
    have hlen' : tail.length = 2 := by
      rw [Walk.length_cons, hreverse] at hlen
      omega
    have hle : G.dist a p ≤ 2 := by
      rw [dist_comm]
      exact hlen' ▸ G.dist_le tail
    have hdiff := hmp.diff_dist_adj (u := a)
    have htwo : G.dist a p = 2 := by omega
    have hp : p ∈ evenBall G a := by simp [evenBall, htwo]
    rw [hsaturated, mem_insert] at hp
    rcases hp with rfl | hp
    · simp at htwo
    · exact ⟨p, hp, hmp.symm⟩

/-- A vertex with disjoint sets of distance-two witnesses uses one slot per
member as well as the slot for itself. -/
theorem card_add_le_of_disjoint_distance_two {s : V} {R N : Finset V} {k : ℕ}
    (hR : ∀ v ∈ R, G.dist s v = 2) (hN : ∀ v ∈ N, G.dist s v = 2)
    (hdis : Disjoint R N) (hcap : (evenBall G s).card ≤ k + 1) :
    R.card + N.card ≤ k := by
  classical
  have hs : s ∉ R ∪ N := by
    simp only [mem_union, not_or]
    exact ⟨fun h => by simpa using hR s h, fun h => by simpa using hN s h⟩
  have hsub : insert s (R ∪ N) ⊆ evenBall G s := by
    intro v hv
    rw [mem_insert, mem_union] at hv
    rcases hv with rfl | h | h
    · simp [evenBall]
    · simp [evenBall, hR v h]
    · simp [evenBall, hN v h]
  have h := card_le_card hsub
  rw [card_insert_of_notMem hs, card_union_of_disjoint hdis] at h
  omega

/-- In the six-port count the remote witnesses number at least (c-k)
and the nonremote witnesses number at least four. -/
theorem order_bound_of_solo_witnesses {s : V} {R N : Finset V} {c k : ℕ}
    (hR : ∀ v ∈ R, G.dist s v = 2) (hN : ∀ v ∈ N, G.dist s v = 2)
    (hdis : Disjoint R N) (hcap : (evenBall G s).card ≤ k + 1)
    (hremote : c - k ≤ R.card) (hnonremote : 4 ≤ N.card) :
    c + 4 ≤ 2 * k := by
  have := card_add_le_of_disjoint_distance_two G hR hN hdis hcap
  omega

#print axioms exists_predecessor_of_saturation
#print axioms order_bound_of_solo_witnesses

end Graph189SaturatedDistance
