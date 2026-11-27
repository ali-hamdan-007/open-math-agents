import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Card
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Degrees

namespace Graph189SaturatedDistance

open SimpleGraph Finset Classical

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- The even-distance count used in Graph Conjecture 189 includes the center. -/
noncomputable def evenBall (a : V) : Finset V :=
  univ.filter (fun v => G.dist a v % 2 = 0)

/-- The local filter counts exactly the vertices in the original statement. -/
theorem evenBall_card_eq_distEven [DecidableEq V] (a : V) :
    (evenBall G a).card = G.distEven a := by
  unfold evenBall SimpleGraph.distEven
  congr 1
  ext v
  simp [Nat.even_iff]

/-- The maximum bound in the original conjecture implies the local cap. -/
theorem evenBall_cap_of_original [DecidableEq V] [Nontrivial V] [DecidableRel G.Adj]
    (hcap : (univ.image (distEven G)).max' (by simp) ≤ 1 + G.secondSmallestDegree)
    (a : V) : (evenBall G a).card ≤ G.secondSmallestDegree + 1 := by
  rw [evenBall_card_eq_distEven, Nat.add_comm]
  exact (le_max' _ _ (mem_image_of_mem _ (mem_univ a))).trans hcap

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

/-- Each remote neighbor of the saturated witness set comes through a gate.
A solo vertex adjacent to every gate reaches the remote in exactly two steps. -/
theorem solo_dist_two_of_saturation {a s m : V} {S gates : Finset V} {k : ℕ}
    (hS : ∀ v ∈ S, G.dist a v = 2) (hcard : S.card = k)
    (hcap : (evenBall G a).card ≤ k + 1)
    (hfar : 3 ≤ G.dist a m) (hnear : G.dist a m ≤ 4)
    (hgate : ∀ u ∈ S, G.Adj u m → u ∈ gates)
    (hsolo : ∀ u ∈ gates, G.Adj s u)
    (hne : s ≠ m) (hnadj : ¬ G.Adj s m) :
    G.dist s m = 2 := by
  obtain ⟨_, u, hu, hum⟩ := exists_predecessor_of_saturation G hS hcard hcap hfar hnear
  let path : G.Walk s m := .cons (hsolo u (hgate u hu hum)) (.cons hum .nil)
  have hlo := path.reachable.one_lt_dist_of_ne_of_not_adj hne hnadj
  have hhi : G.dist s m ≤ 2 := G.dist_le path
  omega

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

/-- Combining gate incidence with the two disjoint witness counts bounds the
remote layer by (2k-4). The stronger additive inequality also rules out the
degenerate cases where natural subtraction truncates. -/
theorem order_bound_of_solo_saturation
    {a s : V} {S gates R N : Finset V} {c k : ℕ}
    (hS : ∀ v ∈ S, G.dist a v = 2) (hcard : S.card = k)
    (hcapA : (evenBall G a).card ≤ k + 1)
    (hfar : ∀ m ∈ R, 3 ≤ G.dist a m) (hnear : ∀ m ∈ R, G.dist a m ≤ 4)
    (hgate : ∀ m ∈ R, ∀ u ∈ S, G.Adj u m → u ∈ gates)
    (hsolo : ∀ u ∈ gates, G.Adj s u)
    (hne : ∀ m ∈ R, s ≠ m) (hnadj : ∀ m ∈ R, ¬ G.Adj s m)
    (hN : ∀ v ∈ N, G.dist s v = 2) (hdis : Disjoint R N)
    (hcapS : (evenBall G s).card ≤ k + 1)
    (hremote : c - k ≤ R.card) (hnonremote : 4 ≤ N.card) :
    c + 4 ≤ 2 * k ∧ c ≤ 2 * k - 4 := by
  have hR (m : V) (hm : m ∈ R) : G.dist s m = 2 :=
    solo_dist_two_of_saturation G hS hcard hcapA (hfar m hm) (hnear m hm)
      (hgate m hm) hsolo (hne m hm) (hnadj m hm)
  have hbound := order_bound_of_solo_witnesses G hR hN hdis hcapS hremote hnonremote
  exact ⟨hbound, by omega⟩

#print axioms evenBall_cap_of_original
#print axioms exists_predecessor_of_saturation
#print axioms solo_dist_two_of_saturation
#print axioms order_bound_of_solo_witnesses
#print axioms order_bound_of_solo_saturation

end Graph189SaturatedDistance
