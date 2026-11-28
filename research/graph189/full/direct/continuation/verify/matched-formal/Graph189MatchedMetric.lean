import Graph189MatchedWedge
import Graph189R1Metric

open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

namespace Graph189MatchedWedge

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The matched wedge obstruction under the actual Graph 189 hypotheses. -/
theorem wedge_order_graph189 (hc : G.Connected) {x y z : V} (hxy : G.Adj x y)
    (hxz : G.Adj x z) (hyz : y ≠ z)
    (cap : ∀ v, G.distEven v ≤ 1+G.secondSmallestDegree) :
    let k := G.secondSmallestDegree
    ∃ t ε : ℕ, ε ≤ 1 ∧
      t + ε + (G.neighborFinset x ∪ (G.neighborFinset y ∪ G.neighborFinset z)).card ≤
        G.degree x + G.distEven x ∧
      Fintype.card V + (G.neighborFinset x ∪ (G.neighborFinset y ∪ G.neighborFinset z)).card +
        t*(t+1) ≤ 3*k+2 + G.degree y + G.degree z + t*k + ε := by
  dsimp only
  have cap' (v : V) : G.distEven v ≤ G.secondSmallestDegree+1 := by simpa only [Nat.add_comm 1] using cap v
  refine wedge_order_matched hc hxy hxz hyz cap' ?_
  have hdiam := diameter_le_five hc cap
  have hle (a b : V) : G.dist a b ≤ 5 :=
    (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc)).trans hdiam
  have low (a : V) (hdx : 5 ≤ G.dist x a) (hdy : 5 ≤ G.dist y a) :
      G.degree a < G.secondSmallestDegree := by
    have hx5 := le_antisymm (hle x a) hdx
    have hy5 := le_antisymm (hle y a) hdy
    rcases degree_pair (G:=G) x y hxy.ne with hh | hh
    · exact (five_endpoints hc cap' x a hx5).resolve_left (not_lt_of_ge hh)
    · exact (five_endpoints hc cap' y a hy5).resolve_left (not_lt_of_ge hh)
  intro a b ha hb
  by_contra hne
  rcases degree_pair (G:=G) a b hne with h | h
  · exact (not_lt_of_ge h) (low a ha.1 ha.2.1)
  · exact (not_lt_of_ge h) (low b hb.1 hb.2.1)

#print axioms wedge_order_graph189
end Graph189MatchedWedge
