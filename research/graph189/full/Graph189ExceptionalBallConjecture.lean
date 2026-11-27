import Graph189ExceptionalBall
import Graph189DegreeTwoOuter

namespace Graph189ExceptionalBall

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Under the even-distance hypothesis of Conjecture 189, an exceptional
vertex below the second-smallest degree cuts no radius-two ball. -/
theorem conjecture_low_vertex_cuts_no_ball (hc : G.Connected) {z : V}
    (hlow : G.degree z < G.secondSmallestDegree)
    (hcap : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree) (c : V) :
    (G.induce {x | G.dist c x ≤ 2 ∧ x ≠ z}).Connected := by
  refine all_balls_connected_after_deleting_low hc ?_ hlow
    (Graph189DegreeTwoOuter.distance_two_cap _ hcap z) c
  intro v hv
  exact (Graph189Bipartite.degree_pair (G := G) v z hv).resolve_right (not_le.mpr hlow)

end Graph189ExceptionalBall

#print axioms Graph189ExceptionalBall.conjecture_low_vertex_cuts_no_ball
