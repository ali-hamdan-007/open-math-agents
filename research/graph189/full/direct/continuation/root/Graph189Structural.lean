import Graph189NearViaLinked
import Graph189NearFinal

open SimpleGraph Finset Graph189ExteriorDegreeCycle Graph189UniversalCycle
namespace Graph189Structural
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The original graph in the structural range has a Hamiltonian path
under the original even-distance and degree assumptions. -/
theorem traceable (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (hs : 5≤G.vertexConnectivity) (hk : 26≤G.secondSmallestDegree)
    (ratio : 3*G.vertexConnectivity<G.secondSmallestDegree)
    :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  rcases Graph189NearViaLinked.traceable_or_minimum_deletion hc cap hs hk ratio with done|near
  · exact done
  · obtain ⟨z,least,x,y,q,hq⟩ := near
    apply Graph189RootedSplice.traceable_of_near_spanning hc cap _ hs hk ratio z least q hq
    intro v
    have equal : {u : V | u∉({v} : Finset V)} = {u : V | u≠v} := by
      ext u
      simp
    rw [←equal]
    exact Graph189CutSides.connected_after_smaller_deletion (G:=G) ({v} : Finset V)
      (by simp; omega : ({v} : Finset V).card<G.vertexConnectivity)

#print axioms traceable
end Graph189Structural
