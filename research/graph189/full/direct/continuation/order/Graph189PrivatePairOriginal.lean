import Graph189CleanPrivatePair
import Graph189DirtySideOrder
import Graph189BalancedPair

open SimpleGraph Finset
namespace Graph189PrivatePairOriginal
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

/-- The complete common-free case of the two-cut paper, with the
exceptional vertex in either component or at either anchor. -/
theorem traceable (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 15≤G.secondSmallestDegree) (sides : Graph189CutSides.CutSides G A B S)
    (pair : S={p,q}) (ne : p≠q) (sc : S.card≤G.vertexConnectivity)
    (a : ∀x∈A,¬(G.Adj x p ∧ G.Adj x q)) (b : ∀x∈B,¬(G.Adj x p ∧ G.Adj x q))
    (conA : (G.induce (A:Set V)).Connected) (conB : (G.induce (B:Set V)).Connected) :
    ∃x y,∃r : G.Walk x y,r.IsHamiltonian := by
  classical
  by_cases cleanA : Graph189CleanSideCounts.Clean G A p q
  · exact Graph189CleanPrivatePair.traceable hc cap large sides pair ne sc cleanA b conA conB
  by_cases cleanB : Graph189CleanSideCounts.Clean G B p q
  · exact Graph189CleanPrivatePair.traceable hc cap large sides.swap pair ne sc cleanB a conB conA
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  exact Graph189BalancedPair.traceable hc cap (by omega) sides sc pair ne
    (Graph189DirtySideOrder.order hc point sides.swap pair ne sc conB b cleanB)
    (Graph189DirtySideOrder.order hc point sides pair ne sc conA a cleanA)

#print axioms traceable
end Graph189PrivatePairOriginal
