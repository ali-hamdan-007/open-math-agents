import Graph189CleanPrivatePair
import Graph189DirtyPrivatePair

open SimpleGraph Finset
namespace Graph189PrivatePairOriginal
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

/-- The complete common-free case of the two-cut paper, with the
exceptional vertex in either component or at either anchor. -/
theorem traceable (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 12≤G.secondSmallestDegree) (sides : Graph189CutSides.CutSides G A B S)
    (pair : S={p,q}) (ne : p≠q) (sc : S.card≤G.vertexConnectivity)
    (a : ∀x∈A,¬(G.Adj x p ∧ G.Adj x q)) (b : ∀x∈B,¬(G.Adj x p ∧ G.Adj x q))
    (conA : (G.induce (A:Set V)).Connected) (conB : (G.induce (B:Set V)).Connected) :
    ∃x y,∃r : G.Walk x y,r.IsHamiltonian := by
  classical
  by_cases cleanA : Graph189CleanSideCounts.Clean G A p q
  · exact Graph189CleanPrivatePair.traceable hc cap large sides pair ne sc cleanA b conA conB
  by_cases cleanB : Graph189CleanSideCounts.Clean G B p q
  · exact Graph189CleanPrivatePair.traceable hc cap large sides.swap pair ne sc cleanB a conB conA
  by_cases big : 3*G.secondSmallestDegree+2<Fintype.card V
  · exact Graph189DirtyPrivatePair.traceable hc cap (by omega) big sides pair ne sc a b conA conB cleanA cleanB
  have size : S.card=2 := by simp [pair,ne]
  exact Graph189OnePortCover.below_four hc cap (size ▸ sc) (by omega) (by omega)

#print axioms traceable
end Graph189PrivatePairOriginal
