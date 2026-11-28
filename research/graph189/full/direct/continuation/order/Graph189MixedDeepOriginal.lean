import Graph189MixedDeepCounts
import Graph189BalancedPair
import Graph189CleanCommonPair

open SimpleGraph Finset Graph189DeepCommonPair
namespace Graph189MixedDeepOriginal
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

/-- The common side has a high nonport. The private side can be clean
or defective and may contain the exceptional vertex. -/
theorem of_eleven (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 11≤G.secondSmallestDegree) (sides : Graph189CutSides.CutSides G A B S)
    (pair : S={p,q}) (ne : p≠q) (sc : S.card≤G.vertexConnectivity)
    (con : (G.induce (A:Set V)).Connected) (free : ∀x∈A,¬(G.Adj x p ∧ G.Adj x q))
    {y z : V} (deep : Deep G B S y) (zb : z∈B) (common : ∀i∈S,G.Adj z i) :
    ∃a b,∃r : G.Walk a b,r.IsHamiltonian := by
  classical
  have size : S.card=2 := by simp [pair,ne]
  by_cases clean : Graph189CleanSideCounts.Clean G A p q
  · exact Graph189CleanCommonPair.of_eleven hc cap large sides pair ne sc clean zb
      (common p (by simp [pair])) (common q (by simp [pair]))
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  exact Graph189BalancedPair.of_eleven hc cap large sides sc pair ne
    (Graph189MixedDeepCounts.opposite hc point sides sc size deep zb common)
    (Graph189DirtySideOrder.order hc point sides pair ne sc con free clean)

theorem traceable (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 12≤G.secondSmallestDegree) (sides : Graph189CutSides.CutSides G A B S)
    (pair : S={p,q}) (ne : p≠q) (sc : S.card≤G.vertexConnectivity)
    (con : (G.induce (A:Set V)).Connected) (free : ∀x∈A,¬(G.Adj x p ∧ G.Adj x q))
    {y z : V} (deep : Deep G B S y) (zb : z∈B) (common : ∀i∈S,G.Adj z i) :
    ∃a b,∃r : G.Walk a b,r.IsHamiltonian :=
  of_eleven hc cap (by omega) sides pair ne sc con free deep zb common

#print axioms of_eleven
#print axioms traceable
end Graph189MixedDeepOriginal
