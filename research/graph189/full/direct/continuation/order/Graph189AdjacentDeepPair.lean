import Graph189BothCommonPair
import Graph189AdjacentPrivateCut

open SimpleGraph Finset Graph189DeepCommonPair
namespace Graph189AdjacentDeepPair
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At every original qualifying graph of second degree at least 10, an
adjacent separating pair with a high nonport on each side forces a
Hamiltonian path. The side orders, low vertex and all port patterns are
unrestricted. -/
theorem traceable (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    {A B S : Finset V} (sides : Graph189CutSides.CutSides G A B S) (sc : S.card≤G.vertexConnectivity)
    {p q : V} (sep : S={p,q}) (edge : G.Adj p q) (large : 10≤G.secondSmallestDegree)
    (deepA : ∃x,Deep G A S x) (deepB : ∃x,Deep G B S x) :
    ∃x y,∃r : G.Walk x y,r.IsHamiltonian := by
  classical
  let C (R : Finset V) := ∃x∈R,∀i∈S,G.Adj x i
  have noCommon (R : Finset V) (fail : ¬C R) (v : V) (vr : v∈R) :
      ¬(G.Adj v p ∧ G.Adj v q) := by
    intro hits
    apply fail
    refine ⟨v,vr,fun i si => ?_⟩
    rcases (show i=p ∨ i=q by simpa [sep] using si) with rfl|rfl
    · exact hits.1
    · exact hits.2
  by_cases a : C A
  · by_cases b : C B
    · exact Graph189DeepCommonPair.traceable hc cap sides sc sep edge.ne large deepA deepB a b
    · exact Graph189AdjacentPrivateCut.traceable hc cap sides.swap sc sep edge (by omega) (noCommon B b) (Or.inr deepA)
  · exact Graph189AdjacentPrivateCut.traceable hc cap sides sc sep edge (by omega) (noCommon A a) (Or.inr deepB)

/-- Every adjacent separating pair in an original qualifying graph of
second-smallest degree at least ten forces a Hamiltonian path. -/
theorem unrestricted (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    {A B S : Finset V} (sides : Graph189CutSides.CutSides G A B S) (sc : S.card≤G.vertexConnectivity)
    {p q : V} (sep : S={p,q}) (edge : G.Adj p q) (large : 10≤G.secondSmallestDegree) :
    ∃x y,∃r : G.Walk x y,r.IsHamiltonian := by
  classical
  let C (R : Finset V) := ∃u∈R, ∀i∈S,G.Adj u i
  have noCommon {R : Finset V} (h : ¬C R) (x : V) (xr : x∈R) (both : G.Adj x p ∧ G.Adj x q) : False := by
    apply h
    refine ⟨x,xr,fun i si => ?_⟩
    rcases (show i=p ∨ i=q by simpa [sep] using si) with rfl|rfl
    · exact both.1
    · exact both.2
  by_cases left : C A
  · by_cases right : C B
    · exact Graph189BothCommonPair.traceable hc cap sides sc sep edge.ne large left right
    · exact Graph189AdjacentPrivateCut.unrestricted hc cap sides.swap sc sep edge (by omega) (noCommon right)
  · exact Graph189AdjacentPrivateCut.unrestricted hc cap sides sc sep edge (by omega) (noCommon left)

#print axioms unrestricted
#print axioms traceable
end Graph189AdjacentDeepPair
