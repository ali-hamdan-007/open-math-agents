import Graph189CleanPairOrder
import Graph189ModerateEight

open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189CleanTwoCutOriginal
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B S : Finset V} {p q : V}

/-- Both local counts from the separating-pair paper, applied to the actual
graph. The threshold counts the nonports on the clean side and the
nonports and common ports on the opposite side. -/
theorem traceable (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 8≤G.secondSmallestDegree) (sides : Graph189CutSides.CutSides G A B S)
    (pair : S={p,q}) (ne : p≠q) (sc : S.card≤G.vertexConnectivity)
    (clean : Graph189CleanSideCounts.Clean G A p q)
    (many : 8≤(A.filter (fun x => G.dist p x≠1 ∧ G.dist q x≠1)).card+
       (B.filter (fun x => G.dist p x≠1 ∧ G.dist q x≠1)).card+
       (B.filter (fun x => G.dist p x=1 ∧ G.dist q x=1)).card) :
    ∃ u v : V, ∃ r : G.Walk u v, r.IsHamiltonian := by
  classical
  let k := G.secondSmallestDegree
  have size : S.card=2 := by simp [pair,ne]
  have two : 2≤G.vertexConnectivity := size ▸ sc
  apply Graph189ModerateEight.traceable_below_four hc cap (by omega) two
  by_cases big : 3*G.secondSmallestDegree+2<Fintype.card V
  swap
  · omega
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    have h := (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
    omega
  have bound := Graph189CleanPairOrder.nonport_order hc point sides pair ne sc big clean
  omega

#print axioms traceable
end Graph189CleanTwoCutOriginal
