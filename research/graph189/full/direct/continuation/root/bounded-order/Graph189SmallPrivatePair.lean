import Graph189NearDegreeWindow
import Graph189DirtyRoutes
import Graph189TwoSoleNearest

open SimpleGraph Finset Graph189DenseSideRoute
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189SmallPrivatePair
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

/-- Either anchor can receive the all-high route. The side containing the
possible low vertex chooses its anchor. Together these miss at most five
vertices, even for the smallest residual degree seven. -/
theorem balanced (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 7≤G.secondSmallestDegree) (minimum : 3≤G.minDegree) (big : 3*G.secondSmallestDegree+2<Fintype.card V)
    (sides : Graph189CutSides.CutSides G A B S) (pair : S={p,q}) (ne : p≠q) (sc : S.card≤G.vertexConnectivity)
    (freeA : ∀x∈A,¬(G.Adj x p ∧ G.Adj x q)) (freeB : ∀x∈B,¬(G.Adj x p ∧ G.Adj x q))
    (conA : (G.induce (A:Set V)).Connected) (conB : (G.induce (B:Set V)).Connected)
    (ordA : A.card+1≤2*G.secondSmallestDegree) (ordB : B.card+1≤2*G.secondSmallestDegree) :
    ∃x y, ∃r : G.Walk x y,r.IsHamiltonian := by
  classical
  let k := G.secondSmallestDegree
  have lower : 7≤k := large
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have size : S.card=2 := by simp [pair,ne]
  have reversePair : S={q,p} := pair.trans (Finset.pair_comm _ _)
  have join {C D : Finset V} (part : Graph189CutSides.CutSides G C D S)
      (highC : ∀x∈C,k≤G.degree x) (freeC : ∀x∈C,¬(G.Adj x p ∧ G.Adj x q))
      (freeD : ∀x∈D,¬(G.Adj x p ∧ G.Adj x q)) (conD : (G.induce (D:Set V)).Connected)
      (nC : C.card+1≤2*k) (nD : D.card+1≤2*k) (z : V) (zD : z∈D)
      (other : ∀x∈D,x≠z → k≤G.degree x) : ∃x y, ∃r : G.Walk x y,r.IsHamiltonian := by
    have revC (x : V) (h : x∈C) (both : G.Adj x q ∧ G.Adj x p) : False := freeC x h both.symm
    have revD (x : V) (h : x∈D) (both : G.Adj x q ∧ G.Adj x p) : False := freeD x h both.symm
    have cp := Graph189DirtyRoutes.contacts hc point part pair sc big freeC
    have cq := Graph189DirtyRoutes.contacts hc point part reversePair sc big revC
    have dp := Graph189DirtyRoutes.contacts hc point part.swap pair sc big freeD
    have dq := Graph189DirtyRoutes.contacts hc point part.swap reversePair sc big revD
    have finish {a : V} (sa : a∈S) (one : Route G C a 1) (three : Route G D a 3) :
        ∃x y, ∃r : G.Walk x y,r.IsHamiltonian := by
      obtain ⟨x,y,r,hr,near⟩ := Graph189TwoSoleNearest.join_routes part sa one three
      rw [size] at near
      apply Graph189OrdinaryPathGap.traceable_of_near_unrestricted hc
        (fun v => by simpa only [Nat.add_comm 1] using point v) (by omega) minimum r hr
      change Fintype.card V≤r.support.length+(k+1)/2+1
      omega
    rcases Graph189DirtyRoutes.exceptional_of_five (by omega : 5≤k) part.swap pair freeD conD zD other nD dp dq with pRoute|qRoute
    · exact finish (by simp [pair] : p∈S)
        (Graph189DirtyRoutes.high_of_five (by omega : 5≤k) part pair freeC highC nC cp) pRoute
    · exact finish (by simp [pair] : q∈S)
        (Graph189DirtyRoutes.high_of_five (by omega : 5≤k) part reversePair revC highC nC cq) qRoute
  by_cases highA : ∀x∈A,k≤G.degree x
  · by_cases highB : ∀x∈B,k≤G.degree x
    · obtain ⟨z,zB⟩ := sides.right_nonempty
      exact join sides highA freeA freeB conB ordA ordB z zB (fun x xB _ => highB x xB)
    push_neg at highB
    obtain ⟨z,zB,low⟩ := highB
    exact join sides highA freeA freeB conB ordA ordB z zB (fun x _ diff =>
      (degree_pair (G:=G) x z diff).resolve_right (not_le.mpr low))
  push_neg at highA
  obtain ⟨z,zA,low⟩ := highA
  have highB (x : V) (xB : x∈B) : k≤G.degree x := (degree_pair (G:=G) x z (fun e =>
    Finset.disjoint_left.mp sides.apart zA (e ▸ xB))).resolve_right (not_le.mpr low)
  exact join sides.swap highB freeB freeA conA ordB ordA z zA (fun x _ diff =>
    (degree_pair (G:=G) x z diff).resolve_right (not_le.mpr low))

end Graph189SmallPrivatePair
#print axioms Graph189SmallPrivatePair.balanced
