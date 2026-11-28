import Graph189DirtyRoutes
import Graph189DirtySideOrder
import Graph189TwoSoleNearest
import Graph189NearPathLinearOrder

open SimpleGraph Finset Graph189DenseSideRoute
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189DirtyPrivatePair
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

/-- The both-nonclean, common-free graph case of the separating-pair
argument. At most five vertices are omitted by the chosen two side paths. -/
theorem traceable (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 12≤G.secondSmallestDegree) (big : 3*G.secondSmallestDegree+2<Fintype.card V)
    (sides : Graph189CutSides.CutSides G A B S) (pair : S={p,q}) (ne : p≠q) (sc : S.card≤G.vertexConnectivity)
    (freeA : ∀x∈A,¬(G.Adj x p ∧ G.Adj x q)) (freeB : ∀x∈B,¬(G.Adj x p ∧ G.Adj x q))
    (conA : (G.induce (A:Set V)).Connected) (conB : (G.induce (B:Set V)).Connected)
    (dirtyA : ¬Graph189CleanSideCounts.Clean G A p q) (dirtyB : ¬Graph189CleanSideCounts.Clean G B p q) :
    ∃x y, ∃r : G.Walk x y,r.IsHamiltonian := by
  classical
  let k := G.secondSmallestDegree
  have lower : 12≤k := large
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have size : S.card=2 := by simp [pair,ne]
  have conn : 2≤G.vertexConnectivity := size ▸ sc
  have ordB := Graph189DirtySideOrder.order hc point sides pair ne sc conA freeA dirtyA
  have ordA := Graph189DirtySideOrder.order hc point sides.swap pair ne sc conB freeB dirtyB
  change A.card+1≤2*k at ordA
  change B.card+1≤2*k at ordB
  have cover : (univ : Finset V)⊆(A∪B)∪S := by
    intro x _
    rcases sides.cover x with h|h|h
    · exact mem_union_left _ (mem_union_left _ h)
    · exact mem_union_left _ (mem_union_right _ h)
    · exact mem_union_right _ h
  have bound := (card_le_card cover).trans (card_union_le _ _)
  rw [card_univ,size] at bound
  have union := card_union_le A B
  have order : Fintype.card V+11<5*k := by omega
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
      exact Graph189PairLinearGap.traceable_under_five hc cap conn (by omega) order r hr (by
        change Fintype.card V+3≤r.support.length+k
        omega)
    rcases Graph189DirtyRoutes.exceptional (by omega : 10≤k) part.swap pair freeD conD zD other nD dp dq with pRoute|qRoute
    · exact finish (by simp [pair] : p∈S)
        (Graph189DirtyRoutes.high (by omega : 10≤k) part pair freeC highC nC cp) pRoute
    · exact finish (by simp [pair] : q∈S)
        (Graph189DirtyRoutes.high (by omega : 10≤k) part reversePair revC highC nC cq) qRoute
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

#print axioms traceable
end Graph189DirtyPrivatePair
