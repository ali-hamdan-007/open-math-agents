import Graph189SmallCommonRoutes
import Graph189SmallPrivateRoutes
import Graph189BalancedPairCounts
import Graph189NearDegreeWindow
import Graph189TwoSoleNearest

open SimpleGraph Finset Graph189DenseSideRoute
namespace Graph189SmallMixedPair
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

def ports (G : SimpleGraph V) [DecidableRel G.Adj] (W S : Finset V) := W.filter (fun x => ∃i∈S,G.Adj i x)

theorem mixed (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 7≤G.secondSmallestDegree) (minimum : 3≤G.minDegree)
    (big : 3*G.secondSmallestDegree+2<Fintype.card V) (upper : Fintype.card V≤5*G.secondSmallestDegree-5)
    (sides : Graph189CutSides.CutSides G A B S) (pair : S={p,q}) (ne : p≠q) (sc : S.card≤G.vertexConnectivity)
    (nonadj : ¬G.Adj p q) (free : ∀x∈B,¬(G.Adj x p ∧ G.Adj x q))
    (conA : (G.induce (A:Set V)).Connected) (conB : (G.induce (B:Set V)).Connected)
    (choose : (B.card+1≤2*G.secondSmallestDegree ∧ A.card<2*(G.secondSmallestDegree-1)+(ports G A S).card) ∨
      (A.card+1≤2*G.secondSmallestDegree ∧ B.card<2*(G.secondSmallestDegree-1)+(ports G B S).card))
    (loss : max 1 (A.card-(2*G.secondSmallestDegree-4))+(B.card-(2*G.secondSmallestDegree-2))+3≤G.secondSmallestDegree) :
    ∃u v, ∃r : G.Walk u v,r.IsHamiltonian := by
  classical
  let k := G.secondSmallestDegree
  let a := max 1 (A.card-(2*k-4))
  let b := B.card-(2*k-2)
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have sz : S.card=2 := by simp [pair,ne]
  have rev := pair.trans (Finset.pair_comm _ _)
  have ps : p∈S := by simp [pair]
  have marks {C D : Finset V} (cut : Graph189CutSides.CutSides G C D S) (i : V) (si : i∈S) :
      2≤(C.filter (G.Adj i)).card := by
    rcases (show i=p ∨ i=q by simpa [pair] using si) with rfl|rfl
    · exact Graph189BalancedPair.two_contacts hc point cut sc pair nonadj big
    · exact Graph189BalancedPair.two_contacts hc point cut sc rev (fun e => nonadj e.symm) big
  have many {C D : Finset V} (cut : Graph189CutSides.CutSides G C D S) : 2≤(ports G C S).card :=
    (marks cut p ps).trans (card_le_card (by
      intro x hit
      exact mem_filter.mpr ⟨(mem_filter.mp hit).1,p,ps,(mem_filter.mp hit).2⟩))
  have finish {i : V} (si : i∈S) (left : Route G A i a) (right : Route G B i b) : ∃u v, ∃r : G.Walk u v,r.IsHamiltonian := by
    obtain ⟨u,v,Q,hQ,len⟩ := Graph189TwoSoleNearest.join_routes sides si left right
    rw [sz] at len
    apply Graph189ExteriorLeaf.traceable_of_near_degree hc cap large upper minimum Q hQ
    change a+b+3≤G.secondSmallestDegree at loss
    omega
  rcases choose with ⟨small,room⟩|⟨small,room⟩
  · obtain ⟨x,xP,y,Q,hQ,ins,len⟩ := Graph189SmallPrivatePair.common_from_marks sides pair ne conA large minimum
      (ports G A S) (filter_subset _ _) (many sides) (fun v va e => mem_filter.mpr ⟨va,p,ps,e⟩) room
    obtain ⟨_,i,si,ix⟩ := mem_filter.mp xP
    have two := marks sides.swap i si
    obtain ⟨u,up,v,r,hr,inB,size⟩ := Graph189SmallPrivatePair.from_marks sides.swap pair free conB minimum
      (B.filter (G.Adj i)) (filter_subset _ _) (card_pos.mp (by omega)) (by omega)
    exact finish si ⟨x,y,Q,hQ,ix,ins,len⟩ ⟨u,v,r,hr,(mem_filter.mp up).2,inB,size⟩
  obtain ⟨x,xP,y,Q,hQ,ins,len⟩ := Graph189SmallPrivatePair.from_marks sides.swap pair free conB minimum
    (ports G B S) (filter_subset _ _) (card_pos.mp (by have := many sides.swap; omega)) room
  obtain ⟨_,i,si,ix⟩ := mem_filter.mp xP
  have right : Route G B i b := ⟨x,y,Q,hQ,ix,ins,len⟩
  have fixed (j : V) (eq : S={i,j}) (diff : i≠j) : Route G A i a := by
    have two := marks sides i si
    obtain ⟨u,up,v,r,hr,inA,size⟩ := Graph189SmallPrivatePair.common_from_marks sides eq diff conA large minimum
      (A.filter (G.Adj i)) (filter_subset _ _) two (fun _ va e => mem_filter.mpr ⟨va,e⟩) (by omega)
    exact ⟨u,v,r,hr,(mem_filter.mp up).2,inA,size⟩
  rcases (show i=p ∨ i=q by simpa [pair] using si) with rfl|rfl
  · exact finish si (fixed q pair ne) right
  · exact finish si (fixed p rev ne.symm) right

end Graph189SmallMixedPair
#print axioms Graph189SmallMixedPair.mixed
