import Graph189CleanPairOrder
import Graph189PrivateContactProfile
import Graph189CleanSideRoute
import Graph189TwoSoleNearest
import Graph189OnePortThreeCut
import Graph189NearPathLinearOrder

open Finset SimpleGraph Graph189DenseSideRoute
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189CleanPrivatePair
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B S : Finset V} {p q : V}

/-- The clean case of the two common-free sides in the original
separating-pair paper, at all orders for k≥13 and with any low vertex. -/
theorem traceable (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 13≤G.secondSmallestDegree) (sides : Graph189CutSides.CutSides G A B S)
    (pair : S={p,q}) (ne : p≠q) (sc : S.card≤G.vertexConnectivity)
    (clean : Graph189CleanSideCounts.Clean G A p q) (freeB : ∀x∈B,¬(G.Adj x p ∧ G.Adj x q))
    (conA : (G.induce (A:Set V)).Connected) (conB : (G.induce (B:Set V)).Connected) :
    ∃u v, ∃w : G.Walk u v,w.IsHamiltonian := by
  classical
  by_contra bad
  let k := G.secondSmallestDegree
  let R (W : Finset V) := (W.filter (fun x => G.dist p x≠1 ∧ G.dist q x≠1)).card
  have size : S.card=2 := by simp [pair,ne]
  have conn : 2≤G.vertexConnectivity := size ▸ sc
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    have h := (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
    omega
  have lower : 4*k≤Fintype.card V+5 := by
    by_cases higher : 3≤G.vertexConnectivity
    · have h := Graph189RotationLinked.base_order bad point (l:=3) (by decide) higher (by omega)
      change 4*(k-3+2)≤Fintype.card V+1 at h
      change 13≤k at large
      omega
    · have eq : G.vertexConnectivity=2 := by omega
      have h := Graph189OnePortCover.additional_index hc cap conn (by rw [eq]; omega) bad
      rw [eq] at h
      change 4*(k-3+2)≤Fintype.card V+1 at h
      change 13≤k at large
      omega
  change 13≤k at large
  have up := Graph189CleanPairOrder.nonport_order hc point sides pair ne sc
    (by change 3*k+2<Fintype.card V; omega) clean
  change Fintype.card V+R A+R B+_ ≤4*k+2 at up
  have few : R A+R B≤7 := by omega
  obtain ⟨missA,ordA⟩ := Graph189PrivateContactProfile.population hc sides.swap pair ne sc point freeB
  obtain ⟨missB,ordB⟩ := Graph189PrivateContactProfile.population hc sides pair ne sc point clean.private_ports
  change (A.filter (fun x => ¬G.Adj p x)).card≤k-1+R A at missA
  change (B.filter (fun x => ¬G.Adj p x)).card≤k-1+R B at missB
  change A.card≤2*k-2+R A at ordA
  change B.card≤2*k-2+R B at ordB
  have all : (univ : Finset V)⊆(A∪B)∪S := by
    intro x _
    rcases sides.cover x with h|h|h
    · exact mem_union_left _ (mem_union_left _ h)
    · exact mem_union_left _ (mem_union_right _ h)
    · exact mem_union_right _ h
  have total := (card_le_card all).trans (card_union_le _ _)
  rw [card_univ,size] at total
  have sum := card_union_le A B
  have pc (i : V) (hi : i∈S) (U W : Finset V) (cut : Graph189CutSides.CutSides G U W S)
      (free : ∀x∈U,¬(G.Adj x p ∧ G.Adj x q)) :
      (W.filter (fun v => ¬G.Adj i v)).card≤k-1+R W := by
    rcases (show i=p ∨ i=q by simpa [pair] using hi) with rfl|rfl
    · exact (Graph189PrivateContactProfile.population hc cut pair ne sc point free).1
    · have h := (Graph189PrivateContactProfile.population hc cut
        (pair.trans (Finset.pair_comm _ _)) ne.symm sc point (fun v hv e => free v hv e.symm)).1
      simpa only [R,and_comm] using h
  have chooseAnchor {D : Finset V} (room : 7+R D≤D.card) : ∃i∈S,4≤(D.filter (G.Adj i)).card := by
    by_contra! small
    have left := small p (by simp [pair])
    have right := small q (by simp [pair])
    let P := D.filter (G.Adj p)
    let Q := D.filter (G.Adj q)
    let N := D.filter (fun x => G.dist p x≠1 ∧ G.dist q x≠1)
    have cover : D⊆P∪Q∪N := by
      intro x hx
      by_cases l : G.Adj p x
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hx,l⟩))
      by_cases t : G.Adj q x
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hx,t⟩))
      exact mem_union_right _ (mem_filter.mpr ⟨hx,fun e => l (dist_eq_one_iff_adj.mp e),
        fun e => t (dist_eq_one_iff_adj.mp e)⟩)
    have bound := (card_le_card cover).trans (card_union_le _ _)
    have count := card_union_le P Q
    change P.card<4 at left
    change Q.card<4 at right
    change 7+N.card≤D.card at room
    omega
  have join {C D : Finset V} (cut : Graph189CutSides.CutSides G C D S)
      (freeC : ∀x∈C,¬(G.Adj x p ∧ G.Adj x q)) (freeD : ∀x∈D,¬(G.Adj x p ∧ G.Adj x q))
      (conC : (G.induce (C:Set V)).Connected) (conD : (G.induce (D:Set V)).Connected)
      (high : ∀x∈C,k≤G.degree x) (z : V) (zD : z∈D) (others : ∀x∈D,x≠z → k≤G.degree x)
      (orderC : C.card≤2*k-2+R C) (orderD : D.card≤2*k-2+R D)
      (enough : 7+R D≤D.card) (nonports : R C+R D≤7) : False := by
    obtain ⟨i,inS,many⟩ := chooseAnchor enough
    obtain ⟨v,vC,vi⟩ := (cut.contacts_of_minimum (fun T lt =>
      Graph189CutSides.connected_after_smaller_deletion T (lt.trans_le sc)) inS).1
    have leftRoute := Graph189CleanSideRoute.high_route_sharp C i (by omega : 11≤k)
      (by omega : R C≤7) conC (fun x => by
        have loss := Graph189CleanSideRoute.loss cut pair freeC x
        have h := high x.val x.property
        omega) orderC ⟨v,mem_filter.mpr ⟨vC,vi.symm⟩⟩ (pc i inS D C cut.swap freeD)
    have rightRoute := Graph189CleanSideRoute.low_route D i (by omega : 11≤k)
      (by omega : R D≤7) conD zD (fun x nx => by
        have loss := Graph189CleanSideRoute.loss cut.swap pair freeD x
        have h := others x.val x.property nx
        omega) orderD many (pc i inS C D cut freeC)
    obtain ⟨u,v,w,hw,near⟩ := Graph189TwoSoleNearest.join_routes cut inS leftRoute rightRoute
    rw [size] at near
    exact bad (Graph189PairLinearGap.traceable_under_five hc cap conn (by omega)
      (by change Fintype.card V+11<5*k; omega) w hw (by
        change Fintype.card V+3≤w.support.length+k
        omega))
  by_cases high : ∀v∈A,k≤G.degree v
  · by_cases opposite : ∀v∈B,k≤G.degree v
    · obtain ⟨z,zb⟩ := sides.right_nonempty
      exact join sides clean.private_ports freeB conA conB high z zb
        (fun v h _ => opposite v h) ordA ordB (by omega) few
    push Not at opposite
    obtain ⟨z,zb,low⟩ := opposite
    exact join sides clean.private_ports freeB conA conB high z zb
      (fun v _ ne => (degree_pair (G:=G) v z ne).resolve_right (not_le.mpr low))
      ordA ordB (by omega) few
  push Not at high
  obtain ⟨z,za,low⟩ := high
  have highB (x : V) (xb : x∈B) : k≤G.degree x := (degree_pair (G:=G) x z
    (fun eq => Finset.disjoint_left.mp sides.apart za (eq ▸ xb))).resolve_right (not_le.mpr low)
  exact join sides.swap freeB clean.private_ports conB conA highB z za
    (fun v _ ne => (degree_pair (G:=G) v z ne).resolve_right (not_le.mpr low))
    ordB ordA (by omega) (by omega)

#print axioms traceable
end Graph189CleanPrivatePair
