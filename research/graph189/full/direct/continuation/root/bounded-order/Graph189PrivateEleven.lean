import Graph189SmallPrivatePair
import Graph189DirtySideOrder
import Graph189CleanPairOrder
import Graph189PrivateContactProfile

open SimpleGraph Finset Graph189DenseSideRoute
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189SmallPrivatePair
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

/-- In the clean common-free case at degree eleven the two losses depend on
the actual side orders. The total nonport budget prevents both sides costing
their separate worst-case allowances. -/
theorem clean_eleven (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (eleven : G.secondSmallestDegree=11) (minimum : 3≤G.minDegree)
    (floor : 4*G.secondSmallestDegree≤Fintype.card V+5)
    (sides : Graph189CutSides.CutSides G A B S) (pair : S={p,q}) (ne : p≠q) (sc : S.card≤G.vertexConnectivity)
    (clean : Graph189CleanSideCounts.Clean G A p q) (freeB : ∀x∈B,¬(G.Adj x p ∧ G.Adj x q))
    (conA : (G.induce (A:Set V)).Connected) (conB : (G.induce (B:Set V)).Connected) :
    ∃u v, ∃w : G.Walk u v,w.IsHamiltonian := by
  classical
  let k := G.secondSmallestDegree
  have eqk : k=11 := eleven
  have big : 3*G.secondSmallestDegree+2<Fintype.card V := by omega
  let R (W : Finset V) := (W.filter (fun x => G.dist p x≠1 ∧ G.dist q x≠1)).card
  have size : S.card=2 := by simp [pair,ne]
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have up := Graph189CleanPairOrder.nonport_order hc point sides pair ne sc big clean
  change Fintype.card V+R A+R B+_≤4*k+2 at up
  change 4*k≤Fintype.card V+5 at floor
  have few : R A+R B≤7 := by omega
  obtain ⟨missA,ordA⟩ := Graph189PrivateContactProfile.population hc sides.swap pair ne sc point freeB
  obtain ⟨missB,ordB⟩ := Graph189PrivateContactProfile.population hc sides pair ne sc point clean.private_ports
  change (A.filter (fun x => ¬G.Adj p x)).card≤k-1+R A at missA
  change (B.filter (fun x => ¬G.Adj p x)).card≤k-1+R B at missB
  change A.card≤2*k-2+R A at ordA
  change B.card≤2*k-2+R B at ordB
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
      (budget : Fintype.card V+R C+R D≤4*k+2) : ∃u v, ∃w : G.Walk u v,w.IsHamiltonian := by
    have parts : C.card+D.card+2=Fintype.card V := by
      have all : C∪D∪S=univ := eq_univ_of_forall (by
        intro u
        rcases cut.cover u with h|h|h
        · exact mem_union_left _ (mem_union_left _ h)
        · exact mem_union_left _ (mem_union_right _ h)
        · exact mem_union_right _ h)
      have total := congrArg Finset.card all
      rwa [card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨cut.left_cut,cut.right_cut⟩),
        card_union_of_disjoint cut.apart,size,card_univ] at total
    have few' : R C+R D≤7 := by omega
    have cp := Graph189DirtyRoutes.contacts hc point cut pair sc big freeC
    have dp := Graph189DirtyRoutes.contacts hc point cut.swap pair sc big freeD
    have every (W : Finset V) (x : V) (xW : x∈W)
        (bound : k-1≤(G.induce (W:Set V)).degree ⟨x,xW⟩) : k≤W.card := by
      have deg := (G.induce (W:Set V)).degree_lt_card_verts (⟨x,xW⟩ : W)
      change _<Fintype.card W at deg
      rw [Fintype.card_coe] at deg
      omega
    have minC (x : C) : k-1≤(G.induce (C:Set V)).degree x := by
      have l := Graph189CleanSideRoute.loss cut pair freeC x
      have h := high _ x.property
      omega
    have minD (x : D) (ne : x.val≠z) : k-1≤(G.induce (D:Set V)).degree x := by
      have l := Graph189CleanSideRoute.loss cut.swap pair freeD x
      have h := others _ x.property ne
      omega
    obtain ⟨c,cm⟩ := cut.left_nonempty
    have cmin := every C c cm (minC ⟨c,cm⟩)
    have dcount := card_le_card (filter_subset (G.Adj p) D)
    obtain ⟨d,dm,dz⟩ := exists_mem_ne (show 1<D.card by omega) z
    have dmin := every D d dm (minD ⟨d,dm⟩ dz)
    obtain ⟨i,inS,two,extra⟩ : ∃i∈S,2≤(D.filter (G.Adj i)).card ∧
        (2*k-3<D.card → 4≤(D.filter (G.Adj i)).card) := by
      by_cases wide : 2*k-3<D.card
      · obtain ⟨i,is_,many⟩ := chooseAnchor (D:=D) (by omega)
        exact ⟨i,is_,by omega,fun _ => many⟩
      exact ⟨p,by simp [pair],dp,fun e => (wide e).elim⟩
    obtain ⟨⟨c',cm',ci⟩,_⟩ := cut.contacts_of_minimum (fun T lt =>
      Graph189CutSides.connected_after_smaller_deletion T (lt.trans_le sc)) inS
    have missC := pc i inS D C cut.swap freeD
    have missD := pc i inS C D cut freeC
    have left := Graph189CleanSideRoute.high_route_by_size C i (by omega : 5≤k) conC minC
      ⟨c',mem_filter.mpr ⟨cm',ci.symm⟩⟩ (by omega)
    have right := Graph189CleanSideRoute.low_route_by_size D i (by omega : 5≤k) conD zD minD
      (by omega) two extra (by omega)
    obtain ⟨a,b,Q,hQ,near⟩ := Graph189TwoSoleNearest.join_routes cut inS left right
    rw [size] at near
    apply Graph189ExteriorLeaf.traceable_of_near_degree hc cap (by omega) (by change Fintype.card V≤5*k-5; omega)
      minimum Q hQ
    change Fintype.card V+2≤Q.support.length+k
    omega
  by_cases high : ∀v∈A,k≤G.degree v
  · by_cases opposite : ∀v∈B,k≤G.degree v
    · obtain ⟨z,zb⟩ := sides.right_nonempty
      exact join sides clean.private_ports freeB conA conB high z zb
        (fun v h _ => opposite v h) ordA ordB (by omega)
    push Not at opposite
    obtain ⟨z,zb,low⟩ := opposite
    exact join sides clean.private_ports freeB conA conB high z zb
      (fun v _ ne => (degree_pair (G:=G) v z ne).resolve_right (not_le.mpr low)) ordA ordB (by omega)
  push Not at high
  obtain ⟨z,za,low⟩ := high
  have highB (x : V) (xb : x∈B) : k≤G.degree x := (degree_pair (G:=G) x z
    (fun eq => Finset.disjoint_left.mp sides.apart za (eq ▸ xb))).resolve_right (not_le.mpr low)
  exact join sides.swap freeB clean.private_ports conB conA highB z za
    (fun v _ ne => (degree_pair (G:=G) v z ne).resolve_right (not_le.mpr low)) ordB ordA (by omega)

/-- All common-free separating pairs of degree eleven in the remaining window.
A defective side bounds the opposite side even when that opposite side is defective too. -/
theorem private_eleven (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (eleven : G.secondSmallestDegree=11) (minimum : 3≤G.minDegree)
    (floor : 4*G.secondSmallestDegree≤Fintype.card V+5)
    (sides : Graph189CutSides.CutSides G A B S) (pair : S={p,q}) (ne : p≠q) (sc : S.card≤G.vertexConnectivity)
    (freeA : ∀x∈A,¬(G.Adj x p ∧ G.Adj x q)) (freeB : ∀x∈B,¬(G.Adj x p ∧ G.Adj x q))
    (conA : (G.induce (A:Set V)).Connected) (conB : (G.induce (B:Set V)).Connected) :
    ∃x y, ∃r : G.Walk x y,r.IsHamiltonian := by
  classical
  by_cases cleanA : Graph189CleanSideCounts.Clean G A p q
  · exact clean_eleven hc cap eleven minimum floor sides pair ne sc cleanA freeB conA conB
  by_cases cleanB : Graph189CleanSideCounts.Clean G B p q
  · exact clean_eleven hc cap eleven minimum floor sides.swap pair ne sc cleanB freeA conB conA
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  exact balanced hc cap (by omega) minimum (by omega) sides pair ne sc freeA freeB conA conB
    (Graph189DirtySideOrder.order hc point sides.swap pair ne sc conB freeB cleanB)
    (Graph189DirtySideOrder.order hc point sides pair ne sc conA freeA cleanA)

end Graph189SmallPrivatePair
#print axioms Graph189SmallPrivatePair.clean_eleven
#print axioms Graph189SmallPrivatePair.private_eleven
