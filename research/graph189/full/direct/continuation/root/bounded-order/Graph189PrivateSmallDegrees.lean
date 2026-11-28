import Graph189SmallPrivateRoutes
import Graph189PrivateEleven

open SimpleGraph Finset Graph189DenseSideRoute
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189SmallPrivatePair
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

/-- In a common-free separating pair the longer side chooses its starting anchor.
Both sides keep their exceptional vertex when selecting high ends. The clean
count bounds the combined losses even at second-smallest degree seven. -/
theorem clean_from_seven (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 7≤G.secondSmallestDegree) (minimum : 3≤G.minDegree)
    (big : 3*G.secondSmallestDegree+2<Fintype.card V) (floor : 4*G.secondSmallestDegree≤Fintype.card V+5)
    (sides : Graph189CutSides.CutSides G A B S) (pair : S={p,q}) (ne : p≠q) (sc : S.card≤G.vertexConnectivity)
    (clean : Graph189CleanSideCounts.Clean G A p q) (freeB : ∀x∈B,¬(G.Adj x p ∧ G.Adj x q))
    (conA : (G.induce (A:Set V)).Connected) (conB : (G.induce (B:Set V)).Connected) :
    ∃u v, ∃r : G.Walk u v,r.IsHamiltonian := by
  classical
  let k := G.secondSmallestDegree
  let R (W : Finset V) := (W.filter (fun x => G.dist p x≠1 ∧ G.dist q x≠1)).card
  have lo : 7≤k := large
  change 4*k≤Fintype.card V+5 at floor
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have size : S.card=2 := by simp [pair,ne]
  have pop := Graph189CleanPairOrder.nonport_order hc point sides pair ne sc big clean
  change Fintype.card V+R A+R B+_≤4*k+2 at pop
  have ordA := (Graph189PrivateContactProfile.population hc sides.swap pair ne sc point freeB).2
  have ordB := (Graph189PrivateContactProfile.population hc sides pair ne sc point clean.private_ports).2
  change A.card≤2*k-2+R A at ordA
  change B.card≤2*k-2+R B at ordB
  have total : A.card+B.card+2=Fintype.card V := by
    have all : A∪B∪S=univ := eq_univ_of_forall (by
      intro u
      rcases sides.cover u with h|h|h
      · exact mem_union_left _ (mem_union_left _ h)
      · exact mem_union_left _ (mem_union_right _ h)
      · exact mem_union_right _ h)
    have count := congrArg Finset.card all
    rwa [card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨sides.left_cut,sides.right_cut⟩),
      card_union_of_disjoint sides.apart,size,card_univ] at count
  have oneAnchor {C D : Finset V} (cut : Graph189CutSides.CutSides G C D S)
      (free : ∀x∈C,¬(G.Adj x p ∧ G.Adj x q)) (i : V) (si : i∈S) : 2≤(C.filter (G.Adj i)).card := by
    rcases (show i=p ∨ i=q by simpa [pair] using si) with rfl|rfl
    · exact Graph189DirtyRoutes.contacts hc point cut pair sc big free
    · exact Graph189DirtyRoutes.contacts hc point cut (pair.trans (Finset.pair_comm _ _)) sc big (fun _ hx e => free _ hx e.symm)
  have lower {C D : Finset V} (cut : Graph189CutSides.CutSides G C D S)
      (free : ∀x∈C,¬(G.Adj x p ∧ G.Adj x q)) : k≤C.card := by
    have two := oneAnchor cut free p (by simp [pair])
    obtain ⟨x,xp,y,yp,xy⟩ := one_lt_card.mp two
    have reg (v : V) (vc : v∈C) (h : k≤G.degree v) : k≤C.card := by
      let t : C := ⟨v,vc⟩
      have drop := Graph189CleanSideRoute.loss cut pair free t
      have room := (G.induce (C:Set V)).degree_lt_card_verts t
      change _<Fintype.card C at room
      rw [Fintype.card_coe] at room
      change G.degree v≤_+1 at drop
      omega
    exact (degree_pair (G:=G) x y xy).elim (reg x (mem_filter.mp xp).1) (reg y (mem_filter.mp yp).1)
  have finish {C D : Finset V} (cut : Graph189CutSides.CutSides G C D S)
      (fc : ∀x∈C,¬(G.Adj x p ∧ G.Adj x q)) (fd : ∀x∈D,¬(G.Adj x p ∧ G.Adj x q))
      (cc : (G.induce (C:Set V)).Connected) (cd : (G.induce (D:Set V)).Connected)
      (sort : C.card≤D.card) (toc : C.card+D.card+2=Fintype.card V)
      (budget : Fintype.card V+R C+R D≤4*k+2) (boundC : C.card≤2*k-2+R C) (boundD : D.card≤2*k-2+R D) :
      ∃u v, ∃r : G.Walk u v,r.IsHamiltonian := by
    let P := D.filter (fun v => ∃i∈S,G.Adj i v)
    have sums := card_filter_add_card_filter_not (s:=D) (p:=fun v => ∃i∈S,G.Adj i v)
    have eq : D.filter (fun v => ¬∃i∈S,G.Adj i v)=D.filter (fun v => G.dist p v≠1 ∧ G.dist q v≠1) := by
      ext v
      simp [pair,dist_eq_one_iff_adj,not_or]
    rw [eq] at sums
    change P.card+R D=D.card at sums
    have dc := lower cut.swap fd
    have ccnt := lower cut fc
    obtain ⟨x,xP,y,r,hr,inD,lenD⟩ := from_marks cut.swap pair fd cd minimum P (filter_subset _ _)
      (card_pos.mp (by omega)) (by change D.card<2*(k-1)+P.card; omega)
    obtain ⟨_,i,si,ix⟩ := mem_filter.mp xP
    have two := oneAnchor cut fc i si
    obtain ⟨a,ap,b,t,ht,inC,lenC⟩ := from_marks cut pair fc cc minimum (C.filter (G.Adj i)) (filter_subset _ _)
      (card_pos.mp (by omega)) (by change C.card<2*(k-1)+_; omega)
    have first : Route G C i (C.card-(2*k-2)) := ⟨a,b,t,ht,(mem_filter.mp ap).2,inC,lenC⟩
    have last : Route G D i (D.card-(2*k-2)) := ⟨x,y,r,hr,ix,inD,lenD⟩
    obtain ⟨u,v,Q,hQ,len⟩ := Graph189TwoSoleNearest.join_routes cut si first last
    rw [size] at len
    apply Graph189ExteriorLeaf.traceable_of_near_degree hc cap large (by change Fintype.card V≤5*k-5; omega) minimum Q hQ
    change Fintype.card V+2≤Q.support.length+k
    omega
  by_cases sort : A.card≤B.card
  · exact finish sides clean.private_ports freeB conA conB sort total (by omega) ordA ordB
  exact finish sides.swap freeB clean.private_ports conB conA (by omega) (by omega) (by omega) ordB ordA

theorem private_from_seven (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 7≤G.secondSmallestDegree) (big : 3*G.secondSmallestDegree+2<Fintype.card V) (minimum : 3≤G.minDegree)
    (floor : 4*G.secondSmallestDegree≤Fintype.card V+5)
    (sides : Graph189CutSides.CutSides G A B S) (pair : S={p,q}) (ne : p≠q) (sc : S.card≤G.vertexConnectivity)
    (freeA : ∀x∈A,¬(G.Adj x p ∧ G.Adj x q)) (freeB : ∀x∈B,¬(G.Adj x p ∧ G.Adj x q))
    (conA : (G.induce (A:Set V)).Connected) (conB : (G.induce (B:Set V)).Connected) :
    ∃x y, ∃r : G.Walk x y,r.IsHamiltonian := by
  classical
  by_cases cleanA : Graph189CleanSideCounts.Clean G A p q
  · exact clean_from_seven hc cap large minimum big floor sides pair ne sc cleanA freeB conA conB
  by_cases cleanB : Graph189CleanSideCounts.Clean G B p q
  · exact clean_from_seven hc cap large minimum big floor sides.swap pair ne sc cleanB freeA conB conA
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  exact balanced hc cap (by omega) minimum (by omega) sides pair ne sc freeA freeB conA conB
    (Graph189DirtySideOrder.order hc point sides.swap pair ne sc conB freeB cleanB)
    (Graph189DirtySideOrder.order hc point sides pair ne sc conA freeA cleanA)

end Graph189SmallPrivatePair
#print axioms Graph189SmallPrivatePair.clean_from_seven
#print axioms Graph189SmallPrivatePair.private_from_seven
