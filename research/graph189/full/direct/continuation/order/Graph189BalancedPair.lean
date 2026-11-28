import Graph189BalancedSideRoutes
import Graph189AdjacentDeepPair
import Graph189CleanSideCounts

open SimpleGraph Finset Graph189DeepCommonPair Graph189DenseSideRoute
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189BalancedPair
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

/-- Nonadjacent anchors force two separate contacts with either anchor in
each side once every edge is triangular. -/
private theorem two_contacts (hc : G.Connected) (point : ∀v,G.distEven v≤G.secondSmallestDegree+1)
    (sides : Graph189CutSides.CutSides G A B S) (sc : S.card≤G.vertexConnectivity)
    (pair : S={p,q}) (nonadj : ¬G.Adj p q) (big : 3*G.secondSmallestDegree+2<Fintype.card V) :
    2≤(A.filter (G.Adj p)).card := by
  classical
  have ps : p∈S := by simp [pair]
  obtain ⟨⟨v,va,vp⟩,_⟩ := sides.contacts_of_minimum (fun T h =>
    Graph189CutSides.connected_after_smaller_deletion T (h.trans_le sc)) ps
  obtain ⟨w,vw,pw⟩ := Graph189CleanSideCounts.edge_triangle hc point big vp
  have wa : w∈A := by
    rcases sides.cover w with h|h|h
    · exact h
    · exact (sides.no_cross v va w h vw).elim
    · rcases (show w=p ∨ w=q by simpa [pair] using h) with e|e
      · exact (pw.ne e.symm).elim
      · exact (nonadj (e ▸ pw)).elim
  exact one_lt_card.mpr ⟨v,mem_filter.mpr ⟨va,vp.symm⟩,w,mem_filter.mpr ⟨wa,pw⟩,vw.ne⟩

private theorem port_count (hc : G.Connected) (point : ∀v,G.distEven v≤G.secondSmallestDegree+1)
    (sides : Graph189CutSides.CutSides G A B S) (sc : S.card≤G.vertexConnectivity)
    (pair : S={p,q}) (ne : p≠q) (large : 12≤G.secondSmallestDegree)
    (left : 2*G.secondSmallestDegree≤A.card+6) (right : 2*G.secondSmallestDegree≤B.card+6)
    (marksP : 2≤(A.filter (G.Adj p)).card) (marksQ : 2≤(A.filter (G.Adj q)).card) :
    4≤(A.filter (fun v => ∃i∈S,G.Adj i v)).card := by
  classical
  let k := G.secondSmallestDegree
  let P (R : Finset V) := R.filter (fun v => ∃i∈S,G.Adj i v)
  let D (R : Finset V) := R.filter (fun v => Deep G R S v)
  let L := univ.filter (fun v => G.degree v<k)
  change 4≤(P A).card
  have sz : S.card=2 := by simp [pair,ne]
  have ps : p∈S := by simp [pair]
  have qs : q∈S := by simp [pair]
  by_cases common : ∃u∈A,∀i∈S,G.Adj u i
  swap
  · have dis : Disjoint (A.filter (G.Adj p)) (A.filter (G.Adj q)) := disjoint_left.mpr (by
      intro x xp xq
      apply common
      refine ⟨x,(mem_filter.mp xp).1,fun i si => ?_⟩
      rcases (show i=p ∨ i=q by simpa [pair] using si) with rfl|rfl
      · exact (mem_filter.mp xp).2.symm
      · exact (mem_filter.mp xq).2.symm)
    have sub : A.filter (G.Adj p)∪A.filter (G.Adj q)⊆P A := by
      intro x hx
      rcases mem_union.mp hx with h|h
      · exact mem_filter.mpr ⟨(mem_filter.mp h).1,p,ps,(mem_filter.mp h).2⟩
      · exact mem_filter.mpr ⟨(mem_filter.mp h).1,q,qs,(mem_filter.mp h).2⟩
    have lower := card_le_card sub
    rw [card_union_of_disjoint dis] at lower
    omega
  obtain ⟨u,ua,cu⟩ := common
  have pb : (P B).card≤k := port_bound hc sides point ua cu
  have low : L.card≤1 := card_le_one.mpr (by
    intro x xh y yh
    by_contra h
    rcases degree_pair (G:=G) x y h with l|r
    · exact (not_lt_of_ge l) (mem_filter.mp xh).2
    · exact (not_lt_of_ge r) (mem_filter.mp yh).2)
  have cover (R : Finset V) : R.card≤(P R).card+(D R).card+1 := by
    have sub : R⊆(P R∪D R)∪L := by
      intro v vr
      by_cases vh : k≤G.degree v
      swap
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,Nat.lt_of_not_ge vh⟩)
      apply mem_union_left
      by_cases port : ∃i∈S,G.Adj i v
      · exact mem_union_left _ (mem_filter.mpr ⟨vr,port⟩)
      · push_neg at port
        exact mem_union_right _ (mem_filter.mpr ⟨vr,vr,vh,port⟩)
    have total := (card_le_card sub).trans (card_union_le _ _)
    have sum := card_union_le (P R) (D R)
    omega
  have coverB := cover B
  change 2*k≤A.card+6 at left
  change 2*k≤B.card+6 at right
  change 12≤k at large
  obtain ⟨b,bb⟩ := card_pos.mp (show 0<(D B).card by omega)
  have deep : Deep G B S b := (mem_filter.mp bb).2
  have row := Graph189BoundaryDebit.even_quota hc sides.swap (fun T h =>
    Graph189CutSides.connected_after_smaller_deletion T (h.trans_le sc)) point (Y:=D A) (filter_subset _ _) deep.1
  have actual : (D A).filter (fun x => Even (G.dist b x))=D A := filter_eq_self.mpr (by
    intro x xD
    obtain ⟨_,_,_,_,four⟩ := nearest hc sides.swap point deep (mem_filter.mp xD).2
    simp [four])
  have empty : Graph189PortLabels.support G S b=∅ := eq_empty_iff_forall_notMem.mpr (by
    intro i hi
    obtain ⟨si,e⟩ := mem_filter.mp hi
    exact deep.2.2 i si e.symm)
  rw [actual,empty,card_empty,Nat.add_zero,sz] at row
  have all := cover A
  change (D A).card+2≤k at row
  omega

/-- Every balanced actual separating pair, with arbitrary position of
the low vertex, supplies a Hamiltonian path in the original graph. -/
theorem traceable (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 12≤G.secondSmallestDegree) (sides : Graph189CutSides.CutSides G A B S)
    (sc : S.card≤G.vertexConnectivity) (pair : S={p,q}) (ne : p≠q)
    (sizeA : A.card+1≤2*G.secondSmallestDegree) (sizeB : B.card+1≤2*G.secondSmallestDegree) :
    ∃x y, ∃r : G.Walk x y,r.IsHamiltonian := by
  classical
  let k := G.secondSmallestDegree
  have sz : S.card=2 := by simp [pair,ne]
  have conn : 2≤G.vertexConnectivity := by omega
  by_cases adjacent : G.Adj p q
  · exact Graph189AdjacentDeepPair.unrestricted hc cap sides sc pair adjacent (by omega)
  by_cases small : Fintype.card V+5<4*k
  · exact Graph189OnePortCover.below_four hc cap conn (by omega) small
  have big : 3*G.secondSmallestDegree+2<Fintype.card V := by change 3*k+2<_; change 12≤k at large; omega
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have many (c : Fin 3 ↪ (G.induce {v : V | v∉S}).ConnectedComponent) :=
    Graph189AnySingletonCut.of_three_components hc cap S sc (by omega) (by omega) (by omega) c
  by_cases conA : (G.induce (A:Set V)).Connected
  swap
  · exact (Graph189SeparatedSideComponents.three_of_disconnected_side sides conA).elim many
  by_cases conB : (G.induce (B:Set V)).Connected
  swap
  · exact (Graph189SeparatedSideComponents.three_of_disconnected_side sides.swap conB).elim many
  have cover : (univ:Finset V)⊆(A∪B)∪S := by
    intro v _
    rcases sides.cover v with a|b|s
    · exact mem_union_left _ (mem_union_left _ a)
    · exact mem_union_left _ (mem_union_right _ b)
    · exact mem_union_right _ s
  have total := (card_le_card cover).trans (card_union_le _ _)
  rw [card_univ,sz] at total
  have sum := card_union_le A B
  change A.card+1≤2*k at sizeA
  change B.card+1≤2*k at sizeB
  change 12≤k at large
  have left : 2*k≤A.card+6 := by omega
  have right : 2*k≤B.card+6 := by omega
  have order : Fintype.card V+11<5*k := by omega
  have reversePair : S={q,p} := pair.trans (Finset.pair_comm _ _)
  have join {C D : Finset V} (part : Graph189CutSides.CutSides G C D S)
      (highC : ∀x∈C,k≤G.degree x) (z : V) (zD : z∈D) (highD : ∀x∈D,x≠z → k≤G.degree x)
      (conC : (G.induce (C:Set V)).Connected) (conD : (G.induce (D:Set V)).Connected)
      (loC : 2*k≤C.card+6) (loD : 2*k≤D.card+6) (hiC : C.card+1≤2*k) (hiD : D.card+1≤2*k) :
      ∃x y, ∃r : G.Walk x y,r.IsHamiltonian := by
    have cp := two_contacts hc point part sc pair adjacent big
    have cq := two_contacts hc point part sc reversePair (fun e => adjacent e.symm) big
    have dp := two_contacts hc point part.swap sc pair adjacent big
    have dq := two_contacts hc point part.swap sc reversePair (fun e => adjacent e.symm) big
    have enough := port_count hc point part.swap sc pair ne large loD loC dp dq
    obtain ⟨i,si,routeD⟩ := Graph189BalancedSideRoutes.exceptional (by omega : 10≤k)
      part.swap pair ne conD zD highD hiD enough
    have routeC : Route G C i 3 := by
      rcases (show i=p ∨ i=q by simpa [pair] using si) with rfl|rfl
      · exact Graph189BalancedSideRoutes.high (by omega : 10≤k) part pair ne conC highC hiC cp
      · exact Graph189BalancedSideRoutes.high (by omega : 10≤k) part reversePair ne.symm conC highC hiC cq
    obtain ⟨a,b,r,hr,near⟩ := Graph189TwoSoleNearest.join_routes part si routeC routeD
    rw [sz] at near
    exact Graph189PairLinearGap.traceable_under_five hc cap conn (by omega) order r hr (by
      change Fintype.card V+3≤r.support.length+k
      omega)
  by_cases highA : ∀x∈A,k≤G.degree x
  · by_cases highB : ∀x∈B,k≤G.degree x
    · obtain ⟨z,zB⟩ := sides.right_nonempty
      exact join sides highA z zB (fun x xB _ => highB x xB) conA conB left right sizeA sizeB
    push_neg at highB
    obtain ⟨z,zB,l⟩ := highB
    exact join sides highA z zB (fun x _ ne => (degree_pair (G:=G) x z ne).resolve_right (not_le.mpr l))
      conA conB left right sizeA sizeB
  push_neg at highA
  obtain ⟨z,zA,l⟩ := highA
  have highB (x : V) (xB : x∈B) : k≤G.degree x := (degree_pair (G:=G) x z (fun e =>
    disjoint_left.mp sides.apart zA (e ▸ xB))).resolve_right (not_le.mpr l)
  exact join sides.swap highB z zA (fun x _ ne => (degree_pair (G:=G) x z ne).resolve_right (not_le.mpr l))
    conB conA right left sizeB sizeA

#print axioms traceable
end Graph189BalancedPair
