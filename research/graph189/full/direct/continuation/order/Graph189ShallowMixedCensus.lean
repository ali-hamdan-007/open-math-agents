import Graph189DeepPairData
import Graph189DistanceLayers
import Graph189PrivateSideSize
import Graph189FarPrivatePort

open SimpleGraph Finset Graph189DeepCommonPair
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189ShallowMixedPair
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

/-- If a high port omits one anchor, it has at most its side's order
many neighbors. -/
private theorem side_floor (sides : Graph189CutSides.CutSides G A B S)
    (pair : S={p,q}) {x : V} (xa : x∈A) (miss : ¬G.Adj x q) : G.degree x≤A.card := by
  classical
  have inc : insert x (G.neighborFinset x)⊆insert p A := by
    intro y hy
    rcases mem_insert.mp hy with eq|yn
    · exact mem_insert_of_mem (eq.symm ▸ xa)
    have e := (G.mem_neighborFinset _ _).mp yn
    rcases sides.cover y with ya|yb|ys
    · exact mem_insert_of_mem ya
    · exact (sides.no_cross x xa y yb e).elim
    · rcases (show y=p ∨ y=q by simpa [pair] using ys) with h|h
      · exact mem_insert.mpr (Or.inl h)
      · exact (miss (h ▸ e)).elim
  have count := (card_le_card inc).trans (card_insert_le p A)
  rw [card_insert_of_notMem (by simp),G.card_neighborFinset_eq_degree] at count
  omega

private theorem representatives (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (pair : S={p,q}) (ne : p≠q) (sc : S.card≤G.vertexConnectivity) (con : (G.induce (A:Set V)).Connected)
    (point : ∀v,G.distEven v≤G.secondSmallestDegree+1) (largeB : 2*G.secondSmallestDegree≤B.card)
    (shallow : ∀x∈A,G.secondSmallestDegree≤G.degree x → ∃i∈S,G.Adj i x)
    (privateP : ∃x∈A,G.Adj x p ∧ ¬G.Adj x q) (privateQ : ∃x∈A,G.Adj x q ∧ ¬G.Adj x p) :
    (∃u∈A,G.dist u p=1 ∧ G.dist u q=2) ∧
    (∀x∈A,G.secondSmallestDegree≤G.degree x → G.Adj x p → ¬G.Adj x q → G.dist q x=2) := by
  classical
  let k := G.secondSmallestDegree
  have qs : q∈S := by simp [pair]
  obtain ⟨v,va,vq,vp⟩ := privateQ
  have atTwo (x : V) (xa : x∈A) (xh : k≤G.degree x) (xp : G.Adj x p) (xq : ¬G.Adj x q) : G.dist x q=2 := by
    have d := (hc x q).one_lt_dist_of_ne_of_not_adj
      (fun e => disjoint_left.mp sides.left_cut xa (e.symm ▸ qs)) xq
    by_contra! no
    have bad := Graph189FarPrivatePort.order hc sides con pair ne sc point xa xp (by omega) xh
      ⟨v,va,fun e => vp e.symm⟩
    omega
  refine ⟨?_,fun x xa xh xp xq => (G.dist_comm (u:=q) (v:=x)).trans (atTwo x xa xh xp xq)⟩
  by_cases choice : ∃x∈A,k≤G.degree x ∧ G.Adj x p ∧ ¬G.Adj x q
  · obtain ⟨x,xa,xh,xp,xq⟩ := choice
    exact ⟨x,xa,dist_eq_one_iff_adj.mpr xp,atTwo x xa xh xp xq⟩
  obtain ⟨x,xa,xp,xq⟩ := privateP
  have low : G.degree x<k := lt_of_not_ge (fun h => choice ⟨x,xa,h,xp,xq⟩)
  have xv : x≠v := fun e => xq (e.symm ▸ vq)
  obtain ⟨w⟩ := con (⟨x,xa⟩ : A) (⟨v,va⟩ : A)
  have live : 0<w.length := Nat.pos_of_ne_zero (fun h => xv (congrArg Subtype.val (Walk.length_eq_zero_iff.mp h).eq))
  let y := w.getVert 1
  have xy : G.Adj x y.val := by
    have h := w.adj_getVert_succ (i:=0) live
    simpa [y] using h
  have high := (degree_pair (G:=G) y.val x xy.ne.symm).resolve_right (not_le.mpr low)
  have yq : G.Adj y.val q := by
    by_contra no
    obtain ⟨i,si,iy⟩ := shallow y.val y.property high
    rcases (show i=p ∨ i=q by simpa [pair] using si) with eq|eq
    · exact choice ⟨y.val,y.property,high,(eq ▸ iy).symm,no⟩
    · exact no ((eq ▸ iy).symm)
  exact ⟨x,xa,dist_eq_one_iff_adj.mpr xp,Graph189LowDegreeTwo.two_edges xy yq
    (fun e => disjoint_left.mp sides.left_cut xa (e.symm ▸ qs)) xq⟩

/-- In a nonadjacent mixed pair with two private types in the shallow
common side, the actual anchor and representative rows give 2n ≤ 7k+1. -/
theorem census (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (pair : S={p,q}) (ne : p≠q) (nonadj : ¬G.Adj p q) (sc : S.card≤G.vertexConnectivity)
    (con : (G.induce (A:Set V)).Connected) (point : ∀v,G.distEven v≤G.secondSmallestDegree+1)
    (largeB : 2*G.secondSmallestDegree≤B.card) (shallow : ∀x∈A,G.secondSmallestDegree≤G.degree x → ∃i∈S,G.Adj i x)
    (free : ∀x∈B,¬(G.Adj x p ∧ G.Adj x q)) (common : ∃x∈A,∀i∈S,G.Adj x i)
    (privateP : ∃x∈A,G.Adj x p ∧ ¬G.Adj x q) (privateQ : ∃x∈A,G.Adj x q ∧ ¬G.Adj x p) :
    2*Fintype.card V≤7*G.secondSmallestDegree+1 := by
  classical
  let k := G.secondSmallestDegree
  let AP := A.filter (G.Adj p)
  let AQ := A.filter (G.Adj q)
  let C := AP∩AQ
  let P := B.filter (fun y => ∃i∈S,G.Adj i y)
  let E (i : V) := univ.filter (fun y => Even (G.dist i y))
  let W := B.filter (fun y => G.dist p y=2 ∧ G.dist q y=2)
  let T := B.filter (fun y => 3≤G.dist p y ∧ 3≤G.dist q y)
  let L := univ.filter (fun x => G.degree x<k)
  have reversePair := pair.trans (Finset.pair_comm _ _)
  have ps : p∈S := by simp [pair]
  have qs : q∈S := by simp [pair]
  have sz : S.card=2 := by simp [pair,ne]
  have flip (x : V) (xb : x∈B) (both : G.Adj x q ∧ G.Adj x p) : False := free x xb both.symm
  have contact (i : V) (si : i∈S) := (sides.contacts_of_minimum (fun X h =>
    Graph189CutSides.connected_after_smaller_deletion X (h.trans_le sc)) si).2
  obtain ⟨u,ub,up⟩ := contact p ps
  obtain ⟨v,vb,vq⟩ := contact q qs
  have cp := Graph189PrivateContactProfile.ports hc sides.swap pair ne sc point ub up
    (fun uq => free u ub ⟨up,uq⟩)
  have cq := Graph189PrivateContactProfile.ports hc sides.swap reversePair ne.symm sc point vb vq
    (fun vp => flip v vb ⟨vq,vp⟩)
  change AP.card+1≤k at cp
  change AQ.card+1≤k at cq
  have low : L.card≤1 := card_le_one.mpr (by
    intro x hx y hy
    by_contra d
    rcases degree_pair (G:=G) x y d with h|h
    · exact (not_lt_of_ge h) (mem_filter.mp hx).2
    · exact (not_lt_of_ge h) (mem_filter.mp hy).2)
  have leftSub : A⊆(AP∪AQ)∪L := by
    intro x xa
    by_cases high : k≤G.degree x
    · obtain ⟨i,si,ix⟩ := shallow x xa high
      apply mem_union_left
      rcases (show i=p ∨ i=q by simpa [pair] using si) with rfl|rfl
      · exact mem_union_left _ (mem_filter.mpr ⟨xa,ix⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨xa,ix⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,lt_of_not_ge high⟩)
  have sumA := (card_le_card leftSub).trans (card_union_le _ _)
  have interA := card_union_add_card_inter AP AQ
  change (AP∪AQ).card+C.card=AP.card+AQ.card at interA
  have aBound : A.card+C.card+1≤2*k := by omega
  obtain ⟨u,ua,iu,notU⟩ := privateP
  obtain ⟨v,va,iv,notV⟩ := privateQ
  have uv : u≠v := fun h => notU (h.symm ▸ iv)
  have bigA : k≤A.card := by
    rcases degree_pair (G:=G) u v uv with h|h
    · exact h.trans (side_floor sides pair ua notU)
    · exact h.trans (side_floor sides reversePair va notV)
  have smallT : T⊆L := by
    intro y yh
    obtain ⟨yb,yp,yq⟩ := mem_filter.mp yh
    exact mem_filter.mpr ⟨mem_univ _,Graph189PrivateSideSize.far_low_of_size hc point sides pair ne sc bigA yb yp yq⟩
  have tiny := (card_le_card smallT).trans low
  obtain ⟨⟨e,ea,ep,eq⟩,pNear⟩ := representatives hc sides pair ne sc con point largeB shallow
    ⟨u,ua,iu,notU⟩ ⟨v,va,iv,notV⟩
  obtain ⟨⟨f,fa,fq,fp⟩,qNear⟩ := representatives hc sides reversePair ne.symm sc con point largeB shallow
    ⟨v,va,iv,notV⟩ ⟨u,ua,iu,notU⟩
  have privateBound := Graph189PrivateRepresentativeBound.order hc sides pair point ea ep eq fa fp fq
  change B.card+_+2≤2*k+W.card+T.card at privateBound
  have unionAll : (univ:Finset V)⊆(A∪B)∪S := by
    intro x _
    rcases sides.cover x with a|b|s
    · exact mem_union_left _ (mem_union_left _ a)
    · exact mem_union_left _ (mem_union_right _ b)
    · exact mem_union_right _ s
  have real := (card_le_card unionAll).trans (card_union_le _ _)
  rw [card_univ,sz] at real
  have ab := card_union_le A B
  have first : Fintype.card V+C.card≤4*k+W.card := by omega
  obtain ⟨g,ga,cg⟩ := common
  have dist := Graph189LowDegreeTwo.two_edges (cg p ps).symm (cg q qs) ne nonadj
  have rev := (G.dist_comm (u:=q) (v:=p)).trans dist
  have ports : P.card≤k := port_bound hc sides point ga cg
  have doubles : insert p (insert q W) ⊆ E p∩E q := by
    intro x hx
    rcases mem_insert.mp hx with same|h
    · subst x
      exact mem_inter.mpr ⟨by simp [E],by simp [E,rev]⟩
    rcases mem_insert.mp h with same|h
    · subst x
      exact mem_inter.mpr ⟨by simp [E,dist],by simp [E]⟩
    obtain ⟨_,px,qx⟩ := mem_filter.mp h
    exact mem_inter.mpr ⟨by simp [E,px],by simp [E,qx]⟩
  have pOut : p∉insert q W := fun h => (mem_insert.mp h).elim ne (fun h =>
    disjoint_left.mp sides.right_cut (mem_filter.mp h).1 ps)
  have qOut : q∉W := fun h => disjoint_left.mp sides.right_cut (mem_filter.mp h).1 qs
  have overlap := card_le_card doubles
  rw [card_insert_of_notMem pOut,card_insert_of_notMem qOut] at overlap
  have cover : univ⊆(((E p∪E q)∪C)∪P)∪L := by
    intro x _
    by_cases high : k≤G.degree x
    swap
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,lt_of_not_ge high⟩)
    apply mem_union_left
    rcases sides.cover x with xa|xb|xs
    · apply mem_union_left
      by_cases px : G.Adj p x
      · by_cases qx : G.Adj q x
        · exact mem_union_right _ (mem_inter.mpr ⟨mem_filter.mpr ⟨xa,px⟩,mem_filter.mpr ⟨xa,qx⟩⟩)
        · have d := pNear x xa high px.symm (fun h => qx h.symm)
          exact mem_union_left _ (mem_union_right _ (by simp [E,d]))
      · obtain ⟨i,si,ix⟩ := shallow x xa high
        have qx : G.Adj q x := by
          rcases (show i=p ∨ i=q by simpa [pair] using si) with h|h
          · exact (px (h ▸ ix)).elim
          · exact h ▸ ix
        have d := qNear x xa high qx.symm (fun h => px h.symm)
        exact mem_union_left _ (mem_union_left _ (by simp [E,d]))
    · by_cases port : ∃i∈S,G.Adj i x
      · exact mem_union_right _ (mem_filter.mpr ⟨xb,port⟩)
      have notFar : x∉T := fun h => (not_lt_of_ge high) (mem_filter.mp (smallT h)).2
      have depth (i : V) (si : i∈S) : 1<G.dist i x := (hc i x).one_lt_dist_of_ne_of_not_adj
        (fun h => disjoint_left.mp sides.right_cut xb (h ▸ si)) (fun e => port ⟨i,si,e⟩)
      have hP := depth p ps
      have hQ := depth q qs
      have both : ¬(3≤G.dist p x ∧ 3≤G.dist q x) := fun h => notFar (mem_filter.mpr ⟨xb,h⟩)
      apply mem_union_left
      apply mem_union_left
      rcases (show G.dist p x=2 ∨ G.dist q x=2 by omega) with h|h
      · exact mem_union_left _ (by simp [E,h])
      · exact mem_union_right _ (by simp [E,h])
    · apply mem_union_left
      apply mem_union_left
      rcases (show x=p ∨ x=q by simpa [pair] using xs) with rfl|rfl
      · exact mem_union_left _ (by simp [E])
      · exact mem_union_right _ (by simp [E])
  have c1 := (card_le_card cover).trans (card_union_le _ _)
  rw [card_univ] at c1
  have c2 := card_union_le ((E p∪E q)∪C) P
  have c3 := card_union_le (E p∪E q) C
  have add := card_union_add_card_inter (E p) (E q)
  have ep' : (E p).card≤k+1 := point p
  have eq' : (E q).card≤k+1 := point q
  change 2*Fintype.card V≤7*k+1
  omega

#print axioms census
end Graph189ShallowMixedPair
