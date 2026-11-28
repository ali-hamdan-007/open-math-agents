import Graph189CommonPortQuota
import Graph189SeparatedSideComponents
import Graph189OnePortThreeCut
import Graph189DistanceLayers

open SimpleGraph Finset Graph189SoleNearestSides
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189DeepCommonPair
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V}

/-- True at both deep sides of any two-cut with a common port on each
side, for either adjacency pattern of the anchors and any exceptional
vertex. -/
theorem traceable (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (sides : Graph189CutSides.CutSides G A B S) (sc : S.card≤G.vertexConnectivity)
    {p q : V} (sep : S={p,q}) (ne : p≠q) (large : 10≤G.secondSmallestDegree)
    (deepA : ∃x,Deep G A S x) (deepB : ∃x,Deep G B S x)
    (commonA : ∃u∈A,∀i∈S,G.Adj u i) (commonB : ∃v∈B,∀i∈S,G.Adj v i) :
    ∃x y, ∃r : G.Walk x y,r.IsHamiltonian := by
  classical
  let k := G.secondSmallestDegree
  have sz : S.card=2 := by simp [sep,ne]
  have point (v : V) : G.distEven v≤k+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  let F (R : Finset V) := ∃x i, Witness G R S x i
  have done {A B : Finset V} (sides : Graph189CutSides.CutSides G A B S)
      (dA : ∃x, Deep G A S x) (dB : ∃y, Deep G B S y)
      (cA : ∃u∈A,∀i∈S,G.Adj u i) (cB : ∃v∈B,∀i∈S,G.Adj v i) (no : ¬F A) :
      ∃x y,∃r : G.Walk x y,r.IsHamiltonian := by
    obtain ⟨a,ha⟩ := dA
    obtain ⟨b,hb⟩ := dB
    obtain ⟨u,ua,cu⟩ := cA
    obtain ⟨v,vb,cv⟩ := cB
    let P (R : Finset V) := R.filter (fun x => ∃i∈S,G.Adj i x)
    let D (R : Finset V) := R.filter (fun x => Deep G R S x)
    let L := univ.filter (fun x => G.degree x<k)
    let E (i : V) := univ.filter (fun x => Even (G.dist i x))
    have pA : (P A).card≤k := port_bound hc sides.swap point vb cv
    have pB : (P B).card≤k := port_bound hc sides point ua cu
    have low : L.card≤1 := card_le_one.mpr (by
      intro x hx y hy
      by_contra xy
      rcases degree_pair (G:=G) x y xy with h|h
      · exact (not_lt_of_ge h) (mem_filter.mp hx).2
      · exact (not_lt_of_ge h) (mem_filter.mp hy).2)
    have eq (i : V) (h : i∈S) : i=p ∨ i=q := by simpa [sep] using h
    have ps : p∈S := by simp [sep]
    have qs : q∈S := by simp [sep]
    have each {x : V} (d : Deep G A S x) : G.dist p x=2 ∧ G.dist q x=2 := by
      obtain ⟨i,si,ix,_⟩ := nearest hc sides point d hb
      have both {j l : V} (js : j∈S) (jj : G.dist j x=2) (other : ∀t∈S,t=j ∨ t=l) : G.dist l x=2 := by
        by_contra fail
        apply no
        exact ⟨x,j,d.1,js,d.2.1,d.2.2,jj,fun t ts h => (other t ts).elim Eq.symm (by rintro rfl; contradiction)⟩
      rcases eq i si with rfl|rfl
      · exact ⟨ix,both ps ix eq⟩
      · exact ⟨both qs ix (fun t ts => (eq t ts).symm),ix⟩
    have intersect : D A ⊆ E p∩E q := by
      intro x hx
      obtain ⟨atP,atQ⟩ := each (mem_filter.mp hx).2
      exact mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _,by simp [atP]⟩,mem_filter.mpr ⟨mem_univ _,by simp [atQ]⟩⟩
    have cov : univ⊆((((E p∪E q)∪P A)∪P B)∪L) := by
      intro x _
      by_cases lowx : G.degree x<k
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,lowx⟩)
      apply mem_union_left
      rcases sides.cover x with xa|xb|xs
      · by_cases port : ∃i∈S,G.Adj i x
        · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨xa,port⟩))
        push_neg at port
        have h := (each ⟨xa,by omega,port⟩).1
        exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem_univ _,by simp [h]⟩)))
      · by_cases port : ∃i∈S,G.Adj i x
        · exact mem_union_right _ (mem_filter.mpr ⟨xb,port⟩)
        push_neg at port
        obtain ⟨i,si,ix,_⟩ := nearest hc sides.swap point (x:=x) ⟨xb,by omega,port⟩ ha
        apply mem_union_left
        apply mem_union_left
        rcases eq i si with rfl|rfl
        · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,by simp [ix]⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,by simp [ix]⟩)
      · apply mem_union_left
        apply mem_union_left
        rcases eq x xs with rfl|rfl
        · exact mem_union_left _ (by simp [E])
        · exact mem_union_right _ (by simp [E])
    have first := (card_le_card cov).trans (card_union_le _ _)
    rw [card_univ] at first
    have first2 := card_union_le ((E p∪E q)∪P A) (P B)
    have first3 := card_union_le (E p∪E q) (P A)
    have add := card_union_add_card_inter (E p) (E q)
    have overlap := card_le_card intersect
    have pe : (E p).card≤k+1 := point p
    have qe : (E q).card≤k+1 := point q
    let extra := (∃x, x∈E p∩E q ∧ x∉D A) ∨ (∃x, x∈P B ∧ x∈E p∪E q)
    have more : extra := by
      by_cases adjacent : G.Adj p q
      swap
      · have dist := Graph189LowDegreeTwo.two_edges (cu p ps).symm (cu q qs) ne adjacent
        left
        exact ⟨q,mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _,by simp [dist]⟩,
          mem_filter.mpr ⟨mem_univ _,by simp⟩⟩,
          fun h => disjoint_left.mp sides.left_cut (mem_filter.mp h).1 qs⟩
      have pick (i j : V) (ij : G.Adj i j) (si : i∈S) (sj : j∈S)
          (labels : ∀t∈S,t=i ∨ t=j) (dist : G.dist i b=2) : extra := by
        obtain ⟨w,iw,wb⟩ := Graph189LowDegreeTwo.split_two hc dist
        have wB : w∈B := by
          rcases sides.cover w with wa|outside|ws
          · exact (sides.no_cross w wa b hb.1 wb).elim
          · exact outside
          · exact (hb.2.2 w ws wb).elim
        by_cases jw : G.Adj j w
        · have db := Graph189LowDegreeTwo.two_edges jw wb
            (fun h => disjoint_left.mp sides.right_cut hb.1 (h ▸ sj)) (hb.2.2 j sj)
          have hit (t : V) (ts : t∈S) : b∈E t := by
            apply mem_filter.mpr
            refine ⟨mem_univ _,?_⟩
            rcases labels t ts with rfl|rfl
            · simp [dist]
            · simp [db]
          left
          exact ⟨b,mem_inter.mpr ⟨hit p ps,hit q qs⟩,
            fun h => disjoint_left.mp sides.apart (mem_filter.mp h).1 hb.1⟩
        · have dw := Graph189LowDegreeTwo.two_edges ij.symm iw
            (fun h => disjoint_left.mp sides.right_cut wB (h ▸ sj)) jw
          have wj : w∈E j := mem_filter.mpr ⟨mem_univ _,by simp [dw]⟩
          right
          refine ⟨w,mem_filter.mpr ⟨wB,i,si,iw⟩,?_⟩
          rcases eq j sj with rfl|rfl
          · exact mem_union_left _ wj
          · exact mem_union_right _ wj
      obtain ⟨i,si,dist,_⟩ := nearest hc sides.swap point hb ha
      rcases eq i si with ip|iq
      · exact pick p q adjacent ps qs eq (ip ▸ dist)
      · exact pick q p adjacent.symm qs ps (fun t ht => (eq t ht).symm) (iq ▸ dist)
    have upper1 : Fintype.card V+(D A).card+1≤2*k+3+(P A).card+(P B).card := by
      rcases more with ⟨x,both,out⟩|⟨x,port,atAnchor⟩
      · have ext : insert x (D A)⊆E p∩E q := insert_subset both intersect
        have bound := card_le_card ext
        rw [card_insert_of_notMem out] at bound
        omega
      · have common : x∈((E p∪E q)∪P A)∩P B := mem_inter.mpr ⟨mem_union_left _ atAnchor,port⟩
        have pos := card_pos.mpr ⟨x,common⟩
        have sum := card_union_add_card_inter ((E p∪E q)∪P A) (P B)
        omega
    have charge := Graph189BoundaryDebit.even_quota hc sides (fun T h =>
      Graph189CutSides.connected_after_smaller_deletion T (h.trans_le sc)) point (Y:=D B) (filter_subset _ _) ha.1
    have all : (D B).filter (fun x => Even (G.dist a x))=D B := filter_eq_self.mpr (by
      intro x hx
      obtain ⟨i,is_,_,_,four⟩ := nearest hc sides point ha (mem_filter.mp hx).2
      rw [four]
      decide)
    have empty : Graph189PortLabels.support G S a=∅ := eq_empty_iff_forall_notMem.mpr (by
      intro i hi
      obtain ⟨si,e⟩ := mem_filter.mp hi
      exact ha.2.2 i si e.symm)
    rw [all,empty,card_empty,Nat.add_zero,sz] at charge
    have high_cover (R : Finset V) : R.filter (fun x => G.secondSmallestDegree≤G.degree x) ⊆ P R∪D R := by
      intro x hx
      obtain ⟨xr,h⟩ := mem_filter.mp hx
      by_cases port : ∃i∈S,G.Adj i x
      · exact mem_union_left _ (mem_filter.mpr ⟨xr,port⟩)
      · push_neg at port
        exact mem_union_right _ (mem_filter.mpr ⟨xr,xr,h,port⟩)
    have hA := (card_le_card (high_cover A)).trans (card_union_le _ _)
    have hB := (card_le_card (high_cover B)).trans (card_union_le _ _)
    have total := order_of_high_sides sides
    have upper2 : Fintype.card V≤k+1+(D A).card+(P A).card+(P B).card := by omega
    change 10≤k at large
    apply Graph189OnePortCover.below_four hc cap (by omega) (by omega)
    change _<4*k
    by_cases rich : 2*k≤(P A).card+(P B).card+1
    · have order := Graph189ShallowCommonOrder.rich_order hc sides (by omega) sz point ua cu vb cv
        (by change k≤(P A).card+1; omega) (by change k≤(P B).card+1; omega)
      change Fintype.card V≤3*k+4 at order
      omega
    · omega
  by_cases Asole : F A
  · by_cases Bsole : F B
    · obtain ⟨x,i,left⟩ := Asole
      obtain ⟨y,j,right⟩ := Bsole
      exact Graph189SeparatedSideComponents.traceable hc cap sides sc sz (by omega) left right
    · exact done sides.swap deepB deepA commonB commonA Bsole
  · exact done sides deepA deepB commonA commonB Asole

#print axioms traceable
end Graph189DeepCommonPair
