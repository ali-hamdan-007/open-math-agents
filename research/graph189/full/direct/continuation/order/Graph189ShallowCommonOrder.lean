import Graph189DeepPairData
import Graph189DistanceLayers

open SimpleGraph Finset Graph189DeepCommonPair
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189ShallowCommonOrder
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V}

/-- A common port with at most one distance-two vertex on its own side
has its entire side within distance two. -/
theorem radius (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (two : 2≤G.vertexConnectivity) {x : V} (xa : x∈A) (common : ∀i∈S,G.Adj x i)
    (few : (A.filter (fun v => G.dist x v=2)).card≤1) (v : V) (va : v∈A) :
    G.dist x v≤2 := by
  classical
  by_contra! far
  let T := A.filter (fun w => G.dist x w=2)
  let H := G.induce {w : V | w∉T}
  have small : T.card<G.vertexConnectivity := by omega
  have con : H.Connected := Graph189CutSides.connected_after_smaller_deletion T small
  have vx : v∉T := fun h => (Nat.ne_of_gt far) (mem_filter.mp h).2
  have xx : x∉T := by simp [T]
  obtain ⟨p⟩ := con ⟨v,vx⟩ ⟨x,xx⟩
  obtain ⟨a,b,⟨aa,fa⟩,nb,e,_⟩ := Graph189CutSides.walk_exits
    (fun w : {w : V | w∉T} => w.val∈A ∧ 2<G.dist x w.val) p ⟨va,far⟩ (by simp)
  have near := hc.dist_triangle (u:=x) (v:=b.val) (w:=a.val)
  rw [dist_eq_one_iff_adj.mpr (show G.Adj b.val a.val from e.symm)] at near
  rcases sides.cover b.val with ba|bb|bs
  · have dist : G.dist x b.val≤2 := by by_contra! h; exact nb ⟨ba,h⟩
    exact b.property (mem_filter.mpr ⟨ba,by omega⟩)
  · exact sides.no_cross a.val aa b.val bb e
  · rw [dist_eq_one_iff_adj.mpr (common b.val bs)] at near
    omega

/-- In the borderline shallow side, every opposite vertex has opposite
distance parity to the low nonport z and the common high port c. -/
theorem offset (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    {z c : V} (za : z∈A) (ca : c∈A) (zc : G.Adj z c)
    (no : ∀ i∈S,¬G.Adj z i) (hit : ∀i∈S,G.Adj c i) (v : V) (vb : v∈B) :
    G.dist z v=G.dist c v+1 := by
  obtain ⟨w,len⟩ := (hc z v).exists_walk_length_eq_dist
  obtain ⟨a,sa,atA⟩ := sides.meets za vb w
  have wt := congrArg Walk.length (Walk.take_spec w atA)
  rw [Walk.length_append] at wt
  have l := G.dist_le (w.takeUntil a atA)
  have r := G.dist_le (w.dropUntil a atA)
  have ne : z≠a := fun eq => Finset.disjoint_left.mp sides.left_cut za (eq.symm ▸ sa)
  have lo := (hc z a).one_lt_dist_of_ne_of_not_adj ne (no a sa)
  have cv := hc.dist_triangle (u:=c) (v:=a) (w:=v)
  rw [dist_eq_one_iff_adj.mpr (hit a sa)] at cv
  have zv := hc.dist_triangle (u:=z) (v:=c) (w:=v)
  rw [dist_eq_one_iff_adj.mpr zc] at zv
  omega

/-- If both sides of a separating pair contain a common port and one side
is shallow among high vertices, any high vertex on the shallow side gives
the true order bound n ≤ 3k+4. -/
theorem order (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (sc : S.card≤G.vertexConnectivity) (sz : S.card=2) (point : ∀v,G.distEven v≤G.secondSmallestDegree+1)
    (shallow : ∀v∈A,G.secondSmallestDegree≤G.degree v → ∃i∈S,G.Adj i v)
    (highA : ∃x∈A,G.secondSmallestDegree≤G.degree x)
    (commonA : ∃u∈A,∀i∈S,G.Adj u i) (commonB : ∃v∈B,∀i∈S,G.Adj v i) :
    Fintype.card V≤3*G.secondSmallestDegree+4 := by
  classical
  let k := G.secondSmallestDegree
  let P (R : Finset V) := R.filter (fun v => ∃i∈S,G.Adj i v)
  obtain ⟨u,ua,cu⟩ := commonA
  obtain ⟨v,vb,cv⟩ := commonB
  obtain ⟨x,xa,xh⟩ := highA
  have pA : (P A).card≤k := port_bound hc sides.swap point vb cv
  have pB : (P B).card≤k := port_bound hc sides point ua cu
  have offA : (A\P A).card≤1 := card_le_one.mpr (by
    intro a ha b hb
    by_contra ne
    rcases degree_pair (G:=G) a b ne with h|h
    · exact (mem_sdiff.mp ha).2 (mem_filter.mpr ⟨(mem_sdiff.mp ha).1,shallow a (mem_sdiff.mp ha).1 h⟩)
    · exact (mem_sdiff.mp hb).2 (mem_filter.mpr ⟨(mem_sdiff.mp hb).1,shallow b (mem_sdiff.mp hb).1 h⟩))
  have sizeA := card_sdiff_add_card_eq_card (show P A⊆A from filter_subset _ _)
  have cover : univ⊆(A∪B)∪S := by
    intro y _
    rcases sides.cover y with a|b|s
    · exact mem_union_left _ (mem_union_left _ a)
    · exact mem_union_left _ (mem_union_right _ b)
    · exact mem_union_right _ s
  have total := (card_le_card cover).trans (card_union_le _ _)
  rw [card_univ] at total
  have split := card_union_le A B
  have incl {a : V} (aa : a∈A) : insert a (G.neighborFinset a)⊆A∪S := by
    intro w hw
    rcases mem_insert.mp hw with same|wn
    · exact mem_union_left _ (same.symm ▸ aa)
    rcases sides.cover w with wa|wb|ws
    · exact mem_union_left _ wa
    · exact (sides.no_cross a aa w wb ((G.mem_neighborFinset _ _).mp wn)).elim
    · exact mem_union_right _ ws
  have nAS := card_union_of_disjoint sides.left_cut
  have xdeg := card_le_card (incl xa)
  rw [card_insert_of_notMem (by simp),G.card_neighborFinset_eq_degree,nAS] at xdeg
  change k≤G.degree x at xh
  by_cases many : k≤(P A).card+1
  · let T := B.filter (fun y => G.dist v y=2)
    have Tsmall : T.card≤1 := by
      have dis : Disjoint T (P A) := sides.apart.symm.mono (filter_subset _ _) (filter_subset _ _)
      have vout : v∉T∪P A := by
        intro hv
        rcases mem_union.mp hv with vt|vp
        · have := (mem_filter.mp vt).2
          simp at this
        · exact Finset.disjoint_left.mp sides.apart (mem_filter.mp vp).1 vb
      have quota := Graph189TwofoldCover.outside_quota point (T∪P A) vout
      rw [filter_eq_self.mpr (by
        intro a ha
        rcases mem_union.mp ha with atT|atP
        · simp [(mem_filter.mp atT).2]
        · obtain ⟨aa,i,si,ia⟩ := mem_filter.mp atP
          rw [Graph189PortDifference.cross_two hc sides.swap vb aa (cv i si) ia]
          decide),card_union_of_disjoint dis] at quota
      change T.card+(P A).card≤k at quota
      omega
    obtain ⟨i,si⟩ := card_pos.mp (show 0<S.card by omega)
    let E := (univ.filter (fun w => Even (G.dist i w))).erase i
    have ie : i∈univ.filter (fun w => Even (G.dist i w)) := by simp
    have quota := point i
    have ecard := card_erase_add_one ie
    change (univ.filter (fun w => Even (G.dist i w))).card≤k+1 at quota
    have emax : E.card≤k := by change ((univ.filter _).erase i).card≤k; omega
    have coverB : B⊆(P B∪E)∪T := by
      intro w wb
      by_cases port : ∃j∈S,G.Adj j w
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨wb,port⟩))
      by_cases e : G.Adj v w
      · have iw : ¬G.Adj i w := fun h => port ⟨i,si,h⟩
        have ne : i≠w := fun eq => Finset.disjoint_left.mp sides.right_cut wb (eq ▸ si)
        have two := Graph189LowDegreeTwo.two_edges (cv i si).symm e ne iw
        exact mem_union_left _ (mem_union_right _ (mem_erase.mpr ⟨ne.symm,mem_filter.mpr ⟨mem_univ _,by simp [two]⟩⟩))
      have neq : v≠w := by
        intro same
        exact port ⟨i,si,same ▸ (cv i si).symm⟩
      have lo := (hc v w).one_lt_dist_of_ne_of_not_adj neq e
      have up := radius hc sides.swap (by omega) vb cv Tsmall w wb
      exact mem_union_right _ (mem_filter.mpr ⟨wb,by omega⟩)
    have bsize := (card_le_card coverB).trans (card_union_le _ _)
    have bc := card_union_le (P B) E
    change Fintype.card V≤3*k+4
    omega
  have nonempty : (A\P A).Nonempty := card_pos.mp (by omega)
  obtain ⟨z,az⟩ := nonempty
  obtain ⟨za,np⟩ := mem_sdiff.mp az
  have nonport (i : V) (si : i∈S) : ¬G.Adj z i := fun e => np (mem_filter.mpr ⟨za,i,si,e.symm⟩)
  have xp : x∈P A := mem_filter.mpr ⟨xa,shallow x xa xh⟩
  have neq : x≠z := fun eq => np (eq ▸ xp)
  have equality : insert x (G.neighborFinset x)=A∪S := by
    apply eq_of_subset_of_card_le (incl xa)
    rw [card_insert_of_notMem (by simp),G.card_neighborFinset_eq_degree,nAS]
    omega
  have touch (w : V) (wa : w∈A∪S) (ne : w≠x) : G.Adj x w := by
    rw [←equality] at wa
    exact (G.mem_neighborFinset _ _).mp ((mem_insert.mp wa).resolve_left ne)
  have all (i : V) (si : i∈S) : G.Adj x i := touch i (mem_union_right _ si)
    (fun eq => Finset.disjoint_left.mp sides.left_cut xa (eq ▸ si))
  have xz := touch z (mem_union_left _ za) neq.symm
  have dis : Disjoint ({x,z}:Finset V) B := Finset.disjoint_left.mpr (fun a ha ab => by
    rcases (show a=x ∨ a=z by simpa using ha) with rfl|rfl
    · exact Finset.disjoint_left.mp sides.apart xa ab
    · exact Finset.disjoint_left.mp sides.apart za ab)
  have small := Graph189PortDifference.even_cover ({x,z}:Finset V) B k dis point (by
    intro w wb
    have eq := offset hc sides za xa xz.symm nonport all w wb
    by_cases he : Even (G.dist x w)
    · exact ⟨x,by simp,he⟩
    · exact ⟨z,by simp,by rw [Nat.even_iff] at he ⊢; omega⟩)
  rw [show ({x,z}:Finset V).card=2 by simp [neq]] at small
  change Fintype.card V≤3*k+4
  omega

#print axioms radius
#print axioms order
end Graph189ShallowCommonOrder
