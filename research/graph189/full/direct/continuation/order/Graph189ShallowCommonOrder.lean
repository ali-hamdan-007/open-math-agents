import Graph189CommonPortQuota
import Graph189ConnectivityDegree

open SimpleGraph Finset Graph189DeepCommonPair
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189ShallowCommonOrder
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V}

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

/-- A side without a high vertex is a degree-two singleton. -/
theorem no_high (sides : Graph189CutSides.CutSides G A B S) (sc : S.card≤G.vertexConnectivity)
    (sz : S.card=2) (high : ¬ ∃x∈A,G.secondSmallestDegree≤G.degree x) :
    ∃x∈A, G.degree x=2 := by
  classical
  push_neg at high
  obtain ⟨x,xa⟩ := sides.left_nonempty
  have ns : G.neighborFinset x⊆S := by
    intro y hy
    have e := (G.mem_neighborFinset _ _).mp hy
    rcases sides.cover y with ya|yb|ys
    · rcases degree_pair (G:=G) x y e.ne with h|h
      · exact ((not_lt_of_ge h) (high x xa)).elim
      · exact ((not_lt_of_ge h) (high y ya)).elim
    · exact (sides.no_cross x xa y yb e).elim
    · exact ys
  have bound := card_le_card ns
  rw [G.card_neighborFinset_eq_degree] at bound
  have low := Graph189CutSides.connectivity_le_degree (G:=G) x
  exact ⟨x,xa,by omega⟩

/-- A shallow side with at most k−2 ports has order at most k−1.
A high vertex attains equality in its side-plus-cut neighborhood, and
its parity row together with the low nonport counts the opposite side. -/
theorem few_ports (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (sz : S.card=2) (point : ∀v,G.distEven v≤G.secondSmallestDegree+1)
    (shallow : ∀v∈A,G.secondSmallestDegree≤G.degree v → ∃i∈S,G.Adj i v)
    (highA : ∃x∈A,G.secondSmallestDegree≤G.degree x)
    (few : (A.filter (fun v => ∃i∈S,G.Adj i v)).card+2≤G.secondSmallestDegree) :
    Fintype.card V≤3*G.secondSmallestDegree+1 := by
  classical
  let k := G.secondSmallestDegree
  let P (R : Finset V) := R.filter (fun v => ∃i∈S,G.Adj i v)
  change (P A).card+2≤k at few
  obtain ⟨x,xa,xh⟩ := highA
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
  change Fintype.card V≤3*k+1
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
  by_cases many : k≤(P A).card+1
  · obtain ⟨T,Tsmall,nearPort⟩ := nonport_quota hc sides.swap (by omega) point vb cv many
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
      by_cases wt : w∈T
      · exact mem_union_right _ wt
      have wi : w≠i := fun eq => Finset.disjoint_left.mp sides.right_cut wb (eq.symm ▸ si)
      exact mem_union_left _ (mem_union_right _ (mem_erase.mpr
        ⟨wi,mem_filter.mpr ⟨mem_univ _,by simp [nearPort w wb wt port i si]⟩⟩))
    have bsize := (card_le_card coverB).trans (card_union_le _ _)
    have bc := card_union_le (P B) E
    change Fintype.card V≤3*k+4
    omega
  have bound := few_ports hc sides sz point shallow ⟨x,xa,xh⟩ (by
    change (P A).card+2≤k
    omega)
  omega

#print axioms few_ports
#print axioms radius
#print axioms order
end Graph189ShallowCommonOrder
