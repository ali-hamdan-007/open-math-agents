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

/-- All but one nonport on this side are at distance two from every
anchor, provided its common port sees at least k−1 opposite-side ports. -/
theorem nonport_quota (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (two : 2≤G.vertexConnectivity) (point : ∀v,G.distEven v≤G.secondSmallestDegree+1)
    {u : V} (ua : u∈A) (common : ∀i∈S,G.Adj u i)
    (many : G.secondSmallestDegree≤(B.filter (fun v => ∃i∈S,G.Adj i v)).card+1) :
    ∃T : Finset V,T.card≤1 ∧ ∀w∈A,w∉T → (¬∃j∈S,G.Adj j w) → ∀i∈S,G.dist i w=2 := by
  classical
  let T := A.filter (fun w => G.dist u w=2)
  let P := B.filter (fun w => ∃i∈S,G.Adj i w)
  have small : T.card≤1 := by
    have dis : Disjoint T P := sides.apart.mono (filter_subset _ _) (filter_subset _ _)
    have no : u∉T∪P := by
      intro hu
      rcases mem_union.mp hu with ut|up
      · have := (mem_filter.mp ut).2
        simp at this
      · exact Finset.disjoint_left.mp sides.apart ua (mem_filter.mp up).1
    have q := Graph189TwofoldCover.outside_quota point (T∪P) no
    rw [filter_eq_self.mpr (by
      intro w hw
      rcases mem_union.mp hw with wt|wp
      · simp [(mem_filter.mp wt).2]
      · obtain ⟨wb,i,si,iw⟩ := mem_filter.mp wp
        rw [Graph189PortDifference.cross_two hc sides ua wb (common i si) iw]
        decide),card_union_of_disjoint dis] at q
    change G.secondSmallestDegree≤P.card+1 at many
    omega
  refine ⟨T,small,?_⟩
  intro w wa wt nonport i si
  have wi : w≠i := fun eq => Finset.disjoint_left.mp sides.left_cut wa (eq.symm ▸ si)
  have uw : G.Adj u w := by
    by_contra fail
    have neq : u≠w := fun eq => nonport ⟨i,si,eq ▸ (common i si).symm⟩
    have near := radius hc sides two ua common small w wa
    have far := (hc u w).one_lt_dist_of_ne_of_not_adj neq fail
    exact wt (mem_filter.mpr ⟨wa,by omega⟩)
  exact Graph189LowDegreeTwo.two_edges (common i si).symm uw wi.symm (fun h => nonport ⟨i,si,h⟩)

/-- If each side sees at least k−1 ports from a common port, the same
anchor counts all but two nonports globally, at positive even distance. -/
theorem rich_order (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (two : 2≤G.vertexConnectivity) (sz : S.card=2)
    (point : ∀v,G.distEven v≤G.secondSmallestDegree+1)
    {u v : V} (ua : u∈A) (cu : ∀i∈S,G.Adj u i) (vb : v∈B) (cv : ∀i∈S,G.Adj v i)
    (manyA : G.secondSmallestDegree≤(A.filter (fun v => ∃i∈S,G.Adj i v)).card+1)
    (manyB : G.secondSmallestDegree≤(B.filter (fun v => ∃i∈S,G.Adj i v)).card+1) :
    Fintype.card V≤3*G.secondSmallestDegree+4 := by
  classical
  let P (R : Finset V) := R.filter (fun w => ∃i∈S,G.Adj i w)
  obtain ⟨ta,sa,atA⟩ := nonport_quota hc sides two point ua cu manyB
  obtain ⟨tb,sb,atB⟩ := nonport_quota hc sides.swap two point vb cv manyA
  obtain ⟨i,si⟩ := card_pos.mp (show 0<S.card by omega)
  let E := (univ.filter (fun w => Even (G.dist i w))).erase i
  have me : i∈univ.filter (fun w => Even (G.dist i w)) := by simp
  have ecard := card_erase_add_one me
  have ec : E.card≤G.secondSmallestDegree := by
    have b := point i
    change (univ.filter (fun w => Even (G.dist i w))).card≤_ at b
    change ((univ.filter _).erase i).card≤_
    omega
  have one {R T : Finset V} (apart : Disjoint R S)
      (atR : ∀w∈R,w∉T → (¬∃j∈S,G.Adj j w) → ∀i∈S,G.dist i w=2) (w : V) (wr : w∈R) :
      w∈P R ∨ w∈T ∨ w∈E := by
    by_cases port : ∃j∈S,G.Adj j w
    · exact Or.inl (mem_filter.mpr ⟨wr,port⟩)
    by_cases wt : w∈T
    · exact Or.inr (Or.inl wt)
    have ne : w≠i := fun eq => Finset.disjoint_left.mp apart wr (eq.symm ▸ si)
    exact Or.inr (Or.inr (mem_erase.mpr ⟨ne,mem_filter.mpr ⟨mem_univ _,by simp [atR w wr wt port i si]⟩⟩))
  have cover : univ⊆(S∪(P A∪P B))∪((ta∪tb)∪E) := by
    intro w _
    rcases sides.cover w with wa|wb|ws
    · rcases one sides.left_cut atA w wa with p|t|e
      · exact mem_union_left _ (mem_union_right _ (mem_union_left _ p))
      · exact mem_union_right _ (mem_union_left _ (mem_union_left _ t))
      · exact mem_union_right _ (mem_union_right _ e)
    · rcases one sides.right_cut atB w wb with p|t|e
      · exact mem_union_left _ (mem_union_right _ (mem_union_right _ p))
      · exact mem_union_right _ (mem_union_left _ (mem_union_right _ t))
      · exact mem_union_right _ (mem_union_right _ e)
    · exact mem_union_left _ (mem_union_left _ ws)
  have n := (card_le_card cover).trans (card_union_le _ _)
  rw [card_univ] at n
  have aa := card_union_le S (P A∪P B)
  have ab := card_union_le (P A) (P B)
  have ba := card_union_le (ta∪tb) E
  have bb := card_union_le ta tb
  have pA : (P A).card≤G.secondSmallestDegree := port_bound hc sides.swap point vb cv
  have pB : (P B).card≤G.secondSmallestDegree := port_bound hc sides point ua cu
  omega

#print axioms radius
#print axioms nonport_quota
#print axioms rich_order
end Graph189ShallowCommonOrder
