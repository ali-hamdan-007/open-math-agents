import Graph189DeepPairData
import Graph189CleanSideCounts

open SimpleGraph Finset Graph189DeepCommonPair
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189BalancedPair
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

/-- Nonadjacent anchors force two separate contacts with either anchor in
each side once every edge is triangular. -/
theorem two_contacts (hc : G.Connected) (point : ∀v,G.distEven v≤G.secondSmallestDegree+1)
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

theorem port_count (hc : G.Connected) (point : ∀v,G.distEven v≤G.secondSmallestDegree+1)
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
    rw [four]
    decide)
  have empty : Graph189PortLabels.support G S b=∅ := eq_empty_iff_forall_notMem.mpr (by
    intro i hi
    obtain ⟨si,e⟩ := mem_filter.mp hi
    exact deep.2.2 i si e.symm)
  rw [actual,empty,card_empty,Nat.add_zero,sz] at row
  have all := cover A
  change (D A).card+2≤k at row
  omega

#print axioms port_count
end Graph189BalancedPair
