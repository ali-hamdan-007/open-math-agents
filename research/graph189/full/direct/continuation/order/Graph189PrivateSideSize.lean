import Graph189BoundaryDebit
import Graph189PrivateRepresentativeBound
import Graph189MinimumCutOrder

open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189PrivateSideSize
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

/-- A common-free side contains disjoint contacts of the two anchors.
One is high and has at most one neighbor on the separator. -/
theorem order (sides : Graph189CutSides.CutSides G A B S) (pair : S={p,q})
    (sc : S.card≤G.vertexConnectivity) (free : ∀x∈A,¬(G.Adj x p ∧ G.Adj x q)) :
    G.secondSmallestDegree≤A.card := by
  classical
  have sideSize (x : V) (ax : x∈A) (high : G.secondSmallestDegree≤G.degree x) :
      G.secondSmallestDegree≤A.card := by
    have priv : ¬G.Adj x p ∨ ¬G.Adj x q := by
      by_cases xp : G.Adj x p
      · exact Or.inr (fun xq => free x ax ⟨xp,xq⟩)
      · exact Or.inl xp
    have cutBound (i j : V) (members : ∀w∈S,w=i ∨ w=j) (miss : ¬G.Adj x j) :
        G.degree x≤A.card := by
      have inc : G.neighborFinset x⊆insert i (A.erase x) := by
        intro w hw
        have e := (G.mem_neighborFinset _ _).mp hw
        rcases sides.cover w with aw|bw|sw
        · exact mem_insert_of_mem (mem_erase.mpr ⟨e.ne.symm,aw⟩)
        · exact (sides.no_cross x ax w bw e).elim
        · rcases members w sw with rfl|rfl
          · exact mem_insert_self _ _
          · exact (miss e).elim
      have h := (card_le_card inc).trans (card_insert_le i _)
      rw [G.card_neighborFinset_eq_degree] at h
      have er := card_erase_add_one ax
      omega
    have members (w : V) (sw : w∈S) : w=p ∨ w=q := by simpa [pair] using sw
    rcases priv with l|r
    · exact high.trans (cutBound q p (fun w sw => (members w sw).symm) l)
    · exact high.trans (cutBound p q members r)
  have contact (i : V) (si : i∈S) := (sides.contacts_of_minimum (fun T h =>
    Graph189CutSides.connected_after_smaller_deletion (G:=G) T (h.trans_le sc)) si).1
  obtain ⟨u,ua,up⟩ := contact p (by simp [pair])
  obtain ⟨v,va,vq⟩ := contact q (by simp [pair])
  have diff : u≠v := by rintro rfl; exact free u ua ⟨up,vq⟩
  exact (degree_pair (G:=G) u v diff).elim (sideSize u ua) (sideSize v va)

/-- Every vertex far from both anchors on the opposite side has degree
strictly below k. It suffices that the near side contains at least k vertices. -/
theorem far_low_of_size (hc : G.Connected) (cap : ∀v,G.distEven v≤G.secondSmallestDegree+1)
    (sides : Graph189CutSides.CutSides G A B S) (pair : S={p,q}) (ne : p≠q)
    (sc : S.card≤G.vertexConnectivity) (bigA : G.secondSmallestDegree≤A.card)
    {y : V} (yb : y∈B) (yp : 3≤G.dist p y) (yq : 3≤G.dist q y) :
    G.degree y<G.secondSmallestDegree := by
  classical
  let H := A.filter (fun x => G.secondSmallestDegree≤G.degree x)
  let L := univ.filter (fun x => G.degree x<G.secondSmallestDegree)
  have few : L.card≤1 := by
    apply card_le_one.mpr
    intro x hx y hy
    by_contra diff
    rcases degree_pair (G:=G) x y diff with h|h
    · exact (not_lt_of_ge h) (mem_filter.mp hx).2
    · exact (not_lt_of_ge h) (mem_filter.mp hy).2
  have size : S.card=2 := by simp [pair,ne]
  have ps : p∈S := by simp [pair]
  have qs : q∈S := by simp [pair]
  by_contra! high
  have all : H.filter (fun w => Even (G.dist y w))=H := filter_eq_self.mpr (by
    intro x hx
    obtain ⟨xa,xh⟩ := mem_filter.mp hx
    have pos (i : V) (si : i∈S) : G.dist x i≠0 := fun e =>
      Finset.disjoint_left.mp sides.left_cut xa ((hc.dist_eq_zero_iff.mp e).symm ▸ si)
    have eq := Graph189PrivateRepresentativeBound.cross_dist hc sides pair xa yb
    have diameter := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc) (u:=x) (v:=y)).trans
      (diameter_le_five hc (fun w => by simpa only [Nat.add_comm] using cap w))
    have nonfive : G.dist x y≠5 := fun e =>
      (five_endpoints hc cap x y e).elim (Nat.not_lt.mpr xh) (Nat.not_lt.mpr high)
    have xp := pos p ps
    have xq := pos q qs
    rw [G.dist_comm (u:=y) (v:=x),show G.dist x y=4 by omega]
    decide)
  have support : Graph189PortLabels.support G S y=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨si,e⟩ := mem_filter.mp hi
    have d := dist_eq_one_iff_adj.mpr e.symm
    rcases (show i=p ∨ i=q by simpa [pair] using si) with rfl|rfl <;> omega
  have bd := Graph189BoundaryDebit.even_quota hc sides.swap (fun T ht =>
    Graph189CutSides.connected_after_smaller_deletion (G:=G) T (ht.trans_le sc)) cap
    (show H⊆A from filter_subset _ _) yb
  rw [all,support,size,card_empty,Nat.add_zero] at bd
  have lowA : A\H⊆L := by
    intro w hw
    exact mem_filter.mpr ⟨mem_univ _,lt_of_not_ge (fun h => (mem_sdiff.mp hw).2 (mem_filter.mpr ⟨(mem_sdiff.mp hw).1,h⟩))⟩
  have fewA := (card_le_card lowA).trans few
  have tot := card_sdiff_add_card_eq_card (show H⊆A from filter_subset _ _)
  omega

theorem far_low (hc : G.Connected) (cap : ∀v,G.distEven v≤G.secondSmallestDegree+1)
    (sides : Graph189CutSides.CutSides G A B S) (pair : S={p,q}) (ne : p≠q)
    (sc : S.card≤G.vertexConnectivity) (free : ∀x∈A,¬(G.Adj x p ∧ G.Adj x q))
    {y : V} (yb : y∈B) (yp : 3≤G.dist p y) (yq : 3≤G.dist q y) :
    G.degree y<G.secondSmallestDegree :=
  far_low_of_size hc cap sides pair ne sc (order sides pair sc free) yb yp yq

#print axioms far_low_of_size
#print axioms order
#print axioms far_low
end Graph189PrivateSideSize
