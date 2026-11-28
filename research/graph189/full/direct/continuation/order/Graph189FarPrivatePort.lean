import Graph189PrivateContactProfile

open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189FarPrivatePort
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B S : Finset V} {p q : V}

private theorem second_layer (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (con : (G.induce (A:Set V)).Connected) {i : V} (si : i∈S)
    {x y : V} (xa : x∈A) (ya : y∈A) (ix : G.Adj i x) (iy : ¬G.Adj i y) :
    ∃w∈A, G.dist i w=2 := by
  obtain ⟨r⟩ := con (⟨x,xa⟩ : A) (⟨y,ya⟩ : A)
  obtain ⟨u,v,iu,iv,uv,_⟩ := Graph189CutSides.walk_exits (fun a : A => G.Adj i a.val) r ix iy
  have ne : i≠v.val := fun e => Finset.disjoint_left.mp sides.left_cut v.property (e ▸ si)
  have d1 := dist_eq_one_iff_adj.mpr iu
  have d2 := dist_eq_one_iff_adj.mpr (show G.Adj u.val v.val from uv)
  have lower := (hc i v.val).one_lt_dist_of_ne_of_not_adj ne iv
  have upper := hc.dist_triangle (u:=i) (v:=u.val) (w:=v.val)
  exact ⟨v.val,v.property,by omega⟩

/-- A high p-private port far from q bounds the entire opposite side.
The local second-layer witness is produced from the connected side A
when it has a vertex missing p (in particular, a nonport). -/
theorem order (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (con : (G.induce (A:Set V)).Connected) (pair : S={p,q}) (ne : p≠q)
    (sc : S.card≤G.vertexConnectivity) (cap : ∀w,G.distEven w≤G.secondSmallestDegree+1)
    {x : V} (xa : x∈A) (xp : G.Adj x p) (far : 3≤G.dist x q)
    (high : G.secondSmallestDegree≤G.degree x) (deep : ∃w∈A,¬G.Adj p w) :
    B.card+1≤2*G.secondSmallestDegree := by
  classical
  have ps : p∈S := by simp [pair]
  have qs : q∈S := by simp [pair]
  have sz : S.card=2 := by simp [pair,ne]
  have xq : ¬G.Adj x q := fun h => by have e := dist_eq_one_iff_adj.mpr h; omega
  obtain ⟨z,za,no⟩ := deep
  obtain ⟨w,wa,dw⟩ := second_layer hc sides con ps xa za xp.symm no
  let T := B.filter (fun y => G.dist p y=2)
  have evT (v : V) (h : v∈insert w T) : Even (G.dist p v) := by
    rcases mem_insert.mp h with rfl|h
    · simp [dw]
    · rw [(mem_filter.mp h).2]
      decide
  have pw : p∉insert w T := by
    intro h
    rcases mem_insert.mp h with rfl|pt
    · exact Finset.disjoint_left.mp sides.left_cut wa ps
    · exact Finset.disjoint_left.mp sides.right_cut (mem_filter.mp pt).1 ps
  have wt : w∉T := fun h => Finset.disjoint_left.mp sides.apart wa (mem_filter.mp h).1
  have shell := Graph189TwofoldCover.outside_quota cap (insert w T) pw
  rw [filter_eq_self.mpr evT,card_insert_of_notMem wt] at shell
  let E := B.filter (fun y => Even (G.dist x y))
  have support : Graph189PortLabels.support G S x={p} := by
    ext v
    simp only [Graph189PortLabels.support,pair,mem_filter,mem_insert,mem_singleton]
    constructor
    · rintro ⟨h,e⟩
      rcases h with h|h
      · exact h
      · subst v
        exact False.elim (xq e)
    · rintro rfl
      exact ⟨Or.inl rfl,xp⟩
  have second := Graph189BoundaryDebit.even_quota hc sides (fun D n =>
    Graph189CutSides.connected_after_smaller_deletion (G:=G) D (n.trans_le sc)) cap (Subset.rfl : B⊆B) xa
  rw [support,card_singleton,sz] at second
  change E.card+2≤G.secondSmallestDegree+1 at second
  let L := B.filter (fun y => G.degree y<G.secondSmallestDegree)
  have lowCount : L.card≤1 := by
    apply card_le_one.mpr
    intro a ha b hb
    by_contra diff
    exact (degree_pair (G:=G) a b diff).elim
      (fun h => (not_lt_of_ge h) (mem_filter.mp ha).2) (fun h => (not_lt_of_ge h) (mem_filter.mp hb).2)
  have covers : B⊆(T∪E)∪L := by
    intro y yb
    by_cases h : G.degree y<G.secondSmallestDegree
    · exact mem_union_right _ (mem_filter.mpr ⟨yb,h⟩)
    apply mem_union_left
    by_cases two : G.dist p y=2
    · exact mem_union_left _ (mem_filter.mpr ⟨yb,two⟩)
    apply mem_union_right
    refine mem_filter.mpr ⟨yb,?_⟩
    have pos (a : V) (sa : a∈S) : G.dist a y≠0 := fun e =>
      Finset.disjoint_left.mp sides.right_cut yb ((hc.dist_eq_zero_iff.mp e) ▸ sa)
    by_cases one : G.dist p y=1
    · rw [Graph189PortDifference.cross_two hc sides xa yb xp (dist_eq_one_iff_adj.mp one)]
      decide
    have eq := Graph189PrivateRepresentativeBound.cross_dist hc sides pair xa yb
    rw [dist_eq_one_iff_adj.mpr xp] at eq
    have pp := pos p ps
    have qq := pos q qs
    have upper := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc) (u:=x) (v:=y)).trans
      (diameter_le_five hc (fun v => by simpa only [Nat.add_comm] using cap v))
    have notFive : G.dist x y≠5 := fun e => (five_endpoints hc cap x y e).elim (Nat.not_lt.mpr high) h
    rw [show G.dist x y=4 by omega]
    decide
  have total := (card_le_card covers).trans (card_union_le _ _)
  have inner := card_union_le T E
  omega

#print axioms order
end Graph189FarPrivatePort
