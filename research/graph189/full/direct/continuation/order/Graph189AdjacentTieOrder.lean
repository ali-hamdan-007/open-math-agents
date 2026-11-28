import Graph189TwofoldCover
import Graph189DistanceLayers
import Graph189BoundaryDebit

open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189AdjacentPrivateCut
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

theorem high_range (hc : G.Connected) (cap : ∀v,G.distEven v≤G.secondSmallestDegree+1)
    {x y : V} (xh : G.secondSmallestDegree≤G.degree x) (yh : G.secondSmallestDegree≤G.degree y) :
    G.dist x y≤4 := by
  have bound := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc) (u:=x) (v:=y)).trans
    (diameter_le_five hc (fun v => by simpa only [Nat.add_comm] using cap v))
  have ne : G.dist x y≠5 := by
    intro eq
    rcases five_endpoints hc cap x y eq with h|h
    · exact (not_lt_of_ge xh) h
    · exact (not_lt_of_ge yh) h
  omega

/-- A private port sees all opposite vertices at odd equal anchor depth
at even distance, including vertices beyond the first two layers. -/
theorem order (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (sep : S={p,q}) (edge : G.Adj p q) (cap : ∀v,G.distEven v≤G.secondSmallestDegree+1)
    {u : V} (ua : u∈A) (up : G.Adj u p) (uq : ¬G.Adj u q)
    (few : ∀x∈A, G.dist p x=G.dist q x → ¬Even (G.dist p x) → G.degree x<G.secondSmallestDegree) :
    Fintype.card V≤3*G.secondSmallestDegree+2 := by
  classical
  let k := G.secondSmallestDegree
  let T := B.filter (fun x => G.dist p x=G.dist q x ∧ ¬Even (G.dist p x))
  let L := univ.filter (fun x => G.degree x<k)
  let E (r : V) := univ.filter (fun x => Even (G.dist r x))
  have ps : p∈S := by simp [sep]
  have qs : q∈S := by simp [sep]
  have eq (a : V) (sa : a∈S) : a=p ∨ a=q := by simpa [sep] using sa
  have inT {x : V} (xh : x∈T) : Even (G.dist u x) := by
    obtain ⟨xb,depth,odd⟩ := mem_filter.mp xh
    obtain ⟨w,len⟩ := (hc u x).exists_walk_length_eq_dist
    obtain ⟨a,sa,hit⟩ := sides.meets ua xb w
    have wt := congrArg Walk.length (Walk.take_spec w hit)
    rw [Walk.length_append] at wt
    have lower := G.dist_le (w.takeUntil a hit)
    have last := G.dist_le (w.dropUntil a hit)
    have positive : G.dist u a≠0 := fun h => Finset.disjoint_left.mp sides.left_cut ua ((hc.dist_eq_zero_iff.mp h).symm ▸ sa)
    have same : G.dist a x=G.dist p x := (eq a sa).elim (by rintro rfl; rfl) (by rintro rfl; exact depth.symm)
    have hi := hc.dist_triangle (u:=u) (v:=p) (w:=x)
    rw [dist_eq_one_iff_adj.mpr up] at hi
    rw [Nat.even_iff] at odd ⊢
    omega
  have nq : q∉T := fun h => Finset.disjoint_left.mp sides.right_cut (mem_filter.mp h).1 qs
  have nu : u∉insert q T := by
    intro h
    rcases mem_insert.mp h with rfl|hu
    · exact Finset.disjoint_left.mp sides.left_cut ua qs
    · exact Finset.disjoint_left.mp sides.apart ua (mem_filter.mp hu).1
  have quota := Graph189TwofoldCover.outside_quota cap (insert q T) nu
  rw [filter_eq_self.mpr (by
    intro x hx
    rcases mem_insert.mp hx with h|h
    · subst x
      have ne : u≠q := fun e => Finset.disjoint_left.mp sides.left_cut ua (e.symm ▸ qs)
      rw [Graph189LowDegreeTwo.two_edges up edge ne uq]
      decide
    · exact inT h),card_insert_of_notMem nq] at quota
  have low : L.card≤1 := card_le_one.mpr (by
    intro a ha b hb
    by_contra ne
    rcases degree_pair (G:=G) a b ne with h|h
    · exact (not_lt_of_ge h) (mem_filter.mp ha).2
    · exact (not_lt_of_ge h) (mem_filter.mp hb).2)
  have covers : univ ⊆ ((E p∪E q)∪T)∪L := by
    intro x _
    by_cases pe : Even (G.dist p x)
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem_univ _,pe⟩)))
    by_cases qe : Even (G.dist q x)
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,qe⟩)))
    have h1 := hc.dist_triangle (u:=p) (v:=q) (w:=x)
    have h2 := hc.dist_triangle (u:=q) (v:=p) (w:=x)
    rw [dist_eq_one_iff_adj.mpr edge] at h1
    rw [dist_eq_one_iff_adj.mpr edge.symm] at h2
    have same : G.dist p x=G.dist q x := by
      rw [Nat.even_iff] at pe qe
      omega
    rcases sides.cover x with a|b|s
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,few x a same pe⟩)
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨b,same,pe⟩))
    · rcases eq x s with rfl|rfl
      · simp at pe
      · simp at qe
  have total := (card_le_card covers).trans (card_union_le _ _)
  rw [card_univ] at total
  have h1 := card_union_le (E p∪E q) T
  have h2 := card_union_le (E p) (E q)
  have ep : (E p).card≤k+1 := cap p
  have eq' : (E q).card≤k+1 := cap q
  change T.card+1≤k at quota
  change Fintype.card V≤3*k+2
  omega

#print axioms order
end Graph189AdjacentPrivateCut
