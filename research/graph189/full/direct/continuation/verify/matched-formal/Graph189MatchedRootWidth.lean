import Graph189MatchedMetric
import Graph189MatchedPack
import Graph189RootWidth
import Mathlib.Data.Finset.Max

namespace Graph189MatchedRootWidth
open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

/-- The exact integer width test, with a large-capacity fallback at D ≥ d. -/
def admissible (n k d D : ℕ) : Prop :=
  Graph189RootWidth.width n k d ≤ D ∧
    (d ≤ D ∨ (2 + (d-k) ≤ D ∧
      (2*n : ℤ) ≤ 6*k+D+Graph189MatchedPack.packed k (D-2-(d-k))))

instance (n k d D : ℕ) : Decidable (admissible n k d D) := by
  unfold admissible
  infer_instance

private def candidates (n k d : ℕ) : Finset ℕ :=
  (range (max (Graph189RootWidth.width n k d) d + 1)).filter (admissible n k d)

private theorem max_mem (n k d : ℕ) : max (Graph189RootWidth.width n k d) d ∈ candidates n k d :=
  mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_self _),le_max_left _ _,Or.inl (le_max_right _ _)⟩

/-- The first codegree allowed by the linear and matched tests. -/
def width (n k d : ℕ) : ℕ := (candidates n k d).min' ⟨_,max_mem n k d⟩

theorem width_admissible (n k d : ℕ) : admissible n k d (width n k d) :=
  (mem_filter.mp (Finset.min'_mem (candidates n k d) ⟨_,max_mem n k d⟩)).2

theorem width_le_admissible {n k d D : ℕ} (h : admissible n k d D) : width n k d ≤ D := by
  by_cases hlo : D ≤ max (Graph189RootWidth.width n k d) d
  · exact Finset.min'_le _ _ (mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hlo),h⟩)
  · exact (Finset.min'_le _ _ (max_mem n k d)).trans (by omega)

private theorem linear_width_le {n k d D : ℕ}
    (h : 2*n+k*d ≤ 4*k+k*k+(k+1)*D) : Graph189RootWidth.width n k d ≤ D := by
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < k+1)).mpr
  have hsub : 2*n+k*d-(4*k+k*k) ≤ (k+1)*D := by omega
  rw [Nat.succ_mul D (k+1), Nat.mul_comm D (k+1)]
  omega

variable {V : Type*} {G : SimpleGraph V}

private theorem predecessor {x z : V} {j : ℕ} (hz : G.dist x z = j+1) :
    ∃ a, G.dist x a = j ∧ G.Adj a z := by
  have hr : G.dist z x = j+1 := by rwa [dist_comm]
  have hp : G.Reachable z x := Reachable.of_dist_ne_zero (by omega)
  obtain ⟨walk,hlen⟩ := hp.exists_walk_length_eq_dist
  cases walk with
  | nil => simp at hz
  | cons he tail =>
    rename_i a
    have ht : tail.length = j := by rw [Walk.length_cons,hr] at hlen; omega
    have hh : G.dist x a ≤ j := by rw [dist_comm]; exact ht ▸ G.dist_le tail
    have := he.diff_dist_adj (u := x)
    exact ⟨a,by omega,he.symm⟩

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private theorem union_lower {a b c : V} (hab : G.Adj b a) (hbc : G.Adj b c)
    (hne : a ≠ c) (hac : ¬G.Adj a c) :
    G.degree a + G.degree c + 2 ≤
      (G.neighborFinset b ∪ (G.neighborFinset a ∪ G.neighborFinset c)).card +
      (G.neighborFinset a ∩ G.neighborFinset c).card := by
  classical
  let S := G.neighborFinset a ∪ G.neighborFinset c
  have ha : a ∉ S := by
    intro h
    rcases Finset.mem_union.mp h with h|h
    · exact G.loopless.irrefl a ((G.mem_neighborFinset _ _).mp h)
    · exact hac ((G.mem_neighborFinset _ _).mp h).symm
  have hc : c ∉ S := by simp [S, G.mem_neighborFinset, hac]
  have ha' : a ∉ insert c S := by simp [hne, ha]
  have sub : insert a (insert c S) ⊆ G.neighborFinset b ∪ S := by
    intro u hu
    rcases mem_insert.mp hu with rfl|hu
    · exact mem_union_left _ ((G.mem_neighborFinset _ _).mpr hab)
    rcases mem_insert.mp hu with rfl|hu
    · exact mem_union_left _ ((G.mem_neighborFinset _ _).mpr hbc)
    · exact mem_union_right _ hu
  have h := card_le_card sub
  rw [card_insert_of_notMem ha', card_insert_of_notMem hc] at h
  have hh := card_union_add_card_inter (G.neighborFinset a) (G.neighborFinset c)
  rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at hh
  change S.card + _ = _ at hh
  change _ ≤ (G.neighborFinset b ∪ S).card + _
  omega

/-- The two endpoint codegrees of a three-edge geodesic supply its width. -/
def codegreeSum (G : SimpleGraph V) [DecidableRel G.Adj] (x i j y : V) : ℕ :=
  (G.neighborFinset x ∩ G.neighborFinset j).card + (G.neighborFinset y ∩ G.neighborFinset i).card

variable [Nontrivial V]

/-- Both ordinary and matched order estimates hold on genuine consecutive wedges. -/
theorem geodesic_admissible (hc : G.Connected) {x i j y : V}
    (hxi : G.Adj x i) (hij : G.Adj i j) (hjy : G.Adj j y) (hxy : G.dist x y = 3)
    (hcap : ∀ v, G.distEven v ≤ 1+G.secondSmallestDegree)
    (hhighx : G.secondSmallestDegree ≤ G.degree x)
    (hhighy : G.secondSmallestDegree ≤ G.degree y) :
    admissible (Fintype.card V) G.secondSmallestDegree (G.degree x) (codegreeSum G x i j y) := by
  let k := G.secondSmallestDegree
  let D := codegreeSum G x i j y
  let n := Fintype.card V
  have cap (v : V) : G.distEven v ≤ k+1 := by simpa only [k,Nat.add_comm 1] using hcap v
  have dx := hc.dist_triangle (u:=x) (v:=i) (w:=y)
  have dy := hc.dist_triangle (u:=x) (v:=j) (w:=y)
  rw [hxy, dist_eq_one_iff_adj.mpr hxi] at dx
  rw [hxy, dist_eq_one_iff_adj.mpr hjy] at dy
  have nxj : ¬G.Adj x j := by
    intro hh
    rw [dist_eq_one_iff_adj.mpr hh] at dy
    omega
  have nyi : ¬G.Adj y i := by
    intro hh
    rw [dist_eq_one_iff_adj.mpr hh.symm] at dx
    omega
  have hxj : x ≠ j := by rintro rfl; simp at dy
  have hyi : y ≠ i := by rintro rfl; simp at dx
  change admissible n k (G.degree x) D
  refine ⟨?_, ?_⟩
  · have hw := Graph189RetainedWidth.geodesic_degree_width hc hxi hij hjy hxy cap
    have hdeg := Nat.mul_le_mul_left k hhighy
    apply linear_width_le
    change 2*n+k*(G.degree x+G.degree y) ≤ 4*k+2*k*k+(k+1)*D at hw
    nlinarith only [hw,hdeg]
  by_cases hD : G.degree x ≤ D
  · exact Or.inl hD
  obtain ⟨t₁,ε₁,_,hcap₁,hord₁⟩ := Graph189MatchedWedge.wedge_order_graph189 hc hxi.symm hij hxj hcap
  obtain ⟨t₂,ε₂,_,hcap₂,hord₂⟩ := Graph189MatchedWedge.wedge_order_graph189 hc hjy hij.symm hyi hcap
  have u₁ := union_lower hxi.symm hij hxj nxj
  have u₂ := union_lower hjy hij.symm hyi nyi
  have ei := cap i
  have ej := cap j
  let K := D-2-(G.degree x-k)
  have hcapacity : t₁+t₂+ε₁+ε₂+2+(G.degree x-k) ≤ D := by
    dsimp [D,codegreeSum]
    change k ≤ G.degree x at hhighx
    change k ≤ G.degree y at hhighy
    omega
  have hsmall : K+3 ≤ k := by
    change k ≤ G.degree x at hhighx
    dsimp only [K]
    omega
  have hfit : t₁+t₂+ε₁+ε₂ ≤ K := by dsimp only [K]; omega
  have horder : 2*n+t₁*(t₁+1)+t₂*(t₂+1) ≤ 6*k+D+t₁*k+t₂*k+ε₁+ε₂ := by
    change Fintype.card V + _ + _ ≤ 3*k+2+_+_+t₁*k+ε₁ at hord₁
    change Fintype.card V + _ + _ ≤ 3*k+2+_+_+t₂*k+ε₂ at hord₂
    dsimp [n,D,codegreeSum]
    omega
  have horderI : (2*n : ℤ)+(t₁ : ℤ)*((t₁ : ℤ)+1)+(t₂ : ℤ)*((t₂ : ℤ)+1) ≤
      6*k+D+(t₁ : ℤ)*k+(t₂ : ℤ)*k+ε₁+ε₂ := by exact_mod_cast horder
  have packed := Graph189MatchedPack.le_packed hsmall hfit
  refine Or.inr ⟨by omega,?_⟩
  change (2*n : ℤ) ≤ 6*k+D+Graph189MatchedPack.packed k K
  unfold Graph189MatchedPack.score at packed
  nlinarith only [horderI,packed]

/-- The maximum-degree root satisfies the exact matched width inequality used by the
64-band replay under the unmodified Graph 189 even-distance hypothesis. -/
theorem root_matched_width_bound (hc : G.Connected)
    (hcap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree) :
    width (Fintype.card V) G.secondSmallestDegree G.maxDegree *
      (Fintype.card V - G.maxDegree - G.secondSmallestDegree - 2) ≤
        G.secondSmallestDegree * G.maxDegree := by
  classical
  let k := G.secondSmallestDegree
  let n := Fintype.card V
  obtain ⟨x,hx⟩ := G.exists_maximal_degree_vertex
  let B := univ.filter (fun b => G.dist x b = 2)
  let C := Graph189HighThirdLayer.highThird G x
  have hmax (a : V) : G.degree a ≤ G.degree x := hx ▸ G.degree_le_maxDegree a
  obtain ⟨p,q,hpq⟩ := exists_pair_ne V
  have large : k ≤ G.degree x := by
    rcases degree_pair (G := G) p q hpq with hp | hq
    · exact hp.trans (hmax p)
    · exact hq.trans (hmax q)
  have cap₀ (a : V) : G.distEven a ≤ 1+k :=
    (le_max' _ _ (mem_image_of_mem (distEven G) (mem_univ a))).trans hcap
  have cap (a : V) : G.distEven a ≤ k+1 := by simpa only [Nat.add_comm 1] using cap₀ a
  have hB (b : V) (hb : b ∈ B) : G.dist x b = 2 := (mem_filter.mp hb).2
  have pred (b : V) (hb : b ∈ B) : ∃ i, G.Adj x i ∧ G.Adj i b := by
    obtain ⟨i,hi,hb'⟩ := predecessor (j := 1) (hB b hb)
    exact ⟨i, dist_eq_one_iff_adj.mp hi, hb'⟩
  have hC (y : V) (hy : y ∈ C) : G.dist x y = 3 := (mem_filter.mp hy).2.1
  have w (y : V) (hy : y ∈ C) :
      width n k (G.degree x) ≤ ((G.neighborFinset x).filter (fun a => G.dist a y = 2)).card +
        (B.filter (fun b => G.Adj b y)).card := by
    obtain ⟨j,hj,hjy⟩ := predecessor (j := 2) (hC y hy)
    obtain ⟨i,hi,hij⟩ := predecessor (j := 1) hj
    have hxi := dist_eq_one_iff_adj.mp hi
    have hky : k ≤ G.degree y := (mem_filter.mp hy).2.2
    exact (width_le_admissible (geodesic_admissible hc hxi hij hjy (hC y hy) cap₀ large hky)).trans
      (Graph189ColumnCancel.geodesic_cost hc x i j y B
        (fun b hb => mem_filter.mpr ⟨mem_univ b,hb⟩) hxi hij hjy (hC y hy))
  have pay := Graph189ColumnCancel.full_column_cancellation hc x B C hmax large hB pred hC cap w
  have layer := Graph189HighThirdLayer.card_highThird_at_max hc hcap x hx.symm
  change n - G.maxDegree - k - 2 ≤ C.card at layer
  rw [hx] at layer ⊢
  exact (Nat.mul_le_mul_left (width n k (G.degree x)) layer).trans pay

#print axioms geodesic_admissible
#print axioms root_matched_width_bound
end Graph189MatchedRootWidth
