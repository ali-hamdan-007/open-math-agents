import Graph189HighThirdLayer
import Graph189RetainedWidth
import Graph189ColumnCancel

namespace Graph189RootWidth
open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

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

/-- Ceiling of the nonnegative degree-retaining wedge width at a root of degree d.
The two subtractions avoid a division over the integers. -/
def width (n k d : ℕ) : ℕ := (2*n+k*d-(4*k+k*k)+k)/(k+1)

private theorem width_le {n k d t : ℕ}
    (h : 2*n+k*d ≤ 4*k+k*k+(k+1)*t) : width n k d ≤ t := by
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < k+1)).mpr
  have hsub : 2*n+k*d-(4*k+k*k) ≤ (k+1)*t := by omega
  rw [Nat.succ_mul t (k+1), Nat.mul_comm t (k+1)]
  omega

variable [Fintype V] [DecidableEq V] [Nontrivial V] [DecidableRel G.Adj]

/-- Under the original registered Graph 189 hypotheses, the order, second-smallest
degree and maximum degree satisfy the rounded, fully cancelled root inequality. -/
theorem root_width_bound (hc : G.Connected)
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
  have cap (a : V) : G.distEven a ≤ k+1 := by
    have hh := (le_max' _ _ (mem_image_of_mem (distEven G) (mem_univ a))).trans hcap
    simpa [k,Nat.add_comm] using hh
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
    have hw := Graph189RetainedWidth.geodesic_degree_width hc hxi hij hjy (hC y hy) cap
    have hky : k ≤ G.degree y := (mem_filter.mp hy).2.2
    have hdeg := Nat.mul_le_mul_left k hky
    apply le_trans _ (Graph189ColumnCancel.geodesic_cost hc x i j y B
      (fun b hb => mem_filter.mpr ⟨mem_univ b,hb⟩) hxi hij hjy (hC y hy))
    apply width_le
    dsimp only [n]
    nlinarith only [hw,hdeg]
  have pay := Graph189ColumnCancel.full_column_cancellation hc x B C hmax large hB pred hC cap w
  have layer := Graph189HighThirdLayer.card_highThird_at_max hc hcap x hx.symm
  change n - G.maxDegree - k - 2 ≤ C.card at layer
  rw [hx] at layer ⊢
  exact (Nat.mul_le_mul_left (width n k (G.degree x)) layer).trans pay

#print axioms root_width_bound
end Graph189RootWidth
