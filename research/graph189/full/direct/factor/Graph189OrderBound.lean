import Graph189ThirdLayer
import Graph189R1Metric

open SimpleGraph Finset Graph189ThirdLayer
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

namespace Graph189OrderBound
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Nontrivial V] [DecidableRel G.Adj] in
private theorem even_budget (x : V) (A B : Finset V) {k : ℕ}
    (cap : G.distEven x ≤ 1 + k) (hA : ∀ v∈A, G.dist x v=2)
    (hB : ∀ v∈B, G.dist x v=4) : A.card+B.card≤k := by
  classical
  have hab : Disjoint A B := Finset.disjoint_left.mpr (by
    intro v ha hb
    have h1 := hA v ha
    have h2 := hB v hb
    omega)
  have hx : x ∉ A ∪ B := by
    intro h
    rcases mem_union.mp h with ha|hb
    · simpa using hA x ha
    · simpa using hB x hb
  have hsub : insert x (A ∪ B) ⊆ univ.filter (fun v => Even (G.dist x v)) := by
    intro v hv
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rcases mem_insert.mp hv with rfl|hw
    · simp
    · rcases mem_union.mp hw with ha|hb
      · rw [hA v ha]; decide
      · rw [hB v hb]; decide
  have hs := card_le_card hsub
  rw [card_insert_of_notMem hx,card_union_of_disjoint hab] at hs
  change (univ.filter (fun v => Even (G.dist x v))).card≤1+k at cap
  omega

/-- Unconditional order estimate under the registered Graph 189 graph hypotheses. -/
theorem order_le (hc : G.Connected)
    (hcap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree) :
    Fintype.card V ≤ 1+G.minDegree+G.secondSmallestDegree+(G.secondSmallestDegree+1)^2/4 := by
  classical
  let k := G.secondSmallestDegree
  have cap (v : V) : G.distEven v ≤ 1+k :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans hcap
  have cap' (v : V) : G.distEven v ≤ G.secondSmallestDegree+1 := by
    simpa [k,Nat.add_comm] using cap v
  have bd := diameter_le_five hc cap
  have distances (u v : V) : G.dist u v ≤ 5 :=
    (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc)).trans bd
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  have high (v : V) (hv : v≠z) : k≤G.degree v := by
    rcases degree_pair (G := G) v z hv with h|h
    · exact h
    · exact h.trans (hz ▸ G.minDegree_le_degree v)
  have rootCap : (layer G z 2).card+(layer G z 4).card≤k :=
    even_budget z _ _ (cap z) (fun _ h => in_layer.mp h) (fun _ h => in_layer.mp h)
  have armCap (a : V) (ha : a∈layer G z 1) :
      (layer G a 2).card+(layer G z 5).card≤k := by
    apply even_budget a _ _ (cap a) (fun _ h => in_layer.mp h)
    intro y hy
    have h1 := in_layer.mp ha
    have h5 := in_layer.mp hy
    have ha' := high a (by rintro rfl; simp at h1)
    have hy' := high y (by rintro rfl; simp at h5)
    have ht := hc.dist_triangle (u := z) (v := a) (w := y)
    have hu := distances a y
    have hnot : G.dist a y ≠ 5 := by
      intro he
      rcases five_endpoints hc cap' a y he with h|h <;> change G.secondSmallestDegree≤_ at ha' hy' <;> omega
    omega
  have h := order_quadratic G hc z k (distances z) rootCap armCap
  have hset : layer G z 1 = G.neighborFinset z := by
    ext v
    simp [dist_eq_one_iff_adj]
  rw [hset] at h
  change Fintype.card V≤1+G.degree z+k+(k+1)^2/4 at h
  simpa [k,← hz] using h
end Graph189OrderBound
#print axioms Graph189OrderBound.order_le
