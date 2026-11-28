import Graph189R1Metric

namespace Graph189HighThirdLayer

open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The vertices of degree at least the second-smallest degree at distance three from x. -/
noncomputable def highThird (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : Finset V :=
  univ.filter fun y => G.dist x y = 3 ∧ G.secondSmallestDegree ≤ G.degree y

/-- Every high root has this many high vertices at distance three, under the original
positive-even-distance bound. The vertex at distance zero is included in `distEven`. -/
theorem cover_of_high (hc : G.Connected)
    (cap : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree)
    (x : V) (hx : G.secondSmallestDegree ≤ G.degree x) :
    Fintype.card V ≤ G.degree x + G.secondSmallestDegree + 2 + (highThird G x).card := by
  classical
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  have high (y : V) (hy : y ≠ z) : G.secondSmallestDegree ≤ G.degree y := by
    rcases degree_pair (G := G) y z hy with h | h
    · exact h
    · exact h.trans (hz ▸ G.minDegree_le_degree y)
  have cap' (v : V) : G.distEven v ≤ G.secondSmallestDegree + 1 := by
    simpa only [Nat.add_comm 1] using cap v
  let E := univ.filter (fun y => Even (G.dist x y))
  let A := G.neighborFinset x
  let C := highThird G x
  have cover : (univ : Finset V) ⊆ insert z (A ∪ E ∪ C) := by
    intro y _
    by_cases hz' : y = z
    · exact mem_insert.mpr (Or.inl hz')
    apply mem_insert.mpr
    right
    by_cases he : Even (G.dist x y)
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,he⟩))
    by_cases hadj : G.Adj x y
    · exact mem_union_left _ (mem_union_left _ ((G.mem_neighborFinset x y).mpr hadj))
    have h5 := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc) (u := x) (v := y)).trans
      (diameter_le_five hc cap)
    have hne5 : G.dist x y ≠ 5 := by
      intro h
      rcases five_endpoints hc cap' x y h with h | h
      · exact (not_lt_of_ge hx) h
      · exact (not_lt_of_ge (high y hz')) h
    have hne1 : G.dist x y ≠ 1 := fun h => hadj (dist_eq_one_iff_adj.mp h)
    rw [Nat.even_iff] at he
    exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, by omega, high y hz'⟩)
  have h1 := card_le_card cover
  have h2 := Finset.card_insert_le z (A ∪ E ∪ C)
  have h3 := Finset.card_union_le (A ∪ E) C
  have h4 := Finset.card_union_le A E
  have hE : E.card ≤ 1 + G.secondSmallestDegree := cap x
  have hA : A.card = G.degree x := G.card_neighborFinset_eq_degree x
  change Fintype.card V ≤ (insert z (A ∪ E ∪ C)).card at h1
  change Fintype.card V ≤ G.degree x + G.secondSmallestDegree + 2 + C.card
  omega

/-- At every maximum-degree root, the genuine high third layer has at least
n minus the maximum degree, the second-smallest degree and two vertices. -/
theorem card_highThird_at_max (hc : G.Connected)
    (hcap : (univ.image (distEven G)).max' (by simp) ≤ 1 + G.secondSmallestDegree)
    (x : V) (hx : G.degree x = G.maxDegree) :
    Fintype.card V - G.maxDegree - G.secondSmallestDegree - 2 ≤ (highThird G x).card := by
  classical
  have cap (v : V) : G.distEven v ≤ 1 + G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans hcap
  obtain ⟨a,b,hab⟩ := exists_pair_ne V
  have kd : G.secondSmallestDegree ≤ G.maxDegree := by
    rcases degree_pair (G := G) a b hab with h | h
    · exact h.trans (G.degree_le_maxDegree a)
    · exact h.trans (G.degree_le_maxDegree b)
  have h := cover_of_high hc cap x (hx ▸ kd)
  omega

#print axioms cover_of_high
#print axioms card_highThird_at_max
end Graph189HighThirdLayer
