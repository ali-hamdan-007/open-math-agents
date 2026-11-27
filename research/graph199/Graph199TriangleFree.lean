import Graph199BipartiteOrder
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Sum

namespace Graph199TriangleFree

open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1
open OMA.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1_H2_R1

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]

theorem degree_add_one_le_tree_order (hG : G.CliqueFree 3) (v : V) :
    G.degree v + 1 ≤ largestInducedTreeSize G := by
  have h := star_bound v (G.neighborFinset v)
    (by simpa using G.isIndepSet_neighborSet_of_triangleFree hG v)
    (fun w hw => (G.mem_neighborFinset v w).mp hw)
  rwa [G.card_neighborFinset_eq_degree] at h

theorem degree_eq_connectivity_or_succ (hG : G.CliqueFree 3)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) (v : V) :
    G.degree v = vertexConnectivity G ∨ G.degree v = vertexConnectivity G + 1 := by
  have hmin := Graph199BipartiteOrder.vertexConnectivity_le_degree (G:=G) v
  have hmax := degree_add_one_le_tree_order hG v
  omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem neighbors_not_adj (hG : G.CliqueFree 3)
    {u x y : V} (hx : G.Adj u x) (hy : G.Adj u y) : ¬ G.Adj x y :=
  fun hxy => G.isIndepSet_neighborSet_of_triangleFree hG u hx hy hxy.ne hxy

/-- The neighbors of one end of an edge that do not extend the edge to a
square are limited by the degree at the other end. -/
theorem square_exceptions_card_add_degree_le (hG : G.CliqueFree 3) {u v : V}
    (huv : G.Adj u v) :
    ((G.neighborFinset v).erase u |>.filter fun y =>
      ¬ ∃ x ∈ (G.neighborFinset u).erase v, G.Adj x y).card + G.degree u + 1 ≤
      largestInducedTreeSize G := by
  classical
  let S := (G.neighborFinset u).erase v
  let T := ((G.neighborFinset v).erase u).filter fun y => ¬ ∃ x ∈ S, G.Adj x y
  change T.card + G.degree u + 1 ≤ _
  have hs (x : V) (hx : x ∈ S) : G.Adj u x ∧ ¬ G.Adj v x := by
    have hux := (G.mem_neighborFinset u x).mp (mem_erase.mp hx).2
    exact ⟨hux, neighbors_not_adj hG huv hux⟩
  have ht (y : V) (hy : y ∈ T) : G.Adj v y ∧ ¬ G.Adj u y := by
    have hvy := (G.mem_neighborFinset v y).mp (mem_erase.mp (mem_filter.mp hy).1).2
    exact ⟨hvy, neighbors_not_adj hG huv.symm hvy⟩
  have hiS : G.IsIndepSet (S : Set V) := by
    intro x hx y hy _
    exact neighbors_not_adj hG (hs x hx).1 (hs y hy).1
  have hiT : G.IsIndepSet (T : Set V) := by
    intro x hx y hy _
    exact neighbors_not_adj hG (ht x hx).1 (ht y hy).1
  have hst (x : V) (hx : x ∈ S) (y : V) (hy : y ∈ T) : x ≠ y ∧ ¬ G.Adj x y :=
    ⟨fun e => (ht y hy).2 (e ▸ (hs x hx).1), fun h => (mem_filter.mp hy).2 ⟨x,hx,h⟩⟩
  have h := double_star_bound u v huv S T hiS hiT hst hs ht (by simp [S]) (by simp [T])
  have hcard : S.card + 1 = G.degree u := by
    rw [← G.card_neighborFinset_eq_degree]
    exact card_erase_add_one ((G.mem_neighborFinset u v).mpr huv)
  omega

theorem square_exceptions_at_most_one (hG : G.CliqueFree 3)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) {u v : V}
    (huv : G.Adj u v) :
    ((G.neighborFinset v).erase u |>.filter fun y =>
      ¬ ∃ x ∈ (G.neighborFinset u).erase v, G.Adj x y).card ≤ 1 := by
  have h := square_exceptions_card_add_degree_le hG huv
  have hmin := Graph199BipartiteOrder.vertexConnectivity_le_degree (G:=G) u
  omega

/-- Around any vertex, the pairs whose only common neighbor is that
vertex form a matching. In particular a given neighbor has at most one partner. -/
theorem unique_common_neighbor_partner (hG : G.CliqueFree 3)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) {u v y z : V}
    (huv : G.Adj u v) (hvy : G.Adj v y) (hvz : G.Adj v z)
    (hyu : y ≠ u) (hzu : z ≠ u)
    (hy : ∀ x, G.Adj u x → G.Adj y x → x = v)
    (hz : ∀ x, G.Adj u x → G.Adj z x → x = v) :
    y = z := by
  classical
  have hmem (a : V) (hva : G.Adj v a) (hau : a ≠ u)
      (ha : ∀ x, G.Adj u x → G.Adj a x → x = v) :
      a ∈ ((G.neighborFinset v).erase u |>.filter fun b =>
        ¬ ∃ x ∈ (G.neighborFinset u).erase v, G.Adj x b) := by
    refine mem_filter.mpr ⟨mem_erase.mpr ⟨hau, (G.mem_neighborFinset v a).mpr hva⟩, ?_⟩
    rintro ⟨x,hx,hxa⟩
    exact (mem_erase.mp hx).1 (ha x ((G.mem_neighborFinset u x).mp (mem_erase.mp hx).2)
      hxa.symm)
  exact card_le_one_iff.mp (square_exceptions_at_most_one hG ht huv)
    (hmem y hvy hyu hy) (hmem z hvz hzu hz)

/-- The square matching at an edge. Values in the finite right summand are
the only possible unmatched neighbors on the left. -/
theorem square_matching_with_deficiency (hG : G.CliqueFree 3) {u v : V}
    (huv : G.Adj u v) {k : ℕ} (ht : largestInducedTreeSize G ≤ k + 2) :
    let A := (G.neighborFinset u).erase v
    let B := (G.neighborFinset v).erase u
    ∃ f : B → V ⊕ Fin (k - A.card), Function.Injective f ∧
      ∀ b : B, ∀ a : V, f b = Sum.inl a → a ∈ A ∧ G.Adj a b := by
  classical
  dsimp only
  let A := (G.neighborFinset u).erase v
  let B := (G.neighborFinset v).erase u
  let d := k - A.card
  let R (b : B) (w : V ⊕ Fin d) : Prop :=
    match w with
    | .inl a => a ∈ A ∧ G.Adj a b
    | .inr _ => True
  have hHall : ∀ X : Finset B, X.card ≤ (univ.filter fun w => ∃ b ∈ X, R b w).card := by
    intro X
    by_cases hx : X = ∅
    · simp [hx]
    let Y := A.filter fun a => ∃ b ∈ X, G.Adj a b
    let S := A \ Y
    let T := X.map ⟨Subtype.val, Subtype.val_injective⟩
    have hs (a : V) (ha : a ∈ S) : G.Adj u a ∧ ¬ G.Adj v a := by
      have hua := (G.mem_neighborFinset u a).mp (mem_erase.mp (mem_sdiff.mp ha).1).2
      exact ⟨hua, neighbors_not_adj hG huv hua⟩
    have hT (b : V) (hb : b ∈ T) : b ∈ B := by
      obtain ⟨z, _, rfl⟩ := mem_map.mp hb
      exact z.property
    have hp (b : V) (hb : b ∈ T) : G.Adj v b ∧ ¬ G.Adj u b := by
      have hvb := (G.mem_neighborFinset v b).mp (mem_erase.mp (hT b hb)).2
      exact ⟨hvb, neighbors_not_adj hG huv.symm hvb⟩
    have hSInd : G.IsIndepSet (S : Set V) := by
      intro a ha a' ha' _
      exact neighbors_not_adj hG (hs a ha).1 (hs a' ha').1
    have hTInd : G.IsIndepSet (T : Set V) := by
      intro b hb b' hb' _
      exact neighbors_not_adj hG (hp b hb).1 (hp b' hb').1
    have hst (a : V) (ha : a ∈ S) (b : V) (hb : b ∈ T) : a ≠ b ∧ ¬ G.Adj a b := by
      refine ⟨fun he => (hp b hb).2 (he ▸ (hs a ha).1), ?_⟩
      intro hab
      obtain ⟨z,hz,rfl⟩ := mem_map.mp hb
      exact (mem_sdiff.mp ha).2 (mem_filter.mpr ⟨(mem_sdiff.mp ha).1, z, hz, hab⟩)
    have hSv : v ∉ S := fun h => (mem_erase.mp (mem_sdiff.mp h).1).1 rfl
    have hTu : u ∉ T := fun h => (mem_erase.mp (hT u h)).1 rfl
    have hc := (double_star_bound u v huv S T hSInd hTInd hst hs hp hSv hTu).trans ht
    have htcard : T.card = X.card := card_map _
    have hpart : S.card + Y.card = A.card :=
      card_sdiff_add_card_eq_card (filter_subset _ _)
    have he : (univ.filter fun w => ∃ b ∈ X, R b w) = Y.disjSum (univ : Finset (Fin d)) := by
      ext w
      cases w with
      | inl a =>
        simp only [mem_filter, mem_univ, true_and, inl_mem_disjSum, Y, R]
        constructor
        · rintro ⟨b,hb,ha,hab⟩
          exact ⟨ha,b,hb,hab⟩
        · rintro ⟨ha,b,hb,hab⟩
          exact ⟨b,hb,ha,hab⟩
      | inr z =>
        obtain ⟨b,hb⟩ := Finset.nonempty_iff_ne_empty.mpr hx
        exact iff_of_true (mem_filter.mpr ⟨mem_univ _, b, hb, trivial⟩)
          (inr_mem_disjSum.mpr (mem_univ _))
    rw [he,card_disjSum,card_univ,Fintype.card_fin]
    change X.card ≤ Y.card + (k - A.card)
    omega
  let row (b : B) : Finset (V ⊕ Fin d) := univ.filter (R b)
  have hHall' (X : Finset B) : X.card ≤ (X.biUnion row).card := by
    have he : X.biUnion row = univ.filter (fun w => ∃ b ∈ X, R b w) := by
      ext w
      simp [row]
    rw [he]
    exact hHall X
  obtain ⟨f,hf,hR⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' row).mp hHall'
  refine ⟨f,hf,?_⟩
  intro b a he
  have h := (mem_filter.mp (hR b)).2
  rw [he] at h
  exact h

/-- An edge is in a family of induced squares with pairwise disjoint
additional vertices. The lower bound is the sum of the two neighborhood
sizes after deleting the opposite endpoints, minus the tree allowance. -/
theorem square_matching (hG : G.CliqueFree 3) {u v : V}
    (huv : G.Adj u v) {k : ℕ} (ht : largestInducedTreeSize G ≤ k + 2) :
    let A := (G.neighborFinset u).erase v
    let B := (G.neighborFinset v).erase u
    ∃ S : Finset B, A.card + B.card - k ≤ S.card ∧
      ∃ f : S ↪ A, ∀ b : S, G.Adj (f b : V) ((b : B) : V) := by
  classical
  dsimp only
  let A := (G.neighborFinset u).erase v
  let B := (G.neighborFinset v).erase u
  let d := k - A.card
  obtain ⟨f,hf,hAdj⟩ := square_matching_with_deficiency hG huv ht
  let S : Finset B := univ.filter fun b => ∃ a : V, f b = Sum.inl a
  let T : Finset B := univ \ S
  let R : Finset (V ⊕ Fin d) := (∅ : Finset V).disjSum univ
  have hsub : T.image f ⊆ R := by
    intro w hw
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hw
    have hn : b ∉ S := (mem_sdiff.mp hb).2
    cases he : f b with
    | inl a => exact (hn (mem_filter.mpr ⟨mem_univ _, a, he⟩)).elim
    | inr r => exact inr_mem_disjSum.mpr (mem_univ _)
  have hT := card_le_card hsub
  rw [card_image_of_injective _ hf,card_disjSum,card_empty,zero_add,card_univ,Fintype.card_fin] at hT
  have hpart : T.card + S.card = B.card := by
    rw [card_sdiff_add_card_eq_card (subset_univ S),card_univ,Fintype.card_coe]
  have hA : A.card ≤ k := by
    have hd : A.card + 1 = G.degree u := by
      rw [← G.card_neighborFinset_eq_degree]
      exact card_erase_add_one ((G.mem_neighborFinset u v).mpr huv)
    have h := degree_add_one_le_tree_order hG u
    omega
  have hsz : A.card + B.card - k ≤ S.card := by
    change T.card ≤ k - A.card at hT
    omega
  have hchoose (b : S) : ∃ a : V, f b = Sum.inl a := (mem_filter.mp b.property).2
  let g (b : S) : A :=
    ⟨Classical.choose (hchoose b), (hAdj b _ (Classical.choose_spec (hchoose b))).1⟩
  have hg : Function.Injective g := by
    intro b c he
    apply Subtype.ext
    apply hf
    rw [Classical.choose_spec (hchoose b), Classical.choose_spec (hchoose c)]
    exact congrArg (fun a : A => Sum.inl (a : V)) he
  exact ⟨S,hsz,⟨g,hg⟩,fun b => (hAdj b _ (Classical.choose_spec (hchoose b))).2⟩

/-- The exact H2 connectivity and tree hypotheses give at least
`vertexConnectivity G - 2` squares at every edge. -/
theorem square_matching_of_tree_bound (hG : G.CliqueFree 3) {u v : V}
    (huv : G.Adj u v) (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    let A := (G.neighborFinset u).erase v
    let B := (G.neighborFinset v).erase u
    ∃ S : Finset B, vertexConnectivity G - 2 ≤ S.card ∧
      ∃ f : S ↪ A, ∀ b : S, G.Adj (f b : V) ((b : B) : V) := by
  obtain ⟨S, hS, f, hf⟩ := square_matching hG huv
    (k := vertexConnectivity G) (by omega)
  have ha : ((G.neighborFinset u).erase v).card + 1 = G.degree u := by
    rw [← G.card_neighborFinset_eq_degree]
    exact card_erase_add_one ((G.mem_neighborFinset u v).mpr huv)
  have hb : ((G.neighborFinset v).erase u).card + 1 = G.degree v := by
    rw [← G.card_neighborFinset_eq_degree]
    exact card_erase_add_one ((G.mem_neighborFinset v u).mpr huv.symm)
  have hdu := Graph199BipartiteOrder.vertexConnectivity_le_degree (G := G) u
  have hdv := Graph199BipartiteOrder.vertexConnectivity_le_degree (G := G) v
  exact ⟨S, by omega, f, hf⟩

#print axioms degree_eq_connectivity_or_succ
#print axioms square_exceptions_card_add_degree_le
#print axioms square_exceptions_at_most_one
#print axioms unique_common_neighbor_partner
#print axioms square_matching_with_deficiency
#print axioms square_matching
#print axioms square_matching_of_tree_bound

end Graph199TriangleFree
