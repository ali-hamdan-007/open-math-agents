import Graph199CliqueSeparator

namespace Graph199

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In a split graph with induced trees of order at most five, a row of
size four forces the other stable neighborhoods to have at most one
vertex outside that row. Any row with such a vertex meets the row of
size four in at least two vertices. -/
theorem split_full_row {Q I : Finset V} (hQ : G.IsClique (Q : Set V))
    (hI : G.IsIndepSet (I : Set V)) (hQI : Disjoint Q I)
    (ht : largestInducedTreeSize G ≤ 5) {u : V} (hu : u ∈ Q)
    (hfull : (I.filter (G.Adj u)).card = 4) :
    let R := fun v => I.filter (G.Adj v)
    ∀ v ∈ Q, ((R v) \ (R u)).card ≤ 1 ∧
      (((R v) \ (R u)).Nonempty → 2 ≤ ((R v) ∩ (R u)).card) := by
  intro R v hv
  have hmem (x y : V) : y ∈ R x ↔ y ∈ I ∧ G.Adj x y := mem_filter
  change (R u).card = 4 at hfull
  by_cases he : u = v
  · subst v
    simp
  have hbound : (R v).card ≤ 4 := by
    have h := star_bound v (R v)
      (fun _ hx _ hy hxy => hI ((hmem _ _).mp hx).1 ((hmem _ _).mp hy).1 hxy)
      (fun _ hx => ((hmem _ _).mp hx).2)
    omega
  have hprivate : ((R u) \ (R v)).card + ((R v) \ (R u)).card ≤ 3 := by
    have hsub (x y z : V) (hz : z ∈ (R x) \ (R y)) : z ∈ I :=
      ((hmem x z).mp (mem_sdiff.mp hz).1).1
    have hdiff (x y z : V) (hz : z ∈ (R x) \ (R y)) : G.Adj x z ∧ ¬ G.Adj y z := by
      refine ⟨((hmem x z).mp (mem_sdiff.mp hz).1).2,fun he' => ?_⟩
      exact (mem_sdiff.mp hz).2 ((hmem y z).mpr ⟨hsub x y z hz,he'⟩)
    have h := double_star_bound u v (hQ hu hv he) ((R u) \ (R v)) ((R v) \ (R u))
      (fun _ hx _ hy hxy => hI (hsub _ _ _ hx) (hsub _ _ _ hy) hxy)
      (fun _ hx _ hy hxy => hI (hsub _ _ _ hx) (hsub _ _ _ hy) hxy)
      (fun x hx y hy => by
        have hn : x ≠ y := fun he' => (mem_sdiff.mp hx).2 (he' ▸ (mem_sdiff.mp hy).1)
        exact ⟨hn,hI (hsub _ _ _ hx) (hsub _ _ _ hy) hn⟩)
      (hdiff u v) (hdiff v u)
      (fun hm => Finset.disjoint_left.mp hQI hv (hsub _ _ _ hm))
      (fun hm => Finset.disjoint_left.mp hQI hu (hsub _ _ _ hm))
    omega
  have hleft := card_sdiff_add_card_inter (R u) (R v)
  have hright := card_sdiff_add_card_inter (R v) (R u)
  rw [inter_comm (R u)] at hleft
  constructor
  · omega
  · intro h
    have := card_pos.mpr h
    omega

#print axioms split_full_row

end Graph199
