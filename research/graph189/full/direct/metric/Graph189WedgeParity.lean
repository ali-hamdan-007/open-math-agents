import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance
import Mathlib.Combinatorics.SimpleGraph.Diam

namespace Graph189WedgeParity

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}

private theorem odd_eq_across_edge (hc : G.Connected) {u w t : V} (e : G.Adj u w)
    (hu : ¬Even (G.dist u t)) (hw : ¬Even (G.dist w t)) :
    G.dist u t = G.dist w t := by
  have h₁ := hc.dist_triangle (u := u) (v := w) (w := t)
  have h₂ := hc.dist_triangle (u := w) (v := u) (w := t)
  rw [dist_eq_one_iff_adj.mpr e] at h₁
  rw [dist_eq_one_iff_adj.mpr e.symm] at h₂
  rw [Nat.even_iff] at hu hw
  omega

/-- Every geodesic to a remote equidistant witness needs a second-layer
vertex missed by both endpoints. Here we extract one such vertex. -/
theorem missed_of_remote (hc : G.Connected) {u w v t : V}
    (hu : G.dist u t = G.dist w t) (hv : G.dist v t = G.dist w t)
    (ht : 3 ≤ G.dist w t) :
    ∃ b, G.dist w b = 2 ∧ ¬G.Adj u b ∧ ¬G.Adj v b := by
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist w t
  cases p with
  | nil => simp at ht
  | @cons _ a _ hwa p =>
    cases p with
    | nil => simp at hp; omega
    | @cons _ b _ hab rest =>
      simp only [Walk.length_cons] at hp
      have tail_le := G.dist_le rest
      have first_le : G.dist w b ≤ 2 := by
        let s : G.Walk w b := .cons hwa (.cons hab .nil)
        simpa [s] using G.dist_le s
      have lower := hc.dist_triangle (u := w) (v := b) (w := t)
      refine ⟨b, by omega, ?_, ?_⟩
      · intro h
        have hle := hc.dist_triangle (u := u) (v := b) (w := t)
        rw [dist_eq_one_iff_adj.mpr h] at hle
        omega
      · intro h
        have hle := hc.dist_triangle (u := v) (v := b) (w := t)
        rw [dist_eq_one_iff_adj.mpr h] at hle
        omega

/-- The order and the overlapping even-distance sets bound the number of
remote odd witnesses required by an induced wedge. -/
theorem wedge_count [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hc : G.Connected) {u w v : V} (e : G.Adj u w) (f : G.Adj w v)
    {k : ℕ} (cap : ∀ a, G.distEven a ≤ k+1) :
    Fintype.card V + (G.neighborFinset w \ (G.neighborFinset u ∪ G.neighborFinset v)).card ≤
      3*(k+1) + ((G.neighborFinset u ∩ G.neighborFinset v) ∩ G.neighborFinset w).card +
        (univ.filter fun t => 3 ≤ G.dist w t ∧ G.dist u t = G.dist w t ∧
          G.dist v t = G.dist w t ∧ ¬Even (G.dist w t)).card := by
  let E (a : V) := univ.filter fun t => Even (G.dist a t)
  let Q := G.neighborFinset w \ (G.neighborFinset u ∪ G.neighborFinset v)
  let C := (G.neighborFinset u ∩ G.neighborFinset v) ∩ G.neighborFinset w
  let T := univ.filter fun t => 3 ≤ G.dist w t ∧ G.dist u t = G.dist w t ∧
    G.dist v t = G.dist w t ∧ ¬Even (G.dist w t)
  have even_nonedge {a t : V} (edge : G.Adj a w) (edge' : G.Adj w t)
      (hn : ¬G.Adj a t) : Even (G.dist a t) := by
    have d := hc.dist_triangle (u := a) (v := w) (w := t)
    rw [dist_eq_one_iff_adj.mpr edge,dist_eq_one_iff_adj.mpr edge'] at d
    have none : G.dist a t ≠ 1 := fun h => hn (dist_eq_one_iff_adj.mp h)
    rw [Nat.even_iff]
    omega
  have overlap : Q ⊆ E u ∩ E v := by
    intro t h
    have hh := mem_sdiff.mp h
    have hwt := (G.mem_neighborFinset _ _).mp hh.1
    have nn := not_or.mp (fun h => hh.2 (mem_union.mpr h))
    exact mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _,even_nonedge e hwt
      (fun h => nn.1 ((G.mem_neighborFinset _ _).mpr h))⟩,mem_filter.mpr ⟨mem_univ _,
        even_nonedge f.symm hwt (fun h => nn.2 ((G.mem_neighborFinset _ _).mpr h))⟩⟩
  have cover : univ ⊆ (((E u ∪ E v) ∪ E w) ∪ C) ∪ T := by
    intro t _
    by_cases h₁ : Even (G.dist u t)
    · simp [h₁,E]
    by_cases h₂ : Even (G.dist v t)
    · simp [h₂,E]
    by_cases h₃ : Even (G.dist w t)
    · simp [h₃,E]
    have xu := odd_eq_across_edge hc e h₁ h₃
    have xv := odd_eq_across_edge hc f.symm h₂ h₃
    by_cases far : 3 ≤ G.dist w t
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,far,xu,xv,h₃⟩)
    · have odd := h₃
      rw [Nat.even_iff] at odd
      have one : G.dist w t = 1 := by omega
      exact mem_union_left _ (mem_union_right _ (mem_inter.mpr ⟨mem_inter.mpr
        ⟨(G.mem_neighborFinset _ _).mpr (dist_eq_one_iff_adj.mp (xu.trans one)),
         (G.mem_neighborFinset _ _).mpr (dist_eq_one_iff_adj.mp (xv.trans one))⟩,
          (G.mem_neighborFinset _ _).mpr (dist_eq_one_iff_adj.mp one)⟩))
  have count := card_le_card cover
  rw [card_univ] at count
  have q := card_le_card overlap
  have uv := card_union_add_card_inter (E u) (E v)
  have h₁ := card_union_le (E u ∪ E v) (E w)
  have h₂ := card_union_le ((E u ∪ E v) ∪ E w) C
  have h₃ := card_union_le (((E u ∪ E v) ∪ E w) ∪ C) T
  have eu : (E u).card ≤ k+1 := cap u
  have ev : (E v).card ≤ k+1 := cap v
  have ew : (E w).card ≤ k+1 := cap w
  change Fintype.card V + Q.card ≤ 3*(k+1) + C.card + T.card
  omega

#print axioms missed_of_remote
#print axioms wedge_count
end Graph189WedgeParity
