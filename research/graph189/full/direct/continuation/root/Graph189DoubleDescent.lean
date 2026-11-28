import Graph189SeparatorCover

open SimpleGraph Finset
namespace Graph189DoubleDescent

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] [DecidableEq V] in
private theorem first {x a : V} (hc : G.Connected) (ne : x ≠ a) :
    ∃ u, G.Adj x u ∧ G.dist x a = G.dist u a + 1 := by
  obtain ⟨p,d⟩ := (hc x a).exists_walk_length_eq_dist
  cases p with
  | nil => exact (ne rfl).elim
  | cons he tail =>
    rename_i y
    refine ⟨_,he,?_⟩
    have h := G.dist_le tail
    have t := hc.dist_triangle (u:=x) (v:=y) (w:=a)
    rw [dist_eq_one_iff_adj.mpr he] at t
    rw [Walk.length_cons] at d
    omega

/-- If the far side exceeds all |S| even-distance budgets combined, every
first edge strictly decreases distance to at most one vertex of the cut. -/
theorem unique_anchor (hc : G.Connected) (x : V) (S B : Finset V)
    (xs : x ∉ S) (xb : x ∉ B) (out : ∀ y, G.Adj x y → y ∉ B)
    (cut : ∀ b ∈ B, ∀ p : G.Walk x b, ∃ a ∈ S, a ∈ p.support)
    (k : ℕ) (cap : ∀ u, G.distEven u ≤ k+1) (big : S.card*k < B.card)
    {u a b : V} (hu : G.Adj x u) (ha : a ∈ S) (hb : b ∈ S)
    (da : G.dist x a = G.dist u a + 1) (db : G.dist x b = G.dist u b + 1) :
    a = b := by
  classical
  let valid (z y : V) := G.Adj x y ∧ G.dist x z = G.dist y z + 1
  have sel (z) (hz : z ∈ S) : ∃ y, valid z y := first hc (by rintro rfl; exact xs hz)
  let f (z : V) := if z = a ∨ z = b then u else if h : z ∈ S then (sel z h).choose else u
  have works (z) (hz : z ∈ S) : valid z (f z) := by
    by_cases hh : z = a ∨ z = b
    · rcases hh with he | he
      · subst z
        simpa [f] using (show valid a u from ⟨hu,da⟩)
      · subst z
        simpa [f] using (show valid b u from ⟨hu,db⟩)
    · simpa only [f,if_neg hh,dif_pos hz] using (sel z hz).choose_spec
  let R := S.image f
  have edge (y) (hy : y ∈ R) : G.Adj x y := by
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
    exact (works i hi).1
  have steps (i) (hi : i ∈ S) : ∃ y ∈ R, G.dist x i = G.dist y i + 1 :=
    ⟨f i,mem_image_of_mem _ hi,(works i hi).2⟩
  have bound := Graph189SeparatorCover.of_walk_separator hc x B S R xb
    (fun y hy => out y (edge y hy)) edge cut steps k cap
  have same : R.card = S.card := by
    have le : R.card ≤ S.card := card_image_le
    by_contra hn
    have hl : R.card + 1 ≤ S.card := by omega
    exact (not_lt_of_ge (bound.trans (Nat.mul_le_mul_right k hl))) big
  have inj : Set.InjOn f (S : Set V) := card_image_iff.mp same
  exact inj ha hb (by simp [f])

#print axioms unique_anchor
end Graph189DoubleDescent
