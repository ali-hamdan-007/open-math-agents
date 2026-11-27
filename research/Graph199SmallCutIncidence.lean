import Graph199Incidence

namespace Graph199
open Finset
open scoped BigOperators

/-- The row-distance bound need only hold on adjacent or overlapping rows
when there are at most twice the minimum column degree plus one rows, and the
adjacency-or-overlap graph is connected. -/
theorem incidence_small_cut_bound_succ {U C : Type*} [Fintype U] [Fintype C]
    [DecidableEq C] (R : U → Finset C) (adj : U → U → Prop) (k : ℕ) (hk : 0 < k)
    (hm : Fintype.card U ≤ 2 * k + 1)
    (col : ∀ i, k ≤ (univ.filter fun u => i ∈ R u).card)
    (row : ∀ u, (R u).card ≤ k + 1)
    (dist : ∀ u v, u ≠ v → (adj u v ∨ (R u ∩ R v).Nonempty) →
      ((R u \ R v) ∪ (R v \ R u)).card ≤ k)
    (connected : ∀ u v, Relation.ReflTransGen (fun a b => adj a b ∨ (R a ∩ R b).Nonempty) u v) :
    Fintype.card C ≤ Fintype.card U + 1 := by
  classical
  let m := Fintype.card U
  let c := Fintype.card C
  let E : ℕ := ∑ u : U, (R u).card
  have Hm : m ≤ 2 * k + 1 := hm
  change c ≤ m + 1
  by_contra! h
  have hc : m + 2 ≤ c := by omega
  have hE : E = ∑ i : C, (univ.filter fun u => i ∈ R u).card := by
    calc
      E = ∑ u : U, ∑ i : C, if i ∈ R u then (1 : ℕ) else 0 := by
        dsimp [E]
        apply sum_congr rfl
        intro u _
        rw [sum_boole]
        congr
        ext i
        simp
      _ = ∑ i : C, ∑ u : U, if i ∈ R u then (1 : ℕ) else 0 := sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro i _
        simp
  have he₁ : k * c ≤ E := by
    rw [hE]
    calc
      _ = ∑ _i : C, k := by simp [c,mul_comm]
      _ ≤ _ := sum_le_sum fun i _ => col i
  let D (u : U) := k + 1 - (R u).card
  let Δ : ℕ := ∑ u : U, D u
  have hbalance (u : U) : (R u).card + D u = k + 1 := by
    dsimp [D]
    have h := row u
    omega
  have he₂ : E + Δ = m * (k + 1) := by
    change (∑ u : U, (R u).card) + (∑ u : U, D u) = _
    rw [← sum_add_distrib]
    simp [hbalance,m]
  have hΔ : Δ ≤ 1 := by
    have hh := Nat.mul_le_mul_left k hc
    nlinarith
  have hpos (u : U) : 0 < (R u).card := by
    have hD : D u ≤ Δ :=
      single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ u)
    have hbal := hbalance u
    omega
  have pair_large (u v : U) (hne : u ≠ v) : 2 * k + 1 ≤ (R u).card + (R v).card := by
    have hp : D u + D v ≤ Δ := by
      have hle : (∑ x ∈ ({u,v} : Finset U), D x) ≤ Δ :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
      simpa [sum_pair hne] using hle
    have hu := hbalance u
    have hv := hbalance v
    omega
  have intersection (u v : U) (hp : adj u v ∨ (R u ∩ R v).Nonempty) :
      (R u).card + (R v).card ≤ k + 2 * ((R u ∩ R v).card) := by
    by_cases he : u = v
    · subst v
      simp only [inter_self]
      omega
    have hd := dist u v he hp
    have hdis : Disjoint (R u \ R v) (R v \ R u) := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      exact (mem_sdiff.mp hi).2 (mem_sdiff.mp hj).1
    rw [card_union_of_disjoint hdis] at hd
    have h1 := card_sdiff_add_card_inter (R u) (R v)
    have h2 := card_sdiff_add_card_inter (R v) (R u)
    rw [inter_comm (R v)] at h2
    omega
  have over_of_edge (u v : U) (hp : adj u v ∨ (R u ∩ R v).Nonempty) :
      (R u ∩ R v).Nonempty := by
    by_cases he : u = v
    · subst v
      simpa using card_pos.mp (hpos u)
    apply card_pos.mp
    have h1 := pair_large u v he
    have h2 := intersection u v hp
    omega
  have over_trans (u v w : U) (huv : (R u ∩ R v).Nonempty) (hvw : (R v ∩ R w).Nonempty) :
      (R u ∩ R w).Nonempty := by
    by_cases he : u = w
    · subst w
      simpa using card_pos.mp (hpos u)
    have hu := intersection u v (Or.inr huv)
    have hw := intersection v w (Or.inr hvw)
    have hh := pair_large u w he
    have hlt : (R v).card < (R u ∩ R v).card + (R v ∩ R w).card := by omega
    obtain ⟨x,hx⟩ := inter_nonempty_of_card_lt_card_add_card inter_subset_right inter_subset_left hlt
    obtain ⟨hL,hR⟩ := mem_inter.mp hx
    exact ⟨x,mem_inter.mpr ⟨(mem_inter.mp hL).1,(mem_inter.mp hR).2⟩⟩
  have all_overlap (u v : U) : (R u ∩ R v).Nonempty := by
    induction connected u v with
    | refl => simpa using card_pos.mp (hpos u)
    | tail _ he ih => exact over_trans _ _ _ ih (over_of_edge _ _ he)
  exact (not_le.mpr h) (incidence_clique_bound R k hk col row
    (fun u v hne => dist u v hne (Or.inr (all_overlap u v))))

/-- The boundary at twice the column degree is a special case of the
small-cut incidence bound. -/
theorem incidence_small_cut_bound {U C : Type*} [Fintype U] [Fintype C]
    [DecidableEq C] (R : U → Finset C) (adj : U → U → Prop) (k : ℕ) (hk : 0 < k)
    (hm : Fintype.card U ≤ 2 * k)
    (col : ∀ i, k ≤ (univ.filter fun u => i ∈ R u).card)
    (row : ∀ u, (R u).card ≤ k + 1)
    (dist : ∀ u v, u ≠ v → (adj u v ∨ (R u ∩ R v).Nonempty) →
      ((R u \ R v) ∪ (R v \ R u)).card ≤ k)
    (connected : ∀ u v, Relation.ReflTransGen (fun a b => adj a b ∨ (R a ∩ R b).Nonempty) u v) :
    Fintype.card C ≤ Fintype.card U + 1 :=
  incidence_small_cut_bound_succ R adj k hk (by omega) col row dist connected

#print axioms incidence_small_cut_bound_succ
#print axioms incidence_small_cut_bound
end Graph199
