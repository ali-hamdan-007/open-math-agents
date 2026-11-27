import Graph199IncidenceNumbers
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Graph199
open Finset
open scoped BigOperators

private theorem sum_indicator {α : Type*} (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (∑ a ∈ s, if p a then (1 : ℤ) else 0) = ((s.filter p).card : ℤ) := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Incidence bound for a collection of columns with minimum degree k,
row degree at most k+1, and pairwise row distance at most k. -/
theorem incidence_clique_bound {U C : Type*} [Fintype U] [Fintype C] [DecidableEq C]
    (R : U → Finset C) (k : ℕ) (hk : 0 < k)
    (col : ∀ i, k ≤ (univ.filter fun u => i ∈ R u).card)
    (row : ∀ u, (R u).card ≤ k + 1)
    (dist : ∀ u v, u ≠ v → ((R u \ R v) ∪ (R v \ R u)).card ≤ k) :
    Fintype.card C ≤ Fintype.card U + 1 := by
  classical
  let m : ℤ := Fintype.card U
  let c : ℤ := Fintype.card C
  let I (i : C) (u : U) : ℤ := if i ∈ R u then 1 else 0
  let D (i : C) : ℤ := (univ.filter fun u => i ∈ R u).card
  let E : ℤ := ∑ i : C, D i
  let F (u v : U) : ℤ := ((R u \ R v) ∪ (R v \ R u)).card
  let T : ℤ := ∑ u : U, ∑ v : U, F u v
  have hI (i : C) : (∑ u : U, I i u) = D i := sum_indicator univ _
  have hrowI (u : U) : (∑ i : C, I i u) = ((R u).card : ℤ) := by
    rw [show (∑ i : C, I i u) = ((univ.filter fun i => i ∈ R u).card : ℤ) by
      exact sum_indicator univ _]
    simp
  have hE : E = ∑ u : U, ((R u).card : ℤ) := by
    simp only [E, ← hI, ← hrowI]
    exact Finset.sum_comm
  have he₁ : (k : ℤ) * c ≤ E := by
    calc
      _ = ∑ _i : C, (k : ℤ) := by simp [c, mul_comm]
      _ ≤ E := Finset.sum_le_sum fun i _ => by
        change (k : ℤ) ≤ ((univ.filter fun u => i ∈ R u).card : ℤ)
        exact_mod_cast col i
  have he₂ : E ≤ m * ((k : ℤ) + 1) := by
    rw [hE]
    calc
      _ ≤ ∑ _u : U, ((k : ℤ) + 1) :=
        Finset.sum_le_sum fun u _ => by exact_mod_cast row u
      _ = _ := by simp [m]
  have hF (u v : U) : F u v =
      ∑ i : C, (I i u * (1 - I i v) + (1 - I i u) * I i v) := by
    let S := (R u \ R v) ∪ (R v \ R u)
    have hcnt : (∑ i : C, if i ∈ S then (1 : ℤ) else 0) = F u v := by
      calc
        _ = ((univ.filter fun i => i ∈ S).card : ℤ) := sum_indicator univ _
        _ = _ := by
          have hS : univ.filter (fun i => i ∈ S) = S := by ext i; simp only [mem_filter, mem_univ, true_and]
          change _ = (S.card : ℤ)
          rw [hS]
    rw [← hcnt]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hu : i ∈ R u <;> by_cases hv : i ∈ R v <;> simp [I, S, hu, hv]
  have hnotI (i : C) : (∑ v : U, (1 - I i v)) = m - D i := by
    rw [Finset.sum_sub_distrib, hI]
    simp [m]
  have hT : T = ∑ i : C, 2 * D i * (m - D i) := by
    calc
      T = ∑ u : U, ∑ v : U, ∑ i : C,
          (I i u * (1 - I i v) + (1 - I i u) * I i v) := by simp only [T, hF]
      _ = ∑ i : C, ∑ u : U, ∑ v : U,
          (I i u * (1 - I i v) + (1 - I i u) * I i v) := by
        calc
          _ = ∑ u : U, ∑ i : C, ∑ v : U,
              (I i u * (1 - I i v) + (1 - I i u) * I i v) := by
            exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
          _ = _ := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hnotI, hI]
        rw [← Finset.sum_mul, ← Finset.sum_mul, hI, hnotI]
        ring
  have hs₁ : 2 * (k : ℤ) * c * m ≤ T + 2 * (k : ℤ) * E := by
    change _ ≤ T + 2 * (k : ℤ) * (∑ i : C, D i)
    rw [hT, Finset.mul_sum, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _i : C, 2 * (k : ℤ) * m := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, c]
        ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        have hlo : (k : ℤ) ≤ D i := by
          change (k : ℤ) ≤ ((univ.filter fun u => i ∈ R u).card : ℤ)
          exact_mod_cast col i
        have hhi : D i ≤ m := by
          change ((univ.filter fun u => i ∈ R u).card : ℤ) ≤ (Fintype.card U : ℤ)
          exact_mod_cast (Finset.card_le_univ (univ.filter fun u : U => i ∈ R u))
        nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)]
  have hs₂ : T ≤ (k : ℤ) * m * (m - 1) := by
    have hinner (u : U) : (∑ v : U, F u v) ≤ (k : ℤ) * (m - 1) := by
      have hzero : F u u = 0 := by simp [F]
      have hm1 : 1 ≤ Fintype.card U := Fintype.card_pos_iff.mpr ⟨u⟩
      calc
        _ = ∑ v ∈ univ.erase u, F u v := by
          have he := Finset.sum_erase_add (s := univ) (F u) (Finset.mem_univ u)
          rw [hzero, add_zero] at he
          exact he.symm
        _ ≤ ∑ _v ∈ univ.erase u, (k : ℤ) := by
          apply Finset.sum_le_sum
          intro v hv
          change ((((R u \ R v) ∪ (R v \ R u)).card : ℤ)) ≤ (k : ℤ)
          exact_mod_cast dist u v (Finset.ne_of_mem_erase hv).symm
        _ = _ := by
          simp [m, Finset.card_erase_of_mem (Finset.mem_univ u),
            Nat.cast_sub hm1, mul_comm]
    calc
      T ≤ ∑ _u : U, (k : ℤ) * (m - 1) :=
        Finset.sum_le_sum fun u _ => hinner u
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, m]; ring
  have hc : c ≤ m + 1 :=
    incidence_numbers (by exact_mod_cast hk) (Int.natCast_nonneg _) he₁ he₂ hs₁ hs₂
  change (Fintype.card C : ℤ) ≤ (Fintype.card U : ℤ) + 1 at hc
  exact_mod_cast hc

#print axioms incidence_clique_bound
end Graph199
