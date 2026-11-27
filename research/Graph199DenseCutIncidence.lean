import Graph199SmallCutIncidence

namespace Graph199
open Finset
open scoped BigOperators

private theorem incidence_degree_sum {U C : Type*} [Fintype U] [Fintype C]
    [DecidableEq C] (R : U → Finset C) :
    (∑ u : U, (R u).card) = ∑ i : C, (univ.filter fun u => i ∈ R u).card := by
  classical
  calc
    _ = ∑ u : U, ∑ i : C, if i ∈ R u then (1 : ℕ) else 0 := by
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

private theorem intersection_large {U C : Type*} [DecidableEq C]
    (R : U → Finset C) (adj : U → U → Prop) (k : ℕ)
    (dist : ∀ u v, u ≠ v → (adj u v ∨ (R u ∩ R v).Nonempty) →
      ((R u \ R v) ∪ (R v \ R u)).card ≤ k)
    (u v : U) (hp : adj u v ∨ (R u ∩ R v).Nonempty) :
    (R u).card + (R v).card ≤ k + 2 * ((R u ∩ R v).card) := by
  classical
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

private theorem overlap_for_large_endpoints {U C : Type*} [DecidableEq C]
    (R : U → Finset C) (adj : U → U → Prop) (k : ℕ)
    (dist : ∀ u v, u ≠ v → (adj u v ∨ (R u ∩ R v).Nonempty) →
      ((R u \ R v) ∪ (R v \ R u)).card ≤ k)
    (u v w : U) (huv : (R u ∩ R v).Nonempty) (hvw : (R v ∩ R w).Nonempty)
    (hlarge : 2 * k < (R u).card + (R w).card) :
    (R u ∩ R w).Nonempty := by
  have hu := intersection_large R adj k dist u v (Or.inr huv)
  have hw := intersection_large R adj k dist v w (Or.inr hvw)
  have hlt : (R v).card < (R u ∩ R v).card + (R v ∩ R w).card := by omega
  obtain ⟨x,hx⟩ := inter_nonempty_of_card_lt_card_add_card inter_subset_right inter_subset_left hlt
  obtain ⟨hL,hR⟩ := mem_inter.mp hx
  exact ⟨x,mem_inter.mpr ⟨(mem_inter.mp hL).1,(mem_inter.mp hR).2⟩⟩

/-- Counting indicator differences over two ordered rows can be performed
column by column. -/
private theorem distance_sum_eq {U C : Type*} [Fintype U] [Fintype C] [DecidableEq C]
    (R : U → Finset C) :
    (∑ u : U, ∑ v : U, (((R u \ R v) ∪ (R v \ R u)).card : ℤ)) =
      ∑ i : C, 2 * ((univ.filter fun u => i ∈ R u).card : ℤ) *
        ((Fintype.card U : ℤ) - ((univ.filter fun u => i ∈ R u).card : ℤ)) := by
  classical
  let m : ℤ := Fintype.card U
  let J (i : C) (u : U) : ℤ := if i ∈ R u then 1 else 0
  let d (i : C) : ℤ := (univ.filter fun u => i ∈ R u).card
  have hd (i : C) : (∑ u : U, J i u) = d i := sum_boole _ _
  have hd' (i : C) : (∑ u : U, (1 - J i u)) = m - d i := by
    rw [sum_sub_distrib,hd]
    simp [m]
  have hF (u v : U) :
      (((R u \ R v) ∪ (R v \ R u)).card : ℤ) =
        ∑ i : C, (J i u * (1 - J i v) + (1 - J i u) * J i v) := by
    let S := (R u \ R v) ∪ (R v \ R u)
    change (S.card : ℤ) = _
    rw [show (S.card : ℤ) = ∑ i : C, if i ∈ S then (1 : ℤ) else 0 by
      rw [sum_boole]
      congr
      ext i
      simp]
    apply sum_congr rfl
    intro i _
    by_cases hu : i ∈ R u <;> by_cases hv : i ∈ R v <;> simp [J,S,hu,hv]
  calc
    _ = ∑ u : U, ∑ v : U, ∑ i : C,
        (J i u * (1 - J i v) + (1 - J i u) * J i v) := by simp only [hF]
    _ = ∑ i : C, ∑ u : U, ∑ v : U,
        (J i u * (1 - J i v) + (1 - J i u) * J i v) := by
      calc
        _ = ∑ u : U, ∑ i : C, ∑ v : U,
            (J i u * (1 - J i v) + (1 - J i u) * J i v) :=
          sum_congr rfl (fun _ _ => sum_comm)
        _ = _ := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro i _
      simp only [sum_add_distrib, ← mul_sum, hd', hd]
      rw [← sum_mul, ← sum_mul, hd, hd']
      change d i * (m - d i) + (m - d i) * d i = _
      ring

/-- The component-count incidence bound for any number of rows, provided
every row meets at least the minimum column degree. -/
theorem incidence_cut_bound_of_min_row {U C : Type*} [Fintype U] [Fintype C]
    [DecidableEq C] (R : U → Finset C) (adj : U → U → Prop) (k : ℕ) (hk : 0 < k)
    (col : ∀ i, k ≤ (univ.filter fun u => i ∈ R u).card)
    (row : ∀ u, k ≤ (R u).card ∧ (R u).card ≤ k + 1)
    (dist : ∀ u v, u ≠ v → (adj u v ∨ (R u ∩ R v).Nonempty) →
      ((R u \ R v) ∪ (R v \ R u)).card ≤ k)
    (connected : ∀ u v, Relation.ReflTransGen (fun a b => adj a b ∨ (R a ∩ R b).Nonempty) u v) :
    Fintype.card C ≤ Fintype.card U + 1 := by
  classical
  let m := Fintype.card U
  let c := Fintype.card C
  let E := ∑ u : U, (R u).card
  let D (u : U) := k + 1 - (R u).card
  let Δ := ∑ u : U, D u
  change c ≤ m + 1
  by_contra! h
  have hc : m + 2 ≤ c := by omega
  have hE := incidence_degree_sum R
  change E = _ at hE
  have he₁ : k * c ≤ E := by
    rw [hE]
    calc
      _ = ∑ _i : C, k := by simp [c,mul_comm]
      _ ≤ _ := sum_le_sum fun i _ => col i
  have hbal (u : U) : (R u).card + D u = k + 1 := by
    dsimp [D]
    have h := (row u).2
    omega
  have he₂ : E + Δ = m * (k + 1) := by
    change (∑ u : U, (R u).card) + (∑ u : U, D u) = _
    rw [← sum_add_distrib]
    simp [hbal,m]
  have hΔ : Δ + 2 * k ≤ m := by
    have hh := Nat.mul_le_mul_left k hc
    nlinarith
  have over_of_edge (u v : U) (hp : adj u v ∨ (R u ∩ R v).Nonempty) :
      (R u ∩ R v).Nonempty := by
    have h := intersection_large R adj k dist u v hp
    have hu := (row u).1
    have hv := (row v).1
    exact card_pos.mp (by omega)
  have shallow (u v : U) (hu : D u = 0) (_hv : D v ≤ 1) : (R u ∩ R v).Nonempty := by
    have hfull := hbal u
    induction connected u v with
    | refl =>
      apply card_pos.mp
      simp only [inter_self]
      have h := (row u).1
      omega
    | tail _ he ih =>
      rename_i y z _
      have hsmall := (row y).1
      have hlarge := (row z).1
      exact overlap_for_large_endpoints R adj k dist u y z
        (ih (by have hrow := hbal y; omega)) (over_of_edge _ _ he) (by omega)
  let M : ℤ := m
  let K : ℤ := k
  let Cn : ℤ := c
  let Ee : ℤ := E
  let X : ℤ := Δ
  let F (u v : U) : ℤ := ((R u \ R v) ∪ (R v \ R u)).card
  let T := ∑ u : U, ∑ v : U, F u v
  have hK : 0 < K := by
    dsimp [K]
    exact_mod_cast hk
  have hM : 0 < M := by
    have hm' : 0 < m := by omega
    dsimp [M]
    exact_mod_cast hm'
  have hX : 0 ≤ X := Int.natCast_nonneg _
  have hXL : X + 2 * K ≤ M := by
    dsimp [M,K,X]
    exact_mod_cast hΔ
  have hCc : M + 2 ≤ Cn := by
    dsimp [M,Cn]
    exact_mod_cast hc
  have hEe : Ee ≤ M * (K + 1) := by
    have hNat : E ≤ m * (k + 1) := by omega
    dsimp [Ee,M,K]
    exact_mod_cast hNat
  have hXsum : (∑ u : U, (D u : ℤ)) = X := by
    dsimp [X,Δ]
    norm_cast
  have hPoint (u v : U) :
      2 * F u v ≤ (if u = v then 0 else 2 * K) + K * ((D u : ℤ) + D v) := by
    by_cases huv : u = v
    · subst v
      have hno : 0 ≤ K * ((D u : ℤ) + D u) := by positivity
      simpa [F] using hno
    have hmain : 2 * (((R u \ R v) ∪ (R v \ R u)).card) ≤ 2 * k + k * (D u + D v) := by
      by_cases hd : D u + D v ≤ 1
      · have hO : (R u ∩ R v).Nonempty := by
          by_cases hu : D u = 0
          · exact shallow u v hu (by omega)
          · rw [inter_comm]
            exact shallow v u (by omega) (by omega)
        have hh := dist u v huv (Or.inr hO)
        have hnon : 0 ≤ k * (D u + D v) := Nat.zero_le _
        omega
      · have hD : 2 ≤ D u + D v := by omega
        have hmul := Nat.mul_le_mul_left k hD
        have h2 : ((R u \ R v) ∪ (R v \ R u)).card ≤ (R u).card + (R v).card := by
          have hu : (R u \ R v).card ≤ (R u).card := card_le_card sdiff_subset
          have hv : (R v \ R u).card ≤ (R v).card := card_le_card sdiff_subset
          have hUnion := card_union_le (R u \ R v) (R v \ R u)
          omega
        have hBu := hbal u
        have hBv := hbal v
        omega
    simp only [if_neg huv]
    dsimp [F,K]
    exact_mod_cast hmain
  have hbase (u : U) : (∑ v : U, if u = v then 0 else 2 * K) = 2 * K * (M - 1) := by
    have h0 : 1 ≤ Fintype.card U := Fintype.card_pos_iff.mpr ⟨u⟩
    have he : (∑ v ∈ univ.erase u, if u = v then 0 else 2 * K) =
        ∑ v : U, if u = v then 0 else 2 * K := by
      simp
    rw [← he]
    calc
      _ = ∑ _v ∈ univ.erase u, 2 * K := by
        apply sum_congr rfl
        intro v hv
        simp [ne_of_mem_erase hv |>.symm]
      _ = _ := by
        simp [M,m,Finset.card_erase_of_mem (Finset.mem_univ u),Nat.cast_sub h0,mul_comm]
  have hSum (u : U) :
      (∑ v : U, ((if u = v then 0 else 2 * K) + K * ((D u : ℤ) + D v))) =
        2 * K * (M - 1) + K * (M * D u + X) := by
    rw [sum_add_distrib,hbase,← mul_sum,sum_add_distrib,hXsum]
    simp [M,m]
  have hTop : 2 * T ≤ 2 * K * M * (M - 1) + 2 * K * M * X := by
    calc
      2 * T = ∑ u : U, ∑ v : U, 2 * F u v := by simp only [T,mul_sum]
      _ ≤ ∑ u : U, ∑ v : U, ((if u = v then 0 else 2 * K) +
          K * ((D u : ℤ) + D v)) := sum_le_sum fun u _ => sum_le_sum fun v _ => hPoint u v
      _ = ∑ u : U, (2 * K * (M - 1) + K * (M * D u + X)) := by simp only [hSum]
      _ = _ := by
        simp only [sum_add_distrib, ← mul_sum, hXsum, sum_const, card_univ, nsmul_eq_mul]
        dsimp [M,m]
        ring
  let d (i : C) : ℤ := (univ.filter fun u => i ∈ R u).card
  have heD : Ee = ∑ i : C, d i := by
    dsimp [Ee,d]
    exact_mod_cast hE
  have hT : T = ∑ i : C, 2 * d i * (M - d i) := distance_sum_eq R
  have hLow : 2 * K * Cn * M ≤ T + 2 * K * Ee := by
    rw [hT,heD,mul_sum,← sum_add_distrib]
    calc
      _ = ∑ _i : C, 2 * K * M := by simp [Cn,c]; ring
      _ ≤ _ := by
        apply sum_le_sum
        intro i _
        have hlo : K ≤ d i := by
          dsimp [K,d]
          exact_mod_cast col i
        have hhi : d i ≤ M := by
          dsimp [d,M,m]
          exact_mod_cast (card_le_univ (univ.filter fun u : U => i ∈ R u))
        nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)]
  have hKM : 0 < K * M := mul_pos hK hM
  have hTX := mul_le_mul_of_nonneg_left hXL hKM.le
  have hEx := mul_le_mul_of_nonneg_left hEe (show 0 ≤ 2 * K by omega)
  have hCc' := mul_le_mul_of_nonneg_left hCc hKM.le
  nlinarith

#print axioms incidence_cut_bound_of_min_row
end Graph199
