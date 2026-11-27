import OMAReductions.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1
import Mathlib.Data.Nat.GCD.BigOperators

open Finset
open scoped BigOperators

private theorem frame_coprime {a M M' N N' p q : ℕ}
    (haM : a ∣ M) (haN : a.Coprime N)
    (hp : p * M' + M = N * q) (hq : q * N' + N = M * p) :
    p.Coprime a := by
  change p.gcd a = 1
  let d := p.gcd a
  have hdp : d ∣ p := Nat.gcd_dvd_left p a
  have hda : d ∣ a := Nat.gcd_dvd_right p a
  have hdM : d ∣ M := hda.trans haM
  have hdNcop : d.Coprime N := haN.coprime_dvd_left hda
  have hdq : d ∣ q := hdNcop.dvd_of_dvd_mul_left <| hp ▸
    dvd_add (dvd_mul_of_dvd_left hdp _) hdM
  have hdN : d ∣ N := (Nat.dvd_add_iff_right (dvd_mul_of_dvd_left hdq N')).mpr
    (hq.symm ▸ dvd_mul_of_dvd_right hdp M)
  exact Nat.dvd_one.mp (hdNcop.gcd_eq_one ▸ Nat.dvd_gcd (dvd_refl d) hdN)

private theorem pairwise_extend {A : Finset ℕ} {p : ℕ} (hp : 2 ≤ p)
    (hA : Set.Pairwise (A : Set ℕ) Nat.Coprime)
    (hcop : ∀ a ∈ A, p.Coprime a) :
    p ∉ A ∧ Set.Pairwise ((insert p A : Finset ℕ) : Set ℕ) Nat.Coprime := by
  have hnot : p ∉ A := by
    intro hpA
    have h := (hcop p hpA).gcd_eq_one
    rw [Nat.gcd_self] at h
    omega
  refine ⟨hnot, ?_⟩
  rw [Finset.coe_insert]
  exact hA.insert fun a ha _ => ⟨hcop a ha, (hcop a ha).symm⟩

theorem OMA.solution : OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1.H2 := by
  intro P Q _ _ _ _ hP hQ hPQ M M' N N' hlt hlowP hlowQ hdivP hdivQ p q
  let Δ := M * N - M' * N'
  have hΔ : 0 < Δ := by
    dsimp only [Δ]
    exact Nat.sub_pos_of_lt hlt
  have hp : 2 ≤ p := (Nat.le_div_iff_mul_le hΔ).2 hlowP
  have hq : 2 ≤ q := (Nat.le_div_iff_mul_le hΔ).2 hlowQ
  obtain ⟨hcP, hcQ⟩ :=
    OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1.frame_cross_eq
      hlt (show Δ = M * N - M' * N' from rfl)
      (show Δ * p = M * N' + N ^ 2 from Nat.mul_div_cancel' hdivP)
      (show Δ * q = M' * N + M ^ 2 from Nat.mul_div_cancel' hdivQ)
  obtain ⟨hnP, hpairP⟩ := pairwise_extend hp hP fun a ha =>
    frame_coprime (Finset.dvd_prod_of_mem (fun x => x) ha)
      (Nat.coprime_prod_right_iff.2 fun b hb => hPQ a ha b hb) hcP hcQ
  obtain ⟨hnQ, hpairQ⟩ := pairwise_extend hq hQ fun b hb =>
    frame_coprime (Finset.dvd_prod_of_mem (fun x => x) hb)
      (Nat.coprime_prod_right_iff.2 fun a ha => (hPQ a ha b hb).symm) hcQ hcP
  exact ⟨hp, hnP, hq, hnQ, hpairP, hpairQ⟩

