import BusyBeaverStrictGrowth
import OMAReductions.R_BusyBeaver_BB_4_R1
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finite.Prod
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-! A maximum is attained among positive finite-state machines, and adding an initial
state increases its running time by one. -/

namespace BusyBeaverSuccessor

open Turing Turing.BusyBeaver

private local instance : Finite (Stmt (Fin 2)) :=
  Finite.of_surjective
    (fun p : Fin 2 × Bool => Stmt.write p.1 (if p.2 then Dir.left else Dir.right))
    (by
      rintro ⟨a, d⟩
      cases d
      · exact ⟨(a, true), rfl⟩
      · exact ⟨(a, false), rfl⟩)

private def runningTimes (n : ℕ) : Set ℕ :=
  { k | ∃ C : BusyBeaver.Candidate n, C.M.haltingNumber = (k : ℕ) }

private theorem runningTimes_finite (n : ℕ) [NeZero n] : (runningTimes n).Finite := by
  classical
  let : Finite (Machine (Fin 2) (Fin n)) := by
    unfold Machine
    infer_instance
  let cast : ℕ → ℕ∞ := fun k => k
  have himage : cast '' runningTimes n ⊆
      Set.range (fun M : Machine (Fin 2) (Fin n) => M.haltingNumber) := by
    rintro _ ⟨k, ⟨C, hC⟩, rfl⟩
    obtain ⟨M, _, hM⟩ := OMA.R_BusyBeaver_BB_4_R1.normalize n C
    exact ⟨M, hM.trans hC⟩
  exact Set.Finite.of_finite_image ((Set.finite_range _).subset himage) (by
    intro a _ b _ hab
    exact ENat.natCast_inj.mp hab)

private theorem runningTimes_nonempty (n : ℕ) [NeZero n] : (runningTimes n).Nonempty := by
  let M : Machine (Fin 2) (Fin n) := fun _ _ => none
  let C : BusyBeaver.Candidate n :=
    { Γ := Fin 2
      Λ := Fin n
      Γ_fintype := inferInstance
      Γ_card := Fintype.card_fin _
      Γ_inhabited := inferInstance
      Λ_fintype := inferInstance
      Λ_card := Fintype.card_fin _
      Λ_inhabited := inferInstance
      M := M
      M_isHalting := (Machine.isHalting_iff_exists_haltsAt M).mpr ⟨0, rfl⟩ }
  exact ⟨0, C, M.haltingNumber_def 0 ⟨_, rfl⟩ rfl⟩

/-- Each Busy Beaver value at positive state count is achieved by a halting machine. -/
theorem maximum_attained (n : ℕ) [NeZero n] :
    ∃ C : BusyBeaver.Candidate n, C.M.haltingNumber = (BusyBeaver.BB n : ℕ) :=
  (runningTimes_nonempty n).csSup_mem (runningTimes_finite n)

private theorem pad_candidate {n k : ℕ} (C : BusyBeaver.Candidate n)
    (hk : C.M.haltingNumber = (k : ℕ)) :
    ∃ D : BusyBeaver.Candidate (n + 1), D.M.haltingNumber = ((k + 1 : ℕ) : ℕ∞) := by
  let : Inhabited (Unit ⊕ C.Λ) := ⟨Sum.inl ()⟩
  obtain ⟨N, hN, htime, hcard⟩ := BusyBeaverStrictGrowth.delay_finite C.M C.M_isHalting hk
  exact ⟨{ Γ := C.Γ
           Λ := Unit ⊕ C.Λ
           Γ_fintype := C.Γ_fintype
           Γ_card := C.Γ_card
           Γ_inhabited := C.Γ_inhabited
           Λ_fintype := inferInstance
           Λ_card := hcard.trans (congrArg (· + 1) C.Λ_card)
           Λ_inhabited := inferInstance
           M := N
           M_isHalting := hN }, htime⟩

/-- One extra state increases the Busy Beaver value by at least one. -/
theorem bb_add_one_le (n : ℕ) [NeZero n] : BusyBeaver.BB n + 1 ≤ BusyBeaver.BB (n + 1) := by
  obtain ⟨C, hC⟩ := maximum_attained n
  exact le_csSup (runningTimes_finite (n + 1)).bddAbove (pad_candidate C hC)

end BusyBeaverSuccessor

#print axioms BusyBeaverSuccessor.maximum_attained
#print axioms BusyBeaverSuccessor.bb_add_one_le
