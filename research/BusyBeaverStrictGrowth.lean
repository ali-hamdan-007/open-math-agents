import FormalConjecturesForMathlib.Computability.TuringMachine.BusyBeavers
import Mathlib.Data.Fintype.Sum

/-! Adding an initial state increases the blank-tape running time by exactly one. -/

namespace BusyBeaverStrictGrowth

open Turing Turing.BusyBeaver

section
variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]

local instance : Inhabited (Unit ⊕ Λ) := ⟨Sum.inl ()⟩

/-- The fresh initial state writes a blank, moves right and enters the old initial state. -/
def delay (M : Machine Γ Λ) : Machine Γ (Unit ⊕ Λ)
  | .inl _, _ => some (some (.inr default), Stmt.write default Dir.right)
  | .inr q, a => (M q a).map fun (q', cmd) => (q'.map Sum.inr, cmd)

def embed (c : Cfg Γ Λ) : Cfg Γ (Unit ⊕ Λ) := ⟨c.q.map Sum.inr, c.tape⟩

theorem delay_step (M : Machine Γ Λ) (c : Cfg Γ Λ) :
    (delay M).step (embed c) = (M.step c).map embed := by
  obtain ⟨q, tape⟩ := c
  cases q with
  | none => rfl
  | some q =>
    cases h : M q tape.head with
    | none => simp [Machine.step, embed, delay, h]
    | some pair =>
      obtain ⟨q', cmd⟩ := pair
      simp [Machine.step, embed, delay, h]

/-- Every subsequent configuration is the corresponding old configuration with lifted labels. -/
theorem delay_trace (M : Machine Γ Λ) (k : ℕ) :
    (delay M).multiStep (Machine.init []) (k + 1) =
      (M.multiStep (Machine.init []) k).map embed := by
  induction k with
  | zero =>
    simp only [Nat.zero_add, Machine.multiStep_one, Machine.multiStep_zero]
    change some (⟨some (Sum.inr (default : Λ)),
      ((Tape.mk₁ ([] : List Γ)).write default).move Dir.right⟩ : Cfg Γ (Unit ⊕ Λ)) =
      some ⟨some (Sum.inr default), Tape.mk₁ []⟩
    have hblank : (ListBlank.mk ([] : List Γ)).cons default = ListBlank.mk [] :=
      (ListBlank.cons_head_tail (ListBlank.mk ([] : List Γ)))
    simp [Tape.write, Tape.move, Tape.mk₁, Tape.mk₂, Tape.mk', hblank]
  | succ k ih =>
    rw [Machine.multiStep_succ (delay M), ih, Machine.multiStep_succ M]
    cases M.multiStep (Machine.init []) k with
    | none => rfl
    | some c => exact delay_step M c

theorem exists_haltingNumber_witness (M : Machine Γ Λ) (hM : M.IsHalting) :
    ∃ k, M.haltingNumber = (k : ℕ) ∧
      (∃ c, M.multiStep (Machine.init []) k = some c) ∧
      M.multiStep (Machine.init []) (k + 1) = none := by
  classical
  have hex := (Machine.isHalting_iff_exists_haltsAt M).mp hM
  have hstop := Nat.find_spec hex
  have hlive : ∃ c, M.multiStep (Machine.init []) (Nat.find hex) = some c := by
    cases hk : Nat.find hex with
    | zero => exact ⟨_, rfl⟩
    | succ k =>
      have hnot := Nat.find_min hex (show k < Nat.find hex by omega)
      rw [Machine.HaltsAfter] at hnot
      exact Option.ne_none_iff_exists'.mp hnot
  exact ⟨_, M.haltingNumber_def _ hlive hstop, hlive, hstop⟩

/-- Adding one state preserves halting and increases the first halting time by one. -/
theorem delay_haltingNumber (M : Machine Γ Λ) (hM : M.IsHalting) {k : ℕ}
    (hk : M.haltingNumber = (k : ℕ)) :
    (delay M).IsHalting ∧ (delay M).haltingNumber = ((k + 1 : ℕ) : ℕ∞) := by
  obtain ⟨j, hj, ⟨c, hc⟩, hstop⟩ := exists_haltingNumber_witness M hM
  have hjk : j = k := by exact_mod_cast hj.symm.trans hk
  subst j
  have live : ∃ c, (delay M).multiStep (Machine.init []) (k + 1) = some c :=
    ⟨embed c, by rw [delay_trace, hc]; rfl⟩
  have stop : (delay M).multiStep (Machine.init []) (k + 1 + 1) = none := by
    rw [delay_trace, hstop]
    rfl
  exact ⟨(Machine.isHalting_iff_exists_haltsAt (delay M)).mpr ⟨k + 1, stop⟩,
    (delay M).haltingNumber_def (k + 1) live stop⟩

/-- The padded machine has one additional state and uses the same tape alphabet. -/
theorem delay_finite (M : Machine Γ Λ) [Fintype Λ] (hM : M.IsHalting) {k : ℕ}
    (hk : M.haltingNumber = (k : ℕ)) :
    ∃ N : Machine Γ (Unit ⊕ Λ), N.IsHalting ∧
      N.haltingNumber = ((k + 1 : ℕ) : ℕ∞) ∧ Fintype.card (Unit ⊕ Λ) = Fintype.card Λ + 1 := by
  obtain ⟨hhalting, hnumber⟩ := delay_haltingNumber M hM hk
  exact ⟨delay M, hhalting, hnumber, by simp [Nat.add_comm]⟩

end

end BusyBeaverStrictGrowth

#print axioms BusyBeaverStrictGrowth.delay_trace
#print axioms BusyBeaverStrictGrowth.delay_haltingNumber
#print axioms BusyBeaverStrictGrowth.delay_finite
