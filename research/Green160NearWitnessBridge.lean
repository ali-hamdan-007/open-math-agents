import FormalConjecturesForMathlib.Combinatorics.AP.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Green160NearWitness

open Set

namespace OMA.Green160NearWitness

private lemma progression_at {N k a d : Nat} (hd : 0 < d)
    (c : Icc 1 N → Fin 2) (color : Fin 2)
    (bound : ∀ i : Fin k, a+i.val*d < N)
    (mono : ∀ (i : Fin k) (hi : a+i.val*d < N), c ⟨a+i.val*d+1, by constructor <;> omega⟩ = color) :
    ∃ s : Finset (Icc 1 N), ({(z : Nat) | z ∈ s}).IsAPOfLength k ∧
      ∀ z ∈ s, c z = color := by
  classical
  let value (i : Fin k) := a + i.val*d + 1
  have inj : Function.Injective value := by
    intro i j h
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_right hd (by simpa [value] using h)
  let point : Fin k ↪ Icc 1 N := ⟨fun i => ⟨value i, by
    have := bound i
    dsimp [value]
    constructor <;> omega⟩, fun i j h => inj (congrArg Subtype.val h)⟩
  let s := Finset.univ.map point
  have eqs : ({(z : Nat) | z ∈ s} : Set Nat) = range value := by
    ext z
    constructor
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hy
      exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨point i,Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩,rfl⟩
  refine ⟨s, ?_, ?_⟩
  · rw [eqs]
    refine ⟨a+1,d,?_,?_⟩
    · rw [ENat.card_coe_set_eq, ← Set.image_univ, inj.encard_image]
      simp
    · ext z
      constructor
      · rintro ⟨i,rfl⟩
        exact ⟨i.val,by exact_mod_cast i.isLt,by simp [value]; omega⟩
      · rintro ⟨i,hi,rfl⟩
        exact ⟨⟨i,by exact_mod_cast hi⟩,by simp [value]; omega⟩
  · intro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hz
    exact mono i (bound i)


def intervalColor (c : Icc 1 160 → Fin 2) (i : Nat) : Bool :=
  if hi : i < 160 then decide (c ⟨i+1, by constructor <;> omega⟩ = 1) else false

theorem on_interval (c : Icc 1 160 → Fin 2)
    (seed : Mono (intervalColor c)) :
    (∃ s : Finset (Icc 1 160), ({(x : Nat) | x ∈ s}).IsAPOfLength 3 ∧
      ∀ x ∈ s, c x = 0) ∨
    (∃ s : Finset (Icc 1 160), ({(x : Nat) | x ∈ s}).IsAPOfLength 13 ∧
      ∀ x ∈ s, c x = 1) := by
  obtain ⟨b,a,d,hd,he,hm⟩ := seed
  cases b
  · left
    apply progression_at (k := 3) (a := a) hd c 0
    · intro i
      have hib := i.isLt
      have := Nat.mul_le_mul_right d (show i.val ≤ 2 by omega)
      simp only [Bool.false_eq_true, if_false] at he
      omega
    · intro i hi
      have hib := i.isLt
      have hh := hm i.val (by simp only [Bool.false_eq_true, if_false]; omega)
      have hv : ¬ c ⟨a+i.val*d+1, by constructor <;> omega⟩ = 1 := by
        simpa [intervalColor, hi] using hh
      exact (show ∀ x : Fin 2, ¬ x = 1 → x = 0 by decide) _ hv
  · right
    apply progression_at (k := 13) (a := a) hd c 1
    · intro i
      have hib := i.isLt
      have := Nat.mul_le_mul_right d (show i.val ≤ 12 by omega)
      simp only [if_true] at he
      omega
    · intro i hi
      have hib := i.isLt
      have hh := hm i.val (by simp only [if_true]; omega)
      simpa [intervalColor, hi] using hh

theorem branch_on_interval (c : Icc 1 160 → Fin 2)
    (red : ∀ x ∈ [66,70,71,89,96,98], intervalColor c x = false)
    (blue : ∀ x ∈ [77,93], intervalColor c x = true) :
    (∃ s : Finset (Icc 1 160), ({(x : Nat) | x ∈ s}).IsAPOfLength 3 ∧
      ∀ x ∈ s, c x = 0) ∨
    (∃ s : Finset (Icc 1 160), ({(x : Nat) | x ∈ s}).IsAPOfLength 13 ∧
      ∀ x ∈ s, c x = 1) :=
  on_interval c (forces_progression (intervalColor c) red blue)

end OMA.Green160NearWitness

#print axioms OMA.Green160NearWitness.branch_on_interval
