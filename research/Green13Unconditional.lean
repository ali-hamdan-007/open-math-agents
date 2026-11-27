import Mathlib.Combinatorics.HalesJewett
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import FormalConjecturesForMathlib.Combinatorics.AP.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
The definition of an arithmetic progression comes from the pinned upstream module
FormalConjecturesForMathlib.Combinatorics.AP.Basic. The following two Green14
definitions are copied verbatim from FormalConjectures.GreensOpenProblems.14
at commit 9097e2f90e66d2f6244209cb1c07f7120d17ec53, so this standalone
verification can use focused imports.
-/

open Set

namespace Green14

/--
The set of natural numbers $N$ such that any 2-coloring of ${1, ..., N}$ contains a monochromatic
arithmetic progression of length $k$ (color 0) or length $r$ (color 1).
-/
def mixedMonoAPGuaranteeSet (k r : ℕ) : Set ℕ :=
  { N | ∀ coloring : Icc 1 N → Fin 2,
    (∃ s : Finset (Icc 1 N), ({(s' : ℕ) | s' ∈ s}).IsAPOfLength k ∧ ∀ x ∈ s, coloring x = 0) ∨
    (∃ s : Finset (Icc 1 N), ({(s' : ℕ) | s' ∈ s}).IsAPOfLength r ∧ ∀ x ∈ s, coloring x = 1) }

/--
We define the 2-colour van der Waerden numbers $W(k, r)$ to be the least quantities such that if
$\{1, ... , W(k, r)\}$ is coloured red and blue then there is either a red $k$-term progression
or a blue $r$-term progression.
-/
noncomputable def W (k r : ℕ) : ℕ := sInf (mixedMonoAPGuaranteeSet k r)


end Green14


/-!
The interval lemmas adapt Green14.W_3_12.R1 by @iskan-ai, which credits
@Halldon and Dominic Dabish. The coloring is independently kernel-checked
using bit intersections. A finite Hales–Jewett instance supplies existence
of a qualifying interval, so the infimum lower bound is unconditional.
-/

open Set Green14
open scoped Classical

namespace OMA.Green13Lower

theorem mixedMonoAPGuaranteeSet_upward (k r : ℕ) {M N : ℕ} (hMN : M ≤ N)
    (hM : M ∈ mixedMonoAPGuaranteeSet k r) :
    N ∈ mixedMonoAPGuaranteeSet k r := by
  intro coloring
  let emb : Icc 1 M ↪ Icc 1 N :=
    ⟨fun x ↦ ⟨x, x.2.1, x.2.2.trans hMN⟩, by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : Icc 1 N ↦ (z : Nat)) h⟩
  let restricted : Icc 1 M → Fin 2 := fun x ↦ coloring (emb x)
  rcases hM restricted with hzero | hone
  · left
    rcases hzero with ⟨s, hsAP, hsColor⟩
    let t : Finset (Icc 1 N) := s.map emb
    have hsets : ({(x : Nat) | x ∈ t} : Set Nat) = {(x : Nat) | x ∈ s} := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hx
        exact ⟨y,hy,rfl⟩
      · rintro ⟨y,hy,rfl⟩
        exact ⟨emb y,Finset.mem_map.mpr ⟨y,hy,rfl⟩,rfl⟩
    refine ⟨t, ?_, ?_⟩
    · rw [hsets]
      exact hsAP
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
      simpa [restricted] using hsColor y hy
  · right
    rcases hone with ⟨s, hsAP, hsColor⟩
    let t : Finset (Icc 1 N) := s.map emb
    have hsets : ({(x : Nat) | x ∈ t} : Set Nat) = {(x : Nat) | x ∈ s} := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hx
        exact ⟨y,hy,rfl⟩
      · rintro ⟨y,hy,rfl⟩
        exact ⟨emb y,Finset.mem_map.mpr ⟨y,hy,rfl⟩,rfl⟩
    refine ⟨t, ?_, ?_⟩
    · rw [hsets]
      exact hsAP
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
      simpa [restricted] using hsColor y hy

/-- One bad coloring of `{1, ..., N}` proves the numerical lower bound
`W(k,r) ≥ N+1`. -/
private theorem W_ge_succ_of_not_mem (k r N : ℕ)
    (hne : (mixedMonoAPGuaranteeSet k r).Nonempty) (hbad : N ∉ mixedMonoAPGuaranteeSet k r) :
    N + 1 ≤ W k r := by
  rw [W]
  apply le_csInf hne
  intro b hb
  by_contra hle
  have hbN : b ≤ N := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hle)
  exact hbad (mixedMonoAPGuaranteeSet_upward k r hbN hb)

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


private lemma extract_progression {N k : ℕ} (hk : 2 ≤ k) (q : ℕ → Fin 2) (col : Fin 2)
    (h : ∃ s : Finset (Icc 1 N), ({(x : ℕ) | x ∈ s}).IsAPOfLength k ∧
      ∀ x ∈ s, q (x.val-1) = col) :
    ∃ a d : Fin N, 0 < d.val ∧ a.val + (k-1)*d.val < N ∧
      ∀ i : Fin k, q (a.val + i.val*d.val) = col := by
  obtain ⟨s,⟨a,d,hcard,hset⟩,hc⟩ := h
  have term (i : ℕ) (hi : i < k) :
      ∃ x ∈ s, (x : ℕ) = a + i*d := by
    change a + i*d ∈ ({(x : ℕ) | x ∈ s} : Set ℕ)
    rw [hset]
    exact ⟨i, by exact_mod_cast hi, by simp⟩
  obtain ⟨x₀, -, hx₀⟩ := term 0 (by omega)
  simp only [Nat.zero_mul, Nat.add_zero] at hx₀
  obtain ⟨x₁, -, hx₁⟩ := term (k-1) (by omega)
  have ha : 1 ≤ a := hx₀ ▸ x₀.property.1
  have hb : a + (k-1)*d ≤ N := hx₁ ▸ x₁.property.2
  have hpos : 0 < d := by
    by_contra! hz
    have hd : d = 0 := by omega
    have heq : ({(x : ℕ) | x ∈ s} : Set ℕ) = {a} := by
      rw [hset]
      ext z
      simp only [hd, nsmul_zero, add_zero, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i,hi,rfl⟩
        rfl
      · rintro rfl
        exact ⟨0, by exact_mod_cast (show 0 < k by omega), rfl⟩
    have hone : (k : ℕ∞) = 1 := by rw [← hcard, heq]; simp
    have : k = 1 := by exact_mod_cast hone
    omega
  have hd' : d ≤ (k-1)*d := by
    simpa using Nat.mul_le_mul_right d (show 1 ≤ k-1 by omega)
  refine ⟨⟨a-1,by omega⟩,⟨d,by omega⟩,hpos,by change a-1+(k-1)*d < N; omega,?_⟩
  intro i
  obtain ⟨x,hx,hval⟩ := term i.val i.isLt
  have he := hc x hx
  change q (a - 1 + i.val*d) = col
  convert he using 2 <;> omega

namespace Witness

def redMask : Nat := 0x1400808110682005024002c40410828100082401

def blueMask : Nat := (2^159 - 1) ^^^ redMask

def color (i : Nat) : Fin 2 := if redMask.testBit i then 0 else 1

def intersect (mask d : Nat) (terms : List Nat) : Nat :=
  terms.foldr (fun t m => (mask >>> (t*d)) &&& m) (2^159 - 1)

theorem intersect_sound (mask a d : Nat) (terms : List Nat)
    (initial : (2^159 - 1 : Nat).testBit a = true)
    (h : ∀ t ∈ terms, mask.testBit (a+t*d) = true) :
    (intersect mask d terms).testBit a = true := by
  induction terms with
  | nil => exact initial
  | cons t ts ih =>
    change ((mask >>> (t*d)) &&& intersect mask d ts).testBit a = true
    rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.add_comm (t*d)]
    simp [h t (by simp), ih (fun u hu => h u (by simp [hu]))]

theorem bounds : ∀ a : Fin 159, (2^159 - 1 : Nat).testBit a.val = true := by decide +kernel

theorem checkRed : ∀ d : Fin 80, 0 < d.val →
    intersect redMask d.val (List.range 3) = 0 := by decide +kernel

theorem checkBlue : ∀ d : Fin 14, 0 < d.val →
    intersect blueMask d.val (List.range 13) = 0 := by decide +kernel

theorem no_red (a d : Nat) (hd : 0 < d) (hend : a + 2*d < 159) :
    ¬ ∀ i : Fin 3, color (a + i.val*d) = 0 := by
  intro h
  have hbit (t : Nat) (ht : t ∈ List.range 3) : redMask.testBit (a+t*d) = true := by
    have hh := h ⟨t,List.mem_range.mp ht⟩
    simpa [color] using hh
  have hh := intersect_sound redMask a d (List.range 3) (bounds ⟨a,by omega⟩) hbit
  have he := checkRed ⟨d,by omega⟩ hd
  change intersect redMask d (List.range 3) = 0 at he
  simp [he] at hh

theorem no_blue (a d : Nat) (hd : 0 < d) (hend : a + 12*d < 159) :
    ¬ ∀ i : Fin 13, color (a + i.val*d) = 1 := by
  intro h
  have hbit (t : Nat) (ht : t ∈ List.range 13) : blueMask.testBit (a+t*d) = true := by
    have ht' := List.mem_range.mp ht
    have hle := Nat.mul_le_mul_right d (show t ≤ 12 by omega)
    have hb : (2^159 - 1 : Nat).testBit (a+t*d) = true := bounds ⟨a+t*d,by omega⟩
    have hh : redMask.testBit (a+t*d) = false := by simpa [color] using h ⟨t,ht'⟩
    rw [blueMask, Nat.testBit_xor, hh, hb]
    rfl
  have hh := intersect_sound blueMask a d (List.range 13) (bounds ⟨a,by omega⟩) hbit
  have he := checkBlue ⟨d,by omega⟩ hd
  change intersect blueMask d (List.range 13) = 0 at he
  simp [he] at hh

end Witness

theorem lower_witness : 159 ∉ mixedMonoAPGuaranteeSet 3 13 := by
  intro h
  rcases h (fun x => Witness.color (x.val-1)) with hr | hb
  · obtain ⟨a,d,hd,hbound,hc⟩ := extract_progression (by decide : 2 ≤ 3) Witness.color 0 hr
    exact Witness.no_red a.val d.val hd hbound hc
  · obtain ⟨a,d,hd,hbound,hc⟩ := extract_progression (by decide : 2 ≤ 13) Witness.color 1 hb
    exact Witness.no_blue a.val d.val hd hbound hc

theorem lower_bound (hexists : (mixedMonoAPGuaranteeSet 3 13).Nonempty) :
    160 ≤ W 3 13 :=
  W_ge_succ_of_not_mem 3 13 159 hexists lower_witness

private theorem finiteGuarantee : (mixedMonoAPGuaranteeSet 3 13).Nonempty := by
  classical
  obtain ⟨ι, hιfin, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin 13) (Fin 2)
  let _ : Fintype ι := hιfin
  let N := 12 * Fintype.card ι + 1
  refine ⟨N, ?_⟩
  intro c
  have sumBound (v : ι → Fin 13) : (∑ j, (v j).val) < N := by
    have hle : (∑ j, (v j).val) ≤ ∑ _ : ι, 12 :=
      Finset.sum_le_sum fun j _ => Nat.le_of_lt_succ (v j).isLt
    simpa [N, Nat.mul_comm] using Nat.lt_succ_of_le hle
  let C (v : ι → Fin 13) : Fin 2 := c ⟨(∑ j, (v j).val) + 1, by
    constructor
    · omega
    · exact sumBound v⟩
  obtain ⟨l, color, hl⟩ := hι C
  let vary : Finset ι := Finset.univ.filter (fun j => l.idxFun j = none)
  let d := vary.card
  let a := ∑ j ∈ varyᶜ, ((l.idxFun j).map Fin.val).getD 0
  have hd : 0 < d := Finset.card_pos.mpr ⟨l.proper.choose, by
    simpa [vary] using l.proper.choose_spec⟩
  have sumEq (x : Fin 13) : (∑ j, (l x j).val) = a + x.val*d := by
    rw [← Finset.sum_add_sum_compl vary]
    have hleft : (∑ j ∈ vary, (l x j).val) = x.val*d := by
      rw [show x.val*d = ∑ _ ∈ vary, x.val by simp [d, Nat.mul_comm]]
      apply Finset.sum_congr rfl
      intro j hj
      have he : l.idxFun j = none := (Finset.mem_filter.mp hj).2
      rw [l.apply_none _ _ he]
    have hright : (∑ j ∈ varyᶜ, (l x j).val) = a := by
      apply Finset.sum_congr rfl
      intro j hj
      have hn : l.idxFun j ≠ none := by simpa [vary] using hj
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists.mp hn
      simp [← hy]
    rw [hleft, hright, Nat.add_comm]
  have mono (x : Fin 13) : ∀ hx : a+x.val*d < N,
      c ⟨a+x.val*d+1, by constructor <;> omega⟩ = color := by
    intro hx
    have he := hl x
    change c ⟨(∑ j, (l x j).val) + 1, _⟩ = color at he
    have hsub : (⟨(∑ j, (l x j).val) + 1, by
        constructor
        · omega
        · exact sumBound (l x)⟩ : Icc 1 N) =
        ⟨a+x.val*d+1, by constructor <;> omega⟩ := Subtype.ext (congrArg (· + 1) (sumEq x))
    rwa [hsub] at he
  have bound (x : Fin 13) : a+x.val*d < N := sumEq x ▸ sumBound (l x)
  have split : color = 0 ∨ color = 1 := (show ∀ y : Fin 2, y = 0 ∨ y = 1 by decide) color
  rcases split with rfl | rfl
  · left
    apply progression_at (a := a) hd c 0
    · intro i
      exact bound ⟨i.val, by omega⟩
    · intro i hi
      exact mono ⟨i.val, by omega⟩ hi
  · exact Or.inr (progression_at hd c 1 bound mono)

theorem lower_bound_unconditional : 160 ≤ W 3 13 := lower_bound finiteGuarantee

end OMA.Green13Lower

#print axioms OMA.Green13Lower.lower_bound_unconditional
