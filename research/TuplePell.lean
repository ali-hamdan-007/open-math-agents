import Lean

namespace TuplePell

private theorem sq_le_sq {a b : Int} (ha : 0 ≤ a) (hab : a ≤ b) : a*a ≤ b*b := by
  exact Int.mul_le_mul hab hab ha (by omega)

private theorem descend_three (x y : Int) (hx : 1 < x) (hy : 0 < y)
    (he : y*y - 3*x*x = -2) :
    0 < 2*x-y ∧ 2*x-y < x ∧ 0 < 2*y-3*x ∧
    (2*y-3*x)*(2*y-3*x) - 3*(2*x-y)*(2*x-y) = -2 := by
  have hx2 : 4 ≤ x*x := by simpa using (sq_le_sq (a := 2) (by decide) (by omega : 2 ≤ x))
  have h₁ : y < 2*x := by
    apply Int.lt_of_not_ge
    intro h
    have hh := sq_le_sq (show 0 ≤ 2*x by omega) (show 2*x ≤ y by omega)
    grind
  have h₂ : x < y := by
    apply Int.lt_of_not_ge
    intro h
    have hh := sq_le_sq (show 0 ≤ y by omega) (show y ≤ x by omega)
    grind
  have h₃ : 3*x < 2*y := by
    apply Int.lt_of_not_ge
    intro h
    have hh := sq_le_sq (show 0 ≤ 2*y by omega) (show 2*y ≤ 3*x by omega)
    grind
  refine ⟨by omega, by omega, by omega, ?_⟩
  grind


private theorem descend_eight (x z : Int) (hx : 2 < x) (hz : 0 < z)
    (he : z*z - 8*x*x = -7) :
    0 < 3*x-z ∧ 3*x-z < x ∧ 0 < 3*z-8*x ∧
    (3*z-8*x)*(3*z-8*x) - 8*(3*x-z)*(3*x-z) = -7 := by
  have hx2 : 9 ≤ x*x := by simpa using (sq_le_sq (a := 3) (by decide) (by omega : 3 ≤ x))
  have h₁ : z < 3*x := by
    apply Int.lt_of_not_ge
    intro h
    have hh := sq_le_sq (show 0 ≤ 3*x by omega) h
    grind
  have h₂ : 2*x < z := by
    apply Int.lt_of_not_ge
    intro h
    have hh := sq_le_sq (show 0 ≤ z by omega) h
    grind
  have h₃ : 8*x < 3*z := by
    apply Int.lt_of_not_ge
    intro h
    have hh := sq_le_sq (show 0 ≤ 3*z by omega) h
    grind
  refine ⟨by omega, by omega, by omega, ?_⟩
  grind

/-- The orbit of `(1, 1)` under multiplication by `2 + √3`.
    The first coordinate multiplies `√3`. -/
def three : Nat → Int × Int
  | 0 => (1, 1)
  | n+1 => let (x,y) := three n; (2*x+y, 3*x+2*y)

/-- The two positive orbits under multiplication by `3 + √8`.
    The first coordinate multiplies `√8`. -/
def eight (second : Bool) : Nat → Int × Int
  | 0 => if second then (2, 5) else (1, 1)
  | n+1 => let (x,z) := eight second n; (3*x+z, 8*x+3*z)

theorem three_complete (x y : Int) (hx : 0 < x) (hy : 0 < y)
    (he : y*y - 3*x*x = -2) : ∃ n, three n = (x,y) := by
  if h : x = 1 then
    subst x
    have hyy : y = 1 := by
      have hh : (y-1)*(y+1) = 0 := by grind
      rcases Int.mul_eq_zero.mp hh with h | h <;> omega
    exact ⟨0, by simp [three, hyy]⟩
  else
    obtain ⟨hx', hlt, hy', he'⟩ := descend_three x y (by omega) hy he
    obtain ⟨n, hn⟩ := three_complete (2*x-y) (2*y-3*x) hx' hy' he'
    refine ⟨n+1, ?_⟩
    simp only [three, hn, Prod.mk.injEq]
    omega
termination_by x.toNat
decreasing_by omega

theorem eight_complete (x z : Int) (hx : 0 < x) (hz : 0 < z)
    (he : z*z - 8*x*x = -7) : ∃ b n, eight b n = (x,z) := by
  if h : x = 1 then
    subst x
    have hzz : z = 1 := by
      have hh : (z-1)*(z+1) = 0 := by grind
      rcases Int.mul_eq_zero.mp hh with h | h <;> omega
    exact ⟨false, 0, by simp [eight, hzz]⟩
  else if h₂ : x = 2 then
    subst x
    have hzz : z = 5 := by
      have hh : (z-5)*(z+5) = 0 := by grind
      rcases Int.mul_eq_zero.mp hh with h | h <;> omega
    exact ⟨true, 0, by simp [eight, hzz]⟩
  else
    obtain ⟨hx', hlt, hz', he'⟩ := descend_eight x z (by omega) hz he
    obtain ⟨b, n, hn⟩ := eight_complete (3*x-z) (3*z-8*x) hx' hz' he'
    refine ⟨b, n+1, ?_⟩
    simp only [eight, hn, Prod.mk.injEq]
    omega
termination_by x.toNat
decreasing_by omega


private theorem three_sound (n : Nat) :
    let (x,y) := three n
    0 < x ∧ 0 < y ∧ y*y - 3*x*x = -2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    generalize he : three n = p at ih
    obtain ⟨x,y⟩ := p
    change 0 < x ∧ 0 < y ∧ y*y - 3*x*x = -2 at ih
    simp only [three, he]
    exact ⟨by omega, by omega, by grind⟩

private theorem eight_sound (b : Bool) (n : Nat) :
    let (x,z) := eight b n
    0 < x ∧ 0 < z ∧ z*z - 8*x*x = -7 := by
  induction n with
  | zero => cases b <;> decide
  | succ n ih =>
    generalize he : eight b n = p at ih
    obtain ⟨x,z⟩ := p
    change 0 < x ∧ 0 < z ∧ z*z - 8*x*x = -7 at ih
    simp only [eight, he]
    exact ⟨by omega, by omega, by grind⟩

/-- Completing `{1,3,8}` is equivalent to matching the first coordinates of
    the two Pell recurrences. The case `d = 0` is included. -/
theorem extension_iff (d : Int) :
    (∃ x y z : Int, 0 < x ∧ 0 < y ∧ 0 < z ∧
      d + 1 = x*x ∧ 3*d + 1 = y*y ∧ 8*d + 1 = z*z) ↔
    ∃ n b m, (three n).1 = (eight b m).1 ∧ d = (three n).1 * (three n).1 - 1 := by
  constructor
  · rintro ⟨x, y, z, hx, hy, hz, hdx, hdy, hdz⟩
    obtain ⟨n, hn⟩ := three_complete x y hx hy (by grind)
    obtain ⟨b, m, hm⟩ := eight_complete x z hx hz (by grind)
    exact ⟨n, b, m, by simp [hn, hm], by simp [hn]; omega⟩
  · rintro ⟨n, b, m, hm, hd⟩
    have h₃ := three_sound n
    have h₈ := eight_sound b m
    generalize hpn : three n = p at h₃ hm hd
    generalize hqm : eight b m = q at h₈ hm
    obtain ⟨x,y⟩ := p
    obtain ⟨u,z⟩ := q
    change 0 < x ∧ 0 < y ∧ y*y - 3*x*x = -2 at h₃
    change 0 < u ∧ 0 < z ∧ z*z - 8*u*u = -7 at h₈
    change x = u at hm
    subst u
    exact ⟨x, y, z, h₃.1, h₃.2.1, h₈.2.1, by grind, by grind, by grind⟩


private theorem monotone_first (f : Nat → Int) (hs : ∀ n, f n ≤ f (n+1))
    (m n : Nat) (hmn : m ≤ n) : f m ≤ f n := by
  induction n with
  | zero =>
    obtain rfl : m = 0 := by omega
    exact Int.le_refl _
  | succ n ih =>
    if h : m ≤ n then exact Int.le_trans (ih h) (hs n)
    else
      obtain rfl : m = n + 1 := by omega
      exact Int.le_refl _

private theorem three_grows (n : Nat) : (three n).1 ≤ (three (n+1)).1 := by
  have hs := three_sound n
  cases ht : three n with
  | mk x y =>
    rw [ht] at hs
    simp only [three, ht]
    obtain ⟨hx,hy,-⟩ := hs
    omega

private theorem eight_grows (b : Bool) (n : Nat) : (eight b n).1 ≤ (eight b (n+1)).1 := by
  have hs := eight_sound b n
  cases ht : eight b n with
  | mk x z =>
    rw [ht] at hs
    simp only [eight, ht]
    obtain ⟨hx,hz,-⟩ := hs
    omega

private def prefixThree : List Int := (List.range 200).map fun n => (three n).1

private def prefixEight : List Int :=
  (List.range 200).flatMap fun n => [(eight false n).1, (eight true n).1]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
private theorem prefix_intersection :
    prefixThree.filter (fun x => prefixEight.elem x) = [1, 11] := by decide +kernel

set_option maxRecDepth 10000 in
/-- Below `10^200`, the only nonnegative values satisfying the square
    conditions are `0` and `120`. -/
theorem extension_below (d x y z : Int) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hdx : d + 1 = x*x) (hdy : 3*d + 1 = y*y) (hdz : 8*d + 1 = z*z)
    (hbound : d < 10^200) : d = 0 ∨ d = 120 := by
  obtain ⟨n, hn⟩ := three_complete x y hx hy (by grind)
  obtain ⟨b, m, hm⟩ := eight_complete x z hx hz (by grind)
  have hxbound : x ≤ (10^100 : Int) := by
    apply Int.le_of_not_gt
    intro hh
    have hsq := sq_le_sq (show 0 ≤ (10^100 : Int) + 1 by decide) (show (10^100 : Int) + 1 ≤ x by omega)
    have hp : ((10^100 : Int) + 1) * (10^100 + 1) > 10^200 := by decide +kernel
    rw [← hdx] at hsq
    omega
  have hn' : n < 200 := by
    apply Nat.lt_of_not_ge
    intro h
    have hg := monotone_first (fun n => (three n).1) three_grows 200 n h
    change (three 200).1 ≤ (three n).1 at hg
    rw [hn] at hg
    have hp : (10^100 : Int) < (three 200).1 := by decide +kernel
    exact Int.not_lt.mpr hxbound (Int.lt_of_lt_of_le hp hg)
  have hm' : m < 200 := by
    apply Nat.lt_of_not_ge
    intro h
    have hg := monotone_first (fun n => (eight b n).1) (eight_grows b) 200 m h
    change (eight b 200).1 ≤ (eight b m).1 at hg
    rw [hm] at hg
    have hp : (10^100 : Int) < (eight b 200).1 := by cases b <;> decide
    exact Int.not_lt.mpr hxbound (Int.lt_of_lt_of_le hp hg)
  have hx₃ : x ∈ prefixThree :=
    List.mem_map.mpr ⟨n, List.mem_range.mpr hn', by simp [hn]⟩
  have hx₈ : x ∈ prefixEight := by
    apply List.mem_flatMap.mpr
    refine ⟨m, List.mem_range.mpr hm', ?_⟩
    cases b <;> simp_all
  have hh : x ∈ prefixThree.filter (fun x => prefixEight.elem x) := List.mem_filter.mpr ⟨hx₃, List.elem_iff.mpr hx₈⟩
  rw [prefix_intersection] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl <;> omega

#print axioms extension_iff
#print axioms extension_below

end TuplePell
