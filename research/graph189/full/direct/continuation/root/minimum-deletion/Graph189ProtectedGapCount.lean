import Graph189ContactGroupCensus
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset
namespace Graph189ContactGroupCensus

/-- Disjoint legal intervals contribute a full detour length, except possibly
one interval containing the prescribed vertex, which contributes at least one. -/
theorem protected_gap_sum {I : Type*} [DecidableEq I] (Gaps : Finset I) (len : I→ℕ)
    {g m : ℕ} (count : Gaps.card=g+1) (positive : 1≤m)
    (short_has_vertex : ∀ i∈Gaps, len i<m → 1≤len i)
    (short_unique : ∀ i∈Gaps, ∀ j∈Gaps, len i<m → len j<m → i=j) :
    g*m+1≤∑ i∈Gaps, len i := by
  classical
  by_cases short : ∃ i∈Gaps, len i<m
  · obtain ⟨i,inside,small⟩ := short
    have upper := short_has_vertex i inside small
    have rest := sum_le_sum (s:=Gaps.erase i) (f:=fun _ => m) (g:=len) (by
      intro j hj
      obtain ⟨ne,hj⟩ := mem_erase.mp hj
      exact le_of_not_gt fun little => ne (short_unique j hj i inside little small))
    rw [sum_const,nsmul_eq_mul,card_erase_of_mem inside,count] at rest
    have add := sum_erase_add (s:=Gaps) len inside
    omega
  · have lower := sum_le_sum (s:=Gaps) (f:=fun _ => m) (g:=len) (by
      intro i hi
      exact le_of_not_gt fun little => short ⟨i,hi,little⟩)
    rw [sum_const,nsmul_eq_mul,count,Nat.add_mul,one_mul] at lower
    omega

/-- With fewer than u−1 surplus vertices in u legal gaps, two legal gaps
have exactly the exterior order. Both can be exchanged independently. -/
theorem two_full_gaps {I : Type*} [DecidableEq I] (Gaps : Finset I) (len : I→ℕ)
    {u m : ℕ} (many : u≤Gaps.card) (bound : ∀ i∈Gaps, m≤len i)
    (sumRoom : (∑ i∈Gaps, len i)+2≤u*m+u) :
    ∃ a∈Gaps, ∃ b∈Gaps, a≠b ∧ len a=m ∧ len b=m := by
  classical
  let T := Gaps.filter fun i => len i=m
  let R := Gaps \ T
  have split := sum_sdiff (f:=len) (filter_subset (fun i => len i=m) Gaps)
  have cards := card_sdiff_add_card_eq_card (filter_subset (fun i => len i=m) Gaps)
  change (∑ i∈R, len i)+(∑ i∈T, len i)=_ at split
  change R.card+T.card=Gaps.card at cards
  have left := sum_le_sum (s:=T) (f:=fun _ => m) (g:=len) (by
    intro i hi
    exact (mem_filter.mp hi).2.ge)
  have right := sum_le_sum (s:=R) (f:=fun _ => m+1) (g:=len) (by
    intro i hi
    obtain ⟨inside,miss⟩ := mem_sdiff.mp hi
    have ne : len i≠m := fun eq => miss (mem_filter.mpr ⟨inside,eq⟩)
    exact lt_of_le_of_ne (bound i inside) ne.symm)
  rw [sum_const,nsmul_eq_mul] at left right
  have times := Nat.mul_le_mul_right m many
  have card : 1<T.card := by nlinarith [congrArg (fun a : ℕ => a*m) cards]
  obtain ⟨a,ha⟩ := card_pos.mp (by omega : 0<T.card)
  obtain ⟨b,hb,ne⟩ := exists_mem_ne card a
  exact ⟨a,(mem_filter.mp ha).1,b,(mem_filter.mp hb).1,ne.symm,
    (mem_filter.mp ha).2,(mem_filter.mp hb).2⟩

end Graph189ContactGroupCensus
