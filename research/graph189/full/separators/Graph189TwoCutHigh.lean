import Graph189TwoCutCounting
import Graph189SeparatorCounts

namespace Graph189TwoCutCounting
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The high-contact branch has exactly three components and second degree at
most six, once each noncut component is represented by a contact label. -/
theorem high_contact_three_and_degree_le_six {ι : Type*} [DecidableEq ι]
    (region : V → ι) (C : Finset V) (p q : V) (k : ℕ) (hk : 3 ≤ k)
    (chosen : ∀ i ∈ C.image region,
      ∃ x ∈ C, region x = i ∧ G.Adj p x ∧ k ≤ G.degree x)
    (hn : ∀ x ∈ C, ∀ y ∈ C, region x ≠ region y → ¬ G.Adj x y)
    (hclosed : ∀ x ∈ C, G.neighborFinset x ⊆ insert p (insert q C))
    (cap : ∀ x : V, (univ.filter (fun y => G.dist x y = 2)).card ≤ k)
    (ht : 3 ≤ (C.image region).card) :
    (C.image region).card = 3 ∧ k ≤ 6 := by
  classical
  let A := C.filter (G.Adj p)
  let L := C.image region
  let t := L.card
  change 3 ≤ t at ht
  change t = 3 ∧ k ≤ 6
  have hAL : A.image region = L := by
    ext i
    constructor
    · intro hi
      obtain ⟨x,hx,hi⟩ := Finset.mem_image.mp hi
      exact Finset.mem_image.mpr ⟨x,(Finset.mem_filter.mp hx).1,hi⟩
    · intro hi
      obtain ⟨x,hx,he,hp,_⟩ := chosen i hi
      exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,hp⟩,he⟩
  have hc := external_count region A p k
    (fun _ hx => (Finset.mem_filter.mp hx).2)
    (fun x hx y hy => hn x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1) cap
  rw [hAL] at hc
  change t*A.card ≤ t*k+A.card at hc
  have hI := internal_count_sum region C L p q k chosen hn hclosed (cap p)
  change t*(k-1) ≤ A.card+k at hI
  have e : (t:ℤ)*A.card ≤ (t:ℤ)*k+A.card := by exact_mod_cast hc
  have i : (t:ℤ)*((k:ℤ)-1) ≤ (A.card:ℤ)+k := by
    have hz : ((k-1 : ℕ) : ℤ) = (k:ℤ)-1 := Int.ofNat_sub (by omega)
    have hi : (t:ℤ)*((k-1 : ℕ):ℤ) ≤ (A.card:ℤ)+k := by exact_mod_cast hI
    rwa [hz] at hi
  have hkz : (3:ℤ) ≤ k := by exact_mod_cast hk
  have ht3 : t = 3 := by
    by_contra ht'
    have ht4 : 4 ≤ (t:ℤ) := by exact_mod_cast (show 4 ≤ t by omega)
    have il : 4*((k:ℤ)-1) ≤ (A.card:ℤ)+k :=
      (mul_le_mul_of_nonneg_right ht4 (by omega)).trans i
    have hAk : (k:ℤ) ≤ A.card := by linarith
    have hextra := mul_nonneg (show 0 ≤ (t:ℤ)-4 by omega)
      (show 0 ≤ (A.card:ℤ)-k by omega)
    have el : 3*(A.card:ℤ) ≤ 4*(k:ℤ) := by nlinarith
    exact Graph189SeparatorCounts.two_cut_four_components hkz il el
  have htZ : (t:ℤ) = 3 := by exact_mod_cast ht3
  rw [htZ] at i e
  have e' : 2*(A.card:ℤ) ≤ 3*(k:ℤ) := by linarith
  exact ⟨ht3,by exact_mod_cast (Graph189SeparatorCounts.two_cut_three_components i e')⟩

#print axioms high_contact_three_and_degree_le_six
end Graph189TwoCutCounting
