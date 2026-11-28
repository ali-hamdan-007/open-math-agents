import Graph189InfiniteTail
import Graph189WidthInterval

namespace Graph189GraphTail
open Graph189WidthInterval Graph189InfiniteTail
open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

/-- The quadratic endpoint retained by the continuous test has enough degree
excess to supply the same normalized square bound as the actual maximum root. -/
private theorem interval_square {k n : ℤ} (hk : 0 < k)
    (hi : n ≤ 4*k+2 ∨ (low k n ≤ 3*k ∧
      min (difference k n (low k n)) (difference k n (3*k)) ≤ 0))
    (hx : 9 ≤ (n : ℚ)/(k : ℚ)) : 3*((n : ℚ)/(k : ℚ)-9)^2 ≤ (k : ℚ)+1 := by
  have hkq : 0 < (k : ℚ) := by exact_mod_cast hk
  have hk1 : (1:ℚ) ≤ (k : ℚ) := by exact_mod_cast (show 1 ≤ k by omega)
  rcases hi with hsmall | ⟨hb,hm⟩
  · have hsmall' : (n : ℚ) ≤ 4*(k : ℚ)+2 := by exact_mod_cast hsmall
    have hlarge := (le_div_iff₀ hkq).mp hx
    linarith
  · obtain ⟨d,hl,hh,hd⟩ : ∃ d : ℤ, low k n ≤ d ∧ d ≤ 3*k ∧ difference k n d ≤ 0 := by
      rcases le_total (difference k n (low k n)) (difference k n (3*k)) with h|h
      · exact ⟨_, le_rfl,hb,min_eq_left h ▸ hm⟩
      · exact ⟨_, hb,le_rfl,min_eq_right h ▸ hm⟩
    have hdk : k ≤ d := by unfold low at hl; omega
    have hround : -((-(n-3*k-1))/k) ≤ d-k := by unfold low at hl; omega
    have hfloor := Int.ediv_mul_le (-(n-3*k-1)) hk.ne'
    have hmult := mul_le_mul_of_nonneg_right hround hk.le
    have hroot : n ≤ 3*k+1+k*(d-k) := by nlinarith only [hfloor, hmult]
    unfold difference at hd
    have hwidth : (n-2*k-(d-k)-2)*(2*(n-2*k)+k*(d-k)) ≤ k*(k+1)*(k+(d-k)) := by
      nlinarith only [hd]
    apply square_order_bound (n := (n : ℚ)) (k := (k : ℚ))
      (e := (d : ℚ)-(k : ℚ)) (x := (n : ℚ)/(k : ℚ)) hk1
    · exact_mod_cast (show 0 ≤ d-k by omega)
    · exact_mod_cast (show d-k ≤ 2*k by omega)
    · rw [mul_comm, div_mul_cancel₀ _ hkq.ne']
    · exact_mod_cast hroot
    · exact_mod_cast hwidth
    · exact hx

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Unconditional order bound for every original Graph 189 counterexample. -/
theorem graph_square_order_bound (hc : G.Connected)
    (hcap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (hn : ¬ ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian) :
    let k : ℚ := G.secondSmallestDegree
    let n : ℚ := Fintype.card V
    9 ≤ n/k → 3*(n/k-9)^2 ≤ k+1 := by
  classical
  obtain ⟨p,q,_⟩ := exists_pair_ne V
  have hp := hc.preconnected.degree_pos_of_nontrivial p
  have hd := G.degree_le_maxDegree p
  have cap (v : V) : G.distEven v ≤ 1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans hcap
  have hm := Graph189DegreeCeiling.maxDegree_le_three_mul_secondSmallestDegree hc cap
  have hk : (0:ℤ) < G.secondSmallestDegree := by exact_mod_cast (show 0 < G.secondSmallestDegree by omega)
  simpa using interval_square hk (necessary_interval hc hcap hn)

/-- The actual graph width supplies the global square-order input. The only
remaining premises for the outer rectangle are the explicit separator bounds. -/
theorem graph_finite_rectangle (hc : G.Connected)
    (hcap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (hn : ¬ ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian) (s : ℚ) (hs : 5 ≤ s) :
    let k : ℚ := G.secondSmallestDegree
    let n : ℚ := Fintype.card V
    3*s < k → (s+1)*(k-s+2)-1 ≤ n →
    (n-2*k-1)*(k-s) ≤ s*k*k →
    (4*s ≤ k → 4*n < k*(k-1) → (s+2)*(k-2*s+2)-1 ≤ n) →
    (6*(s-1) < k → 2*n < (2*s+3)*k+4*s+4) →
    (6*(s-1) < k → (s-2)*(n-2*s-3) < ((s+1)*(s-2)+3)*k) →
    s < 100 ∧ k < 4*s^2+8*s-2 := by
  intro k n hk ho hside hbridge hcut1 hcut2
  exact ⟨connectivity_lt_100 hk ho hside (graph_square_order_bound hc hcap hn)
    hbridge hcut2, degree_lt_cutoff hs hbridge hcut1⟩

end Graph189GraphTail

#print axioms Graph189GraphTail.graph_square_order_bound
#print axioms Graph189GraphTail.graph_finite_rectangle
