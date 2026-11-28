import Graph189ConeExteriorCycle
import Graph189HighMinimumGap

namespace Graph189ExteriorDegreeCycle
open SimpleGraph Graph189UniversalCycle
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every longest cycle in a completion at any vertex of a qualifying
nontraceable graph with minimum degree greater than half the second degree
has a long cycle in its actual exterior. -/
theorem arbitrary_completion_exterior (w : V) {z : V} (C : (completeAt G w).Walk z z)
    (hc : C.IsCycle) (longest : ∀ v (Q : (completeAt G w).Walk v v), Q.IsCycle → Q.length ≤ C.length)
    (notTrace : ¬ ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian)
    (k5 : 5 ≤ G.secondSmallestDegree) (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    {d : ℕ} (two : 2 ≤ d) (room : G.secondSmallestDegree+2*d+2 ≤ 2*G.minDegree) :
    ∃ a, ∃ Q : ((completeAt G w).induce {t : V | t ∉ C.support}).Walk a a,
      Q.IsCycle ∧ d+1 ≤ Q.length := by
  have half' (v : V) : G.secondSmallestDegree < 2*G.degree v := by
    have := G.minDegree_le_degree v
    omega
  apply completeAt_exterior_cycle (D:=G.minDegree-1) w C hc longest
    (high_min_all_paths_gap notTrace k5 cap half') (by omega) cap _ two (by omega)
  intro v
  have := G.minDegree_le_degree v.val
  omega

/-- At a minimum-degree completion, all retained original vertices have degree
at least the original second degree. This gives the full original cone length
from any independently supplied gap of four real vertices. -/
theorem minimum_completion_exterior_of_gap (w : V) (minw : G.degree w = G.minDegree)
    {z : V} (C : (completeAt G w).Walk z z) (hc : C.IsCycle)
    (longest : ∀ v (Q : (completeAt G w).Walk v v), Q.IsCycle → Q.length ≤ C.length)
    (gap : ∀ a b, ∀ p : G.Walk a b, p.IsPath → p.support.length+3 < Fintype.card V)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    {d : ℕ} (two : 2 ≤ d) (room : 2*d+2 ≤ G.secondSmallestDegree) :
    ∃ a, ∃ Q : ((completeAt G w).induce {t : V | t ∉ C.support}).Walk a a,
      Q.IsCycle ∧ d+1 ≤ Q.length := by
  apply completeAt_exterior_cycle (D:=G.secondSmallestDegree-1) w C hc longest gap
    (by omega) cap _ two (by omega)
  intro v
  have high : G.secondSmallestDegree ≤ G.degree v.val := by
    rcases degree_pair (G:=G) v.val w v.property with h|h
    · exact h
    · rw [minw] at h
      exact h.trans (G.minDegree_le_degree v.val)
  omega

/-- For a nontraceable minimum-vertex deletion there is a long exterior cycle
of the minimum completion under the original graph hypotheses alone. -/
theorem minimum_completion_exterior_of_nontraceable_deletion (w : V) (minw : G.degree w = G.minDegree)
    {z : V} (C : (completeAt G w).Walk z z) (hc : C.IsCycle)
    (longest : ∀ v (Q : (completeAt G w).Walk v v), Q.IsCycle → Q.length ≤ C.length)
    (notTrace : ¬ ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian)
    (notH : ¬ ∃ a b, ∃ p : (G.induce {v : V | v ≠ w}).Walk a b, p.IsHamiltonian)
    (k5 : 5 ≤ G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) (minimum : ∀ v, 3 ≤ G.degree v)
    {d : ℕ} (two : 2 ≤ d) (room : 2*d+2 ≤ G.secondSmallestDegree) :
    ∃ a, ∃ Q : ((completeAt G w).induce {t : V | t ∉ C.support}).Walk a a,
      Q.IsCycle ∧ d+1 ≤ Q.length := by
  apply minimum_completion_exterior_of_gap w minw C hc longest _ cap two room
  apply gap_of_no_hamiltonian_low_deletion notTrace k5 cap minimum
  intro v hv
  have vw : v=w := by
    by_contra ne
    have wd := G.minDegree_le_degree v
    rcases degree_pair (G:=G) v w ne with h|h <;> omega
  subst v
  exact notH

#print axioms minimum_completion_exterior_of_nontraceable_deletion
#print axioms arbitrary_completion_exterior
#print axioms minimum_completion_exterior_of_gap
end Graph189ExteriorDegreeCycle
