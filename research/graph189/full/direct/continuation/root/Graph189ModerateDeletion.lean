import Graph189TraceableDeletionOrder
import Graph189NearMinimumDegree

open Finset SimpleGraph Graph189ExteriorGap Graph189ExteriorDegreeCycle
namespace Graph189ModerateDeletion

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In the moderate order range a Hamiltonian minimum deletion gives a
Hamiltonian path in the full graph if its minimum degree is at least three.
At minimum degree two the same conclusion holds up to order 3k−1. -/
theorem traceable (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (large : 8 ≤ G.secondSmallestDegree) (moderate : Fintype.card V ≤ 3*G.secondSmallestDegree+2)
    (z : V) (minimum : G.degree z=G.minDegree) (two : 2 ≤ G.degree z)
    (range : 3 ≤ G.degree z ∨ Fintype.card V < 3*G.secondSmallestDegree)
    {x y : {v : V | v ≠ z}} (p : (G.induce {v : V | v ≠ z}).Walk x y) (hp : p.IsHamiltonian) :
    ∃ a b, ∃ q : G.Walk a b, q.IsHamiltonian := by
  classical
  by_contra nontrace
  let k := G.secondSmallestDegree
  let n := Fintype.card V
  change 8 ≤ k at large
  change n ≤ 3*k+2 at moderate
  change 3 ≤ G.degree z ∨ n < 3*k at range
  have point (v : V) : G.distEven v ≤ k+1 := by
    have h := (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
    change _ ≤ 1+k at h
    omega
  have low := low_of_traceable_minimum_deletion (by change 5 ≤ k; omega) point nontrace z minimum p hp
  by_cases three : 3 ≤ G.degree z
  · have lower := order_of_traceable_low_deletion z low point nontrace p hp (s:=3)
      (by decide) (by change 2*3 ≤ k; omega) three
    change 4*(k-3+2) ≤ n+1 at lower
    omega
  have deg : G.degree z=2 := by omega
  obtain ⟨a,b,Q,hQ,t,eq,maximal⟩ := exists_longest_through G z
  have gap := protected_size_of_traceable_deletion z (by omega) p hp Q hQ maximal
  let m := (Q.support.toFinsetᶜ : Finset V).card
  rw [deg] at gap
  change 1+2+(2+1)*m ≤ n at gap
  have out : (Q.support.toFinsetᶜ : Finset V).Nonempty := by
    by_contra empty
    apply nontrace
    refine ⟨a,b,Q,hQ.isHamiltonian_of_mem (fun v => ?_)⟩
    by_contra absent
    exact empty ⟨v,by simpa using absent⟩
  have lower := protected_order_of_exterior_size Q hQ t (fun q hq h => maximal q hq (eq ▸ h))
    (eq ▸ low) point out (s:=3) (by decide) (by change 2*3 ≤ k; omega)
    (by change m+3 ≤ k+1; omega)
  change 4*(k-3+2) ≤ n+1 at lower
  omega

#print axioms traceable
end Graph189ModerateDeletion
