import Graph189ProtectedOrder
import Graph189ProtectedExteriorSize

open Finset SimpleGraph
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- If deleting the unique low vertex leaves a Hamilton path, the actual
order still satisfies the structural lower bound at every admissible index
up to the degree of that vertex. This includes the one-unit lift whenever
its degree strictly exceeds the connectivity. -/
theorem order_of_traceable_low_deletion (z : V)
    (low : G.degree z < G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (nontrace : ¬ ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian)
    {x y : {v : V | v ≠ z}} (p : (G.induce {v : V | v ≠ z}).Walk x y) (hp : p.IsHamiltonian)
    {s : ℕ} (s3 : 3 ≤ s) (small : 2*s ≤ G.secondSmallestDegree) (sd : s ≤ G.degree z) :
    (s+1)*(G.secondSmallestDegree-s+2) ≤ Fintype.card V+1 := by
  classical
  by_contra! fail
  obtain ⟨a,b,Q,hQ,t,eq,maximal⟩ := exists_longest_through G z
  have size := protected_size_under_base_failure z (by omega) p hp Q hQ maximal
    (by omega : s ≤ G.secondSmallestDegree) sd fail
  have out : (Q.support.toFinsetᶜ : Finset V).Nonempty := by
    by_contra empty
    apply nontrace
    refine ⟨a,b,Q,hQ.isHamiltonian_of_mem (fun v => ?_)⟩
    by_contra absent
    exact empty ⟨v,by simpa using absent⟩
  have bound := protected_order_of_exterior_size Q hQ t (fun q hq h => maximal q hq (eq ▸ h))
    (eq ▸ low) cap out s3 small (by omega)
  omega

#print axioms order_of_traceable_low_deletion
end Graph189ExteriorGap
