import Graph189ExcludeValid
import Graph189TerminalGraph

namespace Graph189StructuralConclusion
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- For the high-degree, small-connectivity range, the two structural lower
bounds alone imply an actual Hamiltonian path under the original even cap. -/
theorem traceable_of_structural_lower_bounds (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (deletion : ∀ z : V, (G.induce {v : V | v ≠ z}).Connected)
    (hs : 5≤G.vertexConnectivity) (hk : 26≤G.secondSmallestDegree)
    (ratio : 3*G.vertexConnectivity<G.secondSmallestDegree) :
    let s : ℤ := G.vertexConnectivity
    let k : ℤ := G.secondSmallestDegree
    let n : ℤ := Fintype.card V
    let d : ℤ := Graph189EffectiveDeficit.effectiveDeficit G
    (s+1)*(k-s+2)-1≤n →
    (3*s<2*(k-d-1) → 2*s≤k-2*d-2 → 4*n<k*(k-1) →
      (s+2)*(k-d-s+1)-1≤n) →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  intro s k n d baseline lift
  by_contra bad
  obtain ⟨r,rs,rk,order,valid⟩ :=
    Graph189TerminalGraph.exists_valid_band hc cap bad hs hk ratio baseline lift
  have point (v : V) : G.distEven v≤1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  exact Graph189ExcludeValid.impossible hc point deletion valid rs rk order

#print axioms traceable_of_structural_lower_bounds
end Graph189StructuralConclusion
