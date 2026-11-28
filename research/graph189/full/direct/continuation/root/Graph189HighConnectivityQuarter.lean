import Graph189QuarterOrder
import Graph189SixIndexOrder
import Graph189ActualScalarWidth
import Graph189MinimumBondyOrder
import Graph189ConnectivityDegree
import Graph189NearMinimumDegree
import Graph189TraceableDeletionOrder

open SimpleGraph Finset Graph189ExteriorDegreeCycle Graph189UniversalCycle
namespace Graph189HighConnectivityQuarter
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A counterexample forces the lower order at every index up to its
connectivity at which the exterior cycle yields a linked set. -/
theorem order_at_index (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (nontrace : ¬ ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian)
    {l : ℕ} (three : 3 ≤ l) (enough : l ≤ G.vertexConnectivity)
    (range : 4*l ≤ G.secondSmallestDegree+5) :
    (l+1)*(G.secondSmallestDegree-l+2) ≤ Fintype.card V+1 := by
  classical
  let k := G.secondSmallestDegree
  let n := Fintype.card V
  change 4*l ≤ k+5 at range
  have point (v : V) : G.distEven v ≤ k+1 := by
    have h := (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
    change _ ≤ 1+k at h
    omega
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  have minz : G.degree z=G.minDegree := hz.symm
  by_cases H : ∃ x y, ∃ p : (G.induce {v : V | v≠z}).Walk x y, p.IsHamiltonian
  · obtain ⟨x,y,p,hp⟩ := H
    have low := low_of_traceable_minimum_deletion (by omega) point nontrace z minz p hp
    exact Graph189ExteriorGap.order_of_traceable_low_deletion z low point nontrace p hp three
        (by change 2*l ≤ k; omega) (enough.trans (Graph189CutSides.connectivity_le_degree z))
  · have order := minimum_bondy_order z minz nontrace H point three
        (enough.trans (completeAt_connectivity z)) range
    change (l+1)*(k-l+2)-1 ≤ n at order
    change (l+1)*(k-l+2) ≤ n+1
    omega

/-- The moderate parent obligation is discharged at connectivity at least
three and second-smallest degree at least eight, including every order
up to the stated upper end. -/
theorem traceable_moderate (_hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (large : 8 ≤ G.secondSmallestDegree) (enough : 3 ≤ G.vertexConnectivity)
    (moderate : Fintype.card V ≤ 3*G.secondSmallestDegree+2) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  by_contra nontrace
  have lower := order_at_index cap nontrace (l := 3) (by decide) enough (by omega)
  change 4*(G.secondSmallestDegree-3+2) ≤ Fintype.card V+1 at lower
  omega

#print axioms traceable_moderate

/-- At second-smallest degree at least 26, connectivity at least the
quarter index already forces a Hamiltonian path in the actual graph. -/
theorem traceable (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (large : 26 ≤ G.secondSmallestDegree)
    (enough : (G.secondSmallestDegree+2)/4 ≤ G.vertexConnectivity) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  by_contra nontrace
  let k := G.secondSmallestDegree
  let n := Fintype.card V
  let l := (k+2)/4
  change 26 ≤ k at large
  change l ≤ G.vertexConnectivity at enough
  have three : 3 ≤ l := by dsimp [l]; omega
  have range : 4*l ≤ k+5 := by dsimp [l]; omega
  have lower : (l+1)*(k-l+2) ≤ n+1 := order_at_index cap nontrace three enough range
  have base := (Graph189QuarterOrder.lower_estimates large lower).1
  have width := Graph189ActualScalarWidth.bounds hc cap nontrace (by change 4*k+2 ≤ n; omega)
  exact Graph189QuarterOrder.impossible large lower width.1 width.2.1 width.2.2.2.1 width.2.2.2.2

/-- At degrees 19 through 25, connectivity six supplies an order bound
strong enough for the integer width contradiction. -/
theorem traceable_six (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (small : 19 ≤ G.secondSmallestDegree) (large : G.secondSmallestDegree ≤ 25)
    (enough : 6 ≤ G.vertexConnectivity) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  by_contra nontrace
  let k := G.secondSmallestDegree
  let n := Fintype.card V
  change 19 ≤ k at small
  change k ≤ 25 at large
  have lower := order_at_index cap nontrace (l := 6) (by decide) enough
    (by change 4*6 ≤ k+5; omega)
  change (6+1)*(k-6+2) ≤ n+1 at lower
  have lowerZ : 7*((k:ℤ)-4)-1 ≤ (n:ℤ) := by omega
  have width := Graph189ActualScalarWidth.bounds hc cap nontrace
    (by change 4*k+2 ≤ n; omega)
  exact Graph189SixIndexOrder.impossible (by exact_mod_cast small) (by exact_mod_cast large)
    lowerZ width.1 width.2.1 width.2.2.2.1 width.2.2.2.2

#print axioms traceable_six
#print axioms traceable
end Graph189HighConnectivityQuarter
