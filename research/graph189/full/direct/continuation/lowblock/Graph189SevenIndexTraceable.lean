import Graph189RotationMinOrder
import Graph189TraceableDeletionOrder
import Graph189ActualScalarWidth
import Graph189ConnectivityDegree
import Graph189NearMinimumDegree

open SimpleGraph Finset Graph189UniversalCycle
namespace Graph189SevenIndexTraceable
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At degrees sixteen through eighteen, the seven-index lower bound already
exceeds the integer geometric width upper bound throughout the excess range. -/
private theorem no_width {k n e w : ℤ} (lo : 16 ≤ k) (hi : k ≤ 18)
    (lower : 8*(k-5)-1 ≤ n) (ep : 0 ≤ e) (em : e ≤ 2*k)
    (width : 2*(n-2*k)+k*e ≤ (k+1)*w)
    (budget : w*(n-2*k-e-2) ≤ k*(k+e)) : False := by
  let b := 8*(k-5)-1
  have wp : 0 ≤ w := by
    by_contra! neg
    have := mul_neg_of_pos_of_neg (by omega : 0 < k+1) neg
    have := mul_nonneg (by omega : 0 ≤ k) ep
    omega
  have cap := (mul_le_mul_of_nonneg_left
    (by dsimp [b]; omega : b-2*k-e-2 ≤ n-2*k-e-2) wp).trans budget
  have wit : 2*(b-2*k)+k*e ≤ (k+1)*w := by dsimp [b]; omega
  dsimp [b] at cap wit
  clear width budget wp lower b n
  interval_cases k <;> norm_num at em cap wit <;> interval_cases e <;> omega

/-- For second-smallest degree sixteen through eighteen, connectivity
at least seven forces a Hamiltonian path in the original qualifying graph. -/
theorem traceable_from_sixteen (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (lo : 16 ≤ G.secondSmallestDegree) (hi : G.secondSmallestDegree ≤ 18)
    (conn : 7 ≤ G.vertexConnectivity) : ∃ a b, ∃ q : G.Walk a b, q.IsHamiltonian := by
  classical
  by_contra nontrace
  let k := G.secondSmallestDegree
  let n := Fintype.card V
  have point (v : V) : G.distEven v ≤ k+1 := by
    have h := (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
    change _ ≤ 1+k at h
    omega
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  have minz := hz.symm
  change 16 ≤ k at lo
  change k ≤ 18 at hi
  have lower : 8*(k-7+2) ≤ n+1 := by
    by_cases H : ∃ u v, ∃ p : (G.induce {v : V | v ≠ z}).Walk u v, p.IsHamiltonian
    · obtain ⟨u,v,p,hp⟩ := H
      have low := Graph189ExteriorDegreeCycle.low_of_traceable_minimum_deletion
        (by change 5 ≤ k; omega) point nontrace z minz p hp
      exact Graph189ExteriorGap.order_of_traceable_low_deletion z low point nontrace p hp
        (s:=7) (by decide) (by change 2*7 ≤ k; omega) (conn.trans (Graph189CutSides.connectivity_le_degree z))
    · have order := Graph189RotationLinked.minimum_order z minz nontrace H point
        (l:=7) (by decide) (conn.trans (completeAt_connectivity z))
        (by change 2*7+1 ≤ k; omega)
      change 8*(k-7+2)-1 ≤ n at order
      omega
  have width := Graph189ActualScalarWidth.bounds hc cap nontrace (by change 4*k+2 ≤ n; omega)
  exact no_width (by exact_mod_cast lo) (by exact_mod_cast hi)
    (by change 8*((k:ℤ)-5)-1 ≤ (n:ℤ); omega) width.1 width.2.1 width.2.2.2.1 width.2.2.2.2

theorem traceable (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (lo : 17 ≤ G.secondSmallestDegree) (hi : G.secondSmallestDegree ≤ 18)
    (conn : 7 ≤ G.vertexConnectivity) : ∃ a b, ∃ q : G.Walk a b, q.IsHamiltonian :=
  traceable_from_sixteen hc cap (by omega) hi conn

end Graph189SevenIndexTraceable
#print axioms Graph189SevenIndexTraceable.traceable

#print axioms Graph189SevenIndexTraceable.traceable_from_sixteen
