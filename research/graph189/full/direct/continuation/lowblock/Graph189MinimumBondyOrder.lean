import Graph189BondyExterior
import Graph189MinimumOrderViaCycles

open SimpleGraph Graph189UniversalCycle
namespace Graph189ExteriorDegreeCycle
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The half-length exterior in a minimum-vertex completion meets the
verified Bondy bound for every connectivity level l with 4l−5 ≤ k. -/
theorem minimum_bondy_order (w : V) (minw : G.degree w=G.minDegree)
    (notTrace : ¬ ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian)
    (notH : ¬ ∃ a b, ∃ p : (G.induce {x : V | x ≠ w}).Walk a b, p.IsHamiltonian)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    {l : ℕ} (three : 3 ≤ l) (conn : l ≤ (completeAt G w).vertexConnectivity)
    (enough : 4*l ≤ G.secondSmallestDegree+5) :
    (l+1)*(G.secondSmallestDegree-l+2)-1 ≤ Fintype.card V := by
  classical
  let K := completeAt G w
  have minimum := secondDegree_le_completeAt_minDegree (G:=G) w minw
  change G.secondSmallestDegree ≤ K.minDegree at minimum
  have two (v : V) : 2 ≤ K.degree v := by
    have := K.minDegree_le_degree v
    omega
  obtain ⟨z,C,hC,_⟩ := cycle_of_degree (G:=K) w (d:=2) (by decide) two
  obtain ⟨a,P,hP,maximal⟩ := exists_longest_cycle K ⟨z,C,hC⟩
  obtain ⟨b,Q,hQ,sz⟩ := minimum_completion_half_cycle w minw P hP maximal notTrace notH cap (by omega)
  have order := Graph189BondyExterior.order_of_long_exterior (G:=K) (k:=l) (by omega) conn
    (by omega) P hP maximal Q hQ (by omega) (by omega)
  have comparison := Nat.mul_le_mul_left (l+1)
    (show G.secondSmallestDegree-l+2 ≤ K.minDegree-l+2 by omega)
  omega

/-- If the minimum deletion is nontraceable, the genuine graph satisfies
the base order whenever 4s−5 ≤ k. -/
theorem base_order_of_minimum_deletion (w : V) (minw : G.degree w=G.minDegree)
    (notTrace : ¬ ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian)
    (notH : ¬ ∃ a b, ∃ p : (G.induce {x : V | x ≠ w}).Walk a b, p.IsHamiltonian)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (three : 3 ≤ G.vertexConnectivity) (enough : 4*G.vertexConnectivity ≤ G.secondSmallestDegree+5) :
    (G.vertexConnectivity+1)*(G.secondSmallestDegree-G.vertexConnectivity+2)-1 ≤ Fintype.card V :=
  minimum_bondy_order w minw notTrace notH cap three (completeAt_connectivity w) enough

end Graph189ExteriorDegreeCycle
#print axioms Graph189ExteriorDegreeCycle.minimum_bondy_order
#print axioms Graph189ExteriorDegreeCycle.base_order_of_minimum_deletion
