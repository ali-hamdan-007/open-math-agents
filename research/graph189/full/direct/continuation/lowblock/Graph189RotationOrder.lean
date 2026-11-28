import Graph189RotationExterior
import Graph189MinimumExteriorCore
import Graph189BondyExterior
import Graph189LongestCycleMaximum

open SimpleGraph Finset Graph189UniversalCycle
namespace Graph189RotationOrder
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Either outcome of the path rotation produces the linked exterior set
required by the verified Bondy order inequality. -/
theorem order_of_core {l d : ℕ} (three : 3 ≤ l) (conn : l ≤ G.vertexConnectivity)
    (min : l ≤ G.minDegree) {a : V} (C : G.Walk a a) (hC : C.IsCycle)
    (longest : ∀ v (p : G.Walk v v), p.IsCycle → p.length ≤ C.length)
    (core : Graph189ExteriorCore.Core (G.induce {v : V | v ∉ C.support}) d)
    (enough : l+1 ≤ d) (dense : 4*l ≤ 3*d+5) :
    (l+1)*(G.minDegree-l+2)-1 ≤ Fintype.card V := by
  classical
  let L := 2*l-3
  have two : 2 ≤ L := by dsimp [L]; omega
  have density : 2*L+1 ≤ 3*d := by dsimp [L]; omega
  obtain ⟨v,q,cycle,len⟩ | ⟨E,size,links⟩ :=
    Graph189RotationExterior.cycle_or_hamilton_connected core.root two density core.degree
  · have mapped := cycle.map core.injective
    apply Graph189BondyExterior.order_of_long_exterior (k:=l) (by omega) conn min C hC longest (q.map core.hom) mapped
    · rw [Walk.length_map]
      dsimp [L] at len
      omega
    · rw [Walk.length_map]
      dsimp [L] at len
      omega
  · exact Graph189BondyExterior.order_of_hamilton_connected_exterior (by omega) conn min C hC longest
      core.hom core.injective E (enough.trans size) links

/-- A nontraceable minimum deletion provides the actual graph order at every
index allowed by its protected exterior core degree. -/
theorem minimum_order_of_parameters (w : V) (minw : G.degree w = G.minDegree)
    (notTrace : ¬ ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian)
    (notH : ¬ ∃ a b, ∃ p : (G.induce {x : V | x ≠ w}).Walk a b, p.IsHamiltonian)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    {l : ℕ} (three : 3 ≤ l) (conn : l ≤ (completeAt G w).vertexConnectivity)
    (enough : l+1 ≤ (G.secondSmallestDegree-1)/2)
    (dense : 4*l ≤ 3*((G.secondSmallestDegree-1)/2)+5) :
    (l+1)*(G.secondSmallestDegree-l+2)-1 ≤ Fintype.card V := by
  classical
  let K := completeAt G w
  have minimum := secondDegree_le_completeAt_minDegree (G:=G) w minw
  change G.secondSmallestDegree ≤ K.minDegree at minimum
  have two (v : V) : 2 ≤ K.degree v := by
    have := K.minDegree_le_degree v
    omega
  obtain ⟨z,C,hC,_⟩ := Graph189ExteriorDegreeCycle.cycle_of_degree (G:=K) w (d:=2) (by decide) two
  obtain ⟨a,P,hP,maximal⟩ := Graph189ExteriorDegreeCycle.exists_longest_cycle K ⟨z,C,hC⟩
  obtain ⟨core⟩ := Graph189ExteriorDegreeCycle.minimum_completion_exterior_core w minw P hP maximal notTrace notH cap (by omega)
  have order := order_of_core (G:=K) three conn (by omega) P hP maximal core enough dense
  have comparison := Nat.mul_le_mul_left (l+1)
    (show G.secondSmallestDegree-l+2 ≤ K.minDegree-l+2 by omega)
  omega

/-- The base lower order at a nontraceable minimum deletion follows at
every l≥3 with 3l≤k, with no external longest-cycle premise. -/
theorem minimum_order (w : V) (minw : G.degree w = G.minDegree)
    (notTrace : ¬ ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian)
    (notH : ¬ ∃ a b, ∃ p : (G.induce {x : V | x ≠ w}).Walk a b, p.IsHamiltonian)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    {l : ℕ} (three : 3 ≤ l) (conn : l ≤ (completeAt G w).vertexConnectivity)
    (enough : 3*l ≤ G.secondSmallestDegree) :
    (l+1)*(G.secondSmallestDegree-l+2)-1 ≤ Fintype.card V :=
  minimum_order_of_parameters w minw notTrace notH cap three conn (by omega) (by omega)

end Graph189RotationOrder
#print axioms Graph189RotationOrder.order_of_core
#print axioms Graph189RotationOrder.minimum_order

#print axioms Graph189RotationOrder.minimum_order_of_parameters
