import Graph189RotationLinked
import Graph189MinimumExteriorCore
import Graph189LongestCycleMaximum
import Graph189BondyOrder
import Graph189MinimumCutOrder

open SimpleGraph Finset Graph189UniversalCycle
namespace Graph189RotationLinked
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The true order inequality follows as soon as the exterior of a longest
cycle contains an embedded graph of minimum degree at least the index. -/
theorem order_of_core {l d : ℕ} (three : 3≤l) (conn : l≤G.vertexConnectivity) (min : l≤G.minDegree)
    {a : V} (C : G.Walk a a) (hC : C.IsCycle)
    (longest : ∀ b (q : G.Walk b b), q.IsCycle → q.length≤C.length)
    (core : Graph189ExteriorCore.Core (G.induce {v : V | v∉C.support}) d) (enough : l≤d) :
    (l+1)*(G.minDegree-l+2)-1≤Fintype.card V := by
  classical
  have linked := of_minimum (G:=core.graph) core.root three (fun w => enough.trans (core.degree w))
  exact OMA.BondyK.graph189_order_of_linked (by omega) min (fun S h =>
    Graph189CutSides.connected_after_smaller_deletion S (h.trans_le conn)) C hC longest
    (Graph189LinkedExterior.map core.hom core.injective linked)

/-- A nontraceable minimum-degree deletion forces the order bound throughout
the complete range of indices covered by its genuine exterior minimum degree. -/
theorem minimum_order (w : V) (minw : G.degree w=G.minDegree)
    (notTrace : ¬∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian)
    (notH : ¬∃ a b, ∃ p : (G.induce {x : V | x≠w}).Walk a b, p.IsHamiltonian)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    {l : ℕ} (three : 3≤l) (conn : l≤(completeAt G w).vertexConnectivity)
    (enough : 2*l+1≤G.secondSmallestDegree) :
    (l+1)*(G.secondSmallestDegree-l+2)-1≤Fintype.card V := by
  classical
  let K := completeAt G w
  have mindeg := secondDegree_le_completeAt_minDegree (G:=G) w minw
  change G.secondSmallestDegree≤K.minDegree at mindeg
  have two (v : V) : 2≤K.degree v := by have := K.minDegree_le_degree v; omega
  obtain ⟨a,R,hR,_⟩ := Graph189ExteriorDegreeCycle.cycle_of_degree (G:=K) w (d:=2) (by decide) two
  obtain ⟨a,C,hC,mx⟩ := Graph189ExteriorDegreeCycle.exists_longest_cycle K ⟨a,R,hR⟩
  obtain ⟨core⟩ := Graph189ExteriorDegreeCycle.minimum_completion_exterior_core w minw C hC mx notTrace notH cap (by omega)
  have lower := order_of_core (G:=K) three conn (by omega) C hC mx core (by omega)
  have cmp := Nat.mul_le_mul_left (l+1) (show G.secondSmallestDegree-l+2≤K.minDegree-l+2 by omega)
  omega

end Graph189RotationLinked
#print axioms Graph189RotationLinked.order_of_core
#print axioms Graph189RotationLinked.minimum_order
