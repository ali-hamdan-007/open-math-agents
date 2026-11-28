import Graph189ArbitraryHalfExterior
import Graph189BondyExterior
import Graph189CriticalOrderViaCycles

open SimpleGraph
open Graph189ExteriorDegreeCycle Graph189UniversalCycle
namespace Graph189ArbitraryHalfExterior
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In the large second-degree range the genuine removable-vertex lift follows
from the accepted linked-set theorem at every order. The removable vertex
may differ from the minimum-degree vertex. -/
theorem critical_bondy_order
    (notTrace : ¬ ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (s2 : 2 ≤ G.vertexConnectivity)
    (large : 4*G.vertexConnectivity+1 ≤ G.secondSmallestDegree)
    (room : G.vertexConnectivity < Fintype.card V-1)
    (enough : G.secondSmallestDegree+2*G.vertexConnectivity+2 ≤ 2*G.minDegree) :
    (G.vertexConnectivity+2)*(G.minDegree-(G.vertexConnectivity+1)+2)-1 ≤ Fintype.card V := by
  classical
  obtain ⟨w,conn⟩ := Graph189CriticalConnectivity.exists_completion (G:=G) room (by omega)
  let K := completeAt G w
  have minK : G.minDegree ≤ K.minDegree := minDegree_le_completeAt w
  have two (v : V) : 2 ≤ K.degree v := by
    have := K.minDegree_le_degree v
    omega
  obtain ⟨b,R,hR,_⟩ := cycle_of_degree (G:=K) w (d:=2) (by decide) two
  obtain ⟨a,C,hC,longest⟩ := exists_longest_cycle K ⟨b,R,hR⟩
  obtain ⟨core⟩ := completion_core w C hC longest notTrace (by omega) (by omega) cap
  obtain ⟨v,Q,hQ,len⟩ := cycle_of_degree (G:=core.graph) (d:=(G.secondSmallestDegree-3)/2)
    core.root (by omega) core.degree
  let q := Q.map core.hom
  have hq := hQ.map core.injective
  have size : (G.secondSmallestDegree-3)/2+1 ≤ q.length :=
    len.trans_eq (Walk.length_map core.hom Q).symm
  have ord := Graph189BondyExterior.order_of_long_exterior (G:=K) (k:=G.vertexConnectivity+1)
    (by omega) conn (by omega) C hC longest q hq (by omega) (by omega)
  have step : G.minDegree-(G.vertexConnectivity+1)+2 ≤ K.minDegree-(G.vertexConnectivity+1)+2 := by omega
  have cmp := Nat.mul_le_mul_left (G.vertexConnectivity+2) step
  change (G.vertexConnectivity+2)*(K.minDegree-(G.vertexConnectivity+1)+2)-1 ≤ Fintype.card V at ord
  omega

#print axioms critical_bondy_order
end Graph189ArbitraryHalfExterior
