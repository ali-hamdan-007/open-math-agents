import Graph189LinkedDegreeSum
import Graph189ArbitraryHalfExterior
import Graph189RotationMinOrder
import Graph189CriticalConnectivity

open Finset SimpleGraph Graph189ExteriorDegreeCycle Graph189UniversalCycle
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189WeightedCriticalOrder
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem sum_at_completion (w : V) (T : Finset V) {l : ℕ} (size : T.card=l+1) :
    l*G.secondSmallestDegree+G.minDegree≤∑ v∈T,(completeAt G w).degree v := by
  classical
  obtain ⟨z,least⟩ := G.exists_minimal_degree_vertex
  have high (v : V) (ne : v≠z) : G.secondSmallestDegree≤(completeAt G w).degree v := by
    apply le_trans _ (degree_le_completeAt w v)
    rcases degree_pair (G:=G) v z ne with h|h
    · exact h
    · exact h.trans (least ▸ G.minDegree_le_degree v)
  obtain ⟨a,ha,others⟩ : ∃a∈T,∀v∈T,v≠a → v≠z := by
    by_cases yes : z∈T
    · exact ⟨z,yes,fun _ _ h => h⟩
    obtain ⟨a,ha⟩ := card_pos.mp (by omega : 0<T.card)
    exact ⟨a,ha,fun v hv eq e => yes (e ▸ hv)⟩
  have bd := sum_le_sum (s:=T.erase a) (fun v hv => high v (others v (mem_erase.mp hv).2 (mem_erase.mp hv).1))
  have er := card_erase_add_one ha
  have count : (T.erase a).card=l := by omega
  simp only [sum_const,count,smul_eq_mul] at bd
  have base := (G.minDegree_le_degree a).trans (degree_le_completeAt w a)
  have split := sum_erase_add T (fun v => (completeAt G w).degree v) ha
  omega

/-- In the lifted linked-set order bound the unique low degree can be charged
only once among the distinct successors and, when needed, the exterior witness. -/
theorem order (bad : ¬ ∃ a b, ∃ p : G.Walk a b,p.IsHamiltonian)
    (cap : ∀v,G.distEven v≤G.secondSmallestDegree+1) (two : 2≤G.vertexConnectivity)
    (wide : 2*G.vertexConnectivity+5≤G.secondSmallestDegree)
    (room : G.vertexConnectivity<Fintype.card V-1)
    (critical : 3*G.vertexConnectivity<2*(G.minDegree+1))
    (minimum : G.secondSmallestDegree+6≤2*G.minDegree) :
    (G.vertexConnectivity+1)*G.secondSmallestDegree+G.minDegree <
      Fintype.card V+(G.vertexConnectivity+1)*G.vertexConnectivity := by
  classical
  by_contra! short
  obtain ⟨w,conn⟩ := Graph189CriticalConnectivity.exists_completion (G:=G) room critical
  let K := completeAt G w
  have mk : G.minDegree≤K.minDegree := minDegree_le_completeAt w
  have twoK (v : V) : 2≤K.degree v := by have := K.minDegree_le_degree v; omega
  obtain ⟨b,R,hR,_⟩ := cycle_of_degree (G:=K) w (d:=2) (by decide) twoK
  obtain ⟨a,C,hC,longest⟩ := exists_longest_cycle K ⟨b,R,hR⟩
  obtain ⟨core⟩ := Graph189ArbitraryHalfExterior.completion_core w C hC longest bad (by omega) (by omega) cap
  let l := G.vertexConnectivity+1
  have enough : l≤(G.secondSmallestDegree-3)/2 := by dsimp [l]; omega
  have linked := Graph189RotationLinked.of_minimum (G:=core.graph) core.root
    (by dsimp [l]; omega : 3≤l) (fun x => enough.trans (core.degree x))
  obtain ⟨H,D,cy,comp,sep,sub,count,paths⟩ := OMA.BondyK.graph189_linked_witness
    (fun S h => Graph189CutSides.connected_after_smaller_deletion (G:=K) S (h.trans_le conn))
    C hC longest (Graph189LinkedExterior.map core.hom core.injective linked)
  apply Graph189LinkedDegreeSum.linked_contra_sum cy comp (by dsimp [l]; omega : 1≤l) _ sep sub count paths
  intro T size
  have sum := sum_at_completion (G:=G) w T size
  apply le_trans _ sum
  simpa [l] using short

#print axioms order
end Graph189WeightedCriticalOrder
