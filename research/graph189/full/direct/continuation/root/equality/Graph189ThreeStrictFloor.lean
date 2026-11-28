import Graph189LinkedEqualityTrace
import Graph189UnrestrictedMinimumDeletion
import Graph189WeightedCriticalOrder
import Graph189StrictCutDeficit

open SimpleGraph Finset Graph189UniversalCycle Graph189ExteriorDegreeCycle
open OMA.BondyK OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189ThreeStrictFloor
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Opening the equality cycle excludes the bottom order in the three-cut
sector. If a low vertex exists then no minimum cut can contain it at this order. -/
theorem strict (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (bad : ¬∃a b,∃p : G.Walk a b,p.IsHamiltonian)
    (three : G.vertexConnectivity=3) (large : 15≤G.secondSmallestDegree)
    (old : 5*G.secondSmallestDegree≤Fintype.card V+11) : 5*G.secondSmallestDegree≤Fintype.card V+10 := by
  classical
  by_contra! boundary
  let k := G.secondSmallestDegree
  let n := Fintype.card V
  change 15≤k at large
  change 5*k≤n+11 at old
  change n+10<5*k at boundary
  have point (v : V) : G.distEven v≤1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have cp (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by simpa only [Nat.add_comm 1] using point v
  have room : G.vertexConnectivity<n-1 := by omega
  have eq : n=(4+1)*(k-4+2)-1 := by omega
  have finish (w : V) (high : ∀v,v≠w → k≤G.degree v) (min : k≤(completeAt G w).minDegree)
      (conn : 4≤(completeAt G w).vertexConnectivity)
      (link : ∀a,∀C : (completeAt G w).Walk a a,C.IsCycle →
        (∀b,∀Q : (completeAt G w).Walk b b,Q.IsCycle → Q.length≤C.length) →
          Graph189LinkedExterior.Linked ((completeAt G w).induce (offWalk C)) 4) : False := by
    let K := completeAt G w
    have deg (a : V) : 2≤K.degree a := by have h := min.trans (K.minDegree_le_degree a); omega
    obtain ⟨a,R,hR,_⟩ := cycle_of_degree (G:=K) w (d:=2) (by decide) deg
    obtain ⟨a,C,hC,longest⟩ := exists_longest_cycle K ⟨a,R,hR⟩
    exact bad (Graph189BondyEquality.traceable_of_linked_equality w (by decide : 2≤4) (by omega) high min conn eq
      C hC longest (link a C hC longest))
  obtain ⟨z,least⟩ := G.exists_minimal_degree_vertex
  by_cases tied : k≤G.minDegree
  · obtain ⟨w,conn⟩ := Graph189CriticalConnectivity.exists_completion (G:=G) room (by omega)
    apply finish w (fun v _ => tied.trans (G.minDegree_le_degree v)) (tied.trans (minDegree_le_completeAt w)) (by omega)
    intro a C hC longest
    obtain ⟨core⟩ := Graph189ArbitraryHalfExterior.completion_core w C hC longest bad
      (by change 8≤k; omega) (by change k+6≤2*G.minDegree; omega) cp
    have linked := Graph189RotationLinked.of_minimum (G:=core.graph) core.root (by decide : 3≤4)
      (fun v => (show 4≤(G.secondSmallestDegree-3)/2 by change 4≤(k-3)/2; omega).trans (core.degree v))
    exact Graph189LinkedExterior.map core.hom core.injective linked
  have free : ∀T : Finset V,T.card=G.vertexConnectivity → z∈T → (G.induce {v : V | v∉T}).Connected := by
    intro T sz zin
    by_contra cut
    have live : ∃v,v∉T := by
      by_contra! full
      rw [eq_univ_iff_forall.mpr full,card_univ] at sz
      change n=G.vertexConnectivity at sz
      omega
    obtain ⟨A,B,sides⟩ := Graph189CutSides.exists_cutSides_of_disconnected T live cut
    obtain ⟨r,rs,_,debit⟩ := sides.strict_low_cut hc
      (fun U lt => Graph189CutSides.connected_after_smaller_deletion U (lt.trans_eq sz)) point zin
      (by change G.degree z<k; omega)
    change n+k*(k-G.degree z)<2*k+(k+1)*r at debit
    have hi := Nat.mul_le_mul_left (k+1) (by omega : r≤3)
    have lo := Nat.mul_le_mul_left k (show 1≤k-G.degree z by omega)
    omega
  apply finish z (fun v ne => (degree_pair (G:=G) v z ne).resolve_right (by change ¬k≤G.degree z; omega))
    (secondDegree_le_completeAt_minDegree z least.symm) (by have h := completeAt_connectivity_add_one z room free; omega)
  intro a C hC longest
  have degree := Graph189CutSides.connectivity_le_degree (G:=G) z
  have del : ¬∃a b,∃p : (G.induce {v : V | v≠z}).Walk a b,p.IsHamiltonian := by
    rintro ⟨a,b,p,hp⟩
    exact bad (Graph189RootedSplice.traceable_of_hamiltonian_minimum_deletion_unrestricted hc z least.symm
      (by omega) (by change 5≤k; omega) cp p hp)
  obtain ⟨core⟩ := minimum_completion_exterior_core z least.symm C hC longest bad del cp (by change 5≤k; omega)
  have linked := Graph189RotationLinked.of_minimum (G:=core.graph) core.root (by decide : 3≤4)
    (fun v => (by omega : 4≤(k-1)/2).trans (core.degree v))
  exact Graph189LinkedExterior.map core.hom core.injective linked

end Graph189ThreeStrictFloor
#print axioms Graph189ThreeStrictFloor.strict
