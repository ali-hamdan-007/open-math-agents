import Graph189AtomNonneighbor
import Graph189RepairedConeOrder
import Graph189RotationMinOrder
import Graph189ParentConnectivity
import Graph189ParentFocused

open Finset SimpleGraph Graph189UniversalCycle Graph189ExteriorDegreeCycle Graph189CutSides
namespace Graph189ModerateEight
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At every connectivity at least two and second degree at least seven,
a counterexample requires at least four times the second degree minus five
vertices. The statement allows the low vertex in a minimum separator. -/
theorem traceable_below_four (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 7≤G.secondSmallestDegree) (conn : 2≤G.vertexConnectivity)
    (order : Fintype.card V+5<4*G.secondSmallestDegree) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let k := G.secondSmallestDegree
  let n := Fintype.card V
  let s := G.vertexConnectivity
  change 7≤k at large
  change 2≤s at conn
  change n+5<4*k at order
  have upper (v : V) : G.distEven v≤1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by simpa only [Nat.add_comm] using upper v
  by_contra nontrace
  by_cases three : 3≤s
  · have bound := Graph189RotationLinked.base_order nontrace point (l:=3) (by decide)
      three (by change 2*3+1≤k; omega)
    change 4*(k-3+2)≤n+1 at bound
    omega
  have two : s=2 := by omega
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  have minimum := hz.symm
  have sd := connectivity_le_degree (G:=G) z
  change s≤G.degree z at sd
  by_cases lowTwo : G.degree z=2
  · exact nontrace (Graph189DegreeTwoOriginal.traceable hc cap conn z lowTwo large)
  have zthree : 3≤G.degree z := by omega
  by_cases H : ∃ a b, ∃ p : (G.induce {x : V | x≠z}).Walk a b, p.IsHamiltonian
  · obtain ⟨a,b,p,hp⟩ := H
    have low := low_of_traceable_minimum_deletion (by change 5≤k; omega) point nontrace z minimum p hp
    have bound := Graph189ExteriorGap.order_of_traceable_low_deletion z low point nontrace p hp
      (s:=3) (by decide) (by change 2*3≤k; omega) zthree
    change 4*(k-3+2)≤n+1 at bound
    omega
  have max := (secondDegree_le_completeAt_minDegree (G:=G) z minimum).trans ((completeAt G z).minDegree_le_degree z)
  rw [completeAt_degree_self] at max
  change k≤n-1 at max
  have room : G.vertexConnectivity<Fintype.card V-1 := by change s<n-1; omega
  by_cases free : ∀ T : Finset V, T.card=G.vertexConnectivity → z∈T →
      (G.induce {v : V | v∉T}).Connected
  · have connK := completeAt_connectivity_add_one z room free
    have bound := Graph189RotationLinked.minimum_order z minimum nontrace H point (l:=3)
      (by decide) (by change s+1≤_ at connK; omega) (by change 2*3+1≤k; omega)
    change 4*(k-3+2)-1≤n at bound
    omega
  push Not at free
  obtain ⟨T,size,zin,bad⟩ := free
  have survive : ∃ t, t∉T := by
    by_contra! all
    have eq := eq_univ_iff_forall.mpr all
    rw [eq,card_univ] at size
    change n=s at size
    omega
  obtain ⟨A,B,cut⟩ := exists_cutSides_of_disconnected T survive bad
  have sep := cut.anchor_degree (fun L h => connected_after_smaller_deletion L (h.trans_eq size)) upper zin
  change k+1≤G.degree z+T.card at sep
  change T.card=s at size
  have near : k≤G.minDegree+1 := by omega
  have complete : ∃ w : V, 3≤(completeAt G w).vertexConnectivity ∧ k≤(completeAt G w).minDegree := by
    by_cases tie : k≤G.minDegree
    · obtain ⟨w,gain⟩ := Graph189CriticalConnectivity.exists_completion (G:=G) room
        (by change 3*s<2*(G.minDegree+1); omega)
      change s+1≤_ at gain
      exact ⟨w,by omega,tie.trans (minDegree_le_completeAt w)⟩
    have eq : G.degree z+1=k := by omega
    obtain ⟨w,wz,miss,gain⟩ := Graph189AtomNonneighbor.free_nonneighbor z cut size zin room
      (by change 3*s<2*(G.minDegree+1); omega) (by change G.degree z<k; omega)
      (by change G.degree z+s≤k+1; omega)
    change s+1≤_ at gain
    exact ⟨w,by omega,Graph189AtomNonneighbor.repaired_minDegree z w wz miss eq⟩
  obtain ⟨w,gain,minK⟩ := complete
  have bound := Graph189RepairedConeOrder.order_three w large nontrace point
    (by change k<2*G.minDegree; omega) gain minK
  change 4*(k-3+2)-1≤n at bound
  omega

/-- The whole two-connected moderate parent range is traceable for every
second-smallest degree at least eight. -/
theorem traceable_moderate (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 8≤G.secondSmallestDegree) (conn : 2≤G.vertexConnectivity)
    (order : Fintype.card V≤3*G.secondSmallestDegree+2) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian :=
  traceable_below_four hc cap (by omega) conn (by omega)

/-- The original conjecture on the entire order window below four times
the second degree minus five, including graphs with a cut vertex. -/
theorem original_below_four (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 7≤G.secondSmallestDegree) (order : Fintype.card V+5<4*G.secondSmallestDegree) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have point (v : V) : G.distEven v≤1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  by_cases short : Fintype.card V≤2*G.secondSmallestDegree+2
  · exact OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.theorem_C hc point short
  by_cases del : ∀ z : V, (G.induce {v | v≠z}).Connected
  · exact traceable_below_four hc cap large (Graph189ParentConnectivity.two_of_deletions hc (by omega) del) order
  push Not at del
  exact Graph189CutH1.cut_vertex_case G hc point (by omega) del

/-- The registered conjecture holds at every moderate order and
second-smallest degree at least eight, with no connectivity-index hypothesis. -/
theorem original_moderate (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 8≤G.secondSmallestDegree) (order : Fintype.card V≤3*G.secondSmallestDegree+2) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian :=
  original_below_four hc cap (by omega) (by omega)

end Graph189ModerateEight
#print axioms Graph189ModerateEight.traceable_below_four
#print axioms Graph189ModerateEight.traceable_moderate
#print axioms Graph189ModerateEight.original_below_four
#print axioms Graph189ModerateEight.original_moderate
