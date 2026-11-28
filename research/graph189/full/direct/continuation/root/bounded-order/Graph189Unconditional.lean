import Graph189ModerateSeven
import Graph189BothCommonSmall
import Graph189TwoConnectivityTen
import Graph189ThreeConnectedComplete

open SimpleGraph Finset
namespace Graph189FullProof

/-- The full universe-polymorphic statement, with the binder text taken from
the registered Formal Conjectures theorem at 9097e2f90e66. -/
theorem original : Graph189ParentAssembly.ExactStatement.{u} := by
  intro V _ _ _ G _ hc cap
  classical
  by_contra bad
  obtain ⟨lo,_,floor,_,minimum,two⟩ := Graph189SmallOrderWindow.necessary hc cap bad
  by_cases highConn : 3≤G.vertexConnectivity
  · exact bad (Graph189ExteriorLeaf.traceable_three_connected hc cap highConn)
  have conn : G.vertexConnectivity=2 := by omega
  by_cases ten : 10≤G.secondSmallestDegree
  · exact bad (Graph189TwoConnectivity.of_ten hc cap ten conn)
  by_cases big : 3*G.secondSmallestDegree+2<Fintype.card V
  swap
  · exact bad (Graph189ModerateSeven.original hc cap lo (by omega))
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  obtain ⟨A,B,p,q,ne,sides,conA,conB,twoA,twoB,least⟩ :=
    Graph189TwoCutSelect.exists_connected_least_cut conn (by omega) minimum lo point
  have size : ({p,q}:Finset V).card=2 := by simp [ne]
  have sc : ({p,q}:Finset V).card≤G.vertexConnectivity := by omega
  let C (H : Finset V) := ∃x∈H,∀i∈({p,q}:Finset V),G.Adj x i
  have free {H : Finset V} (absent : ¬C H) (v : V) (vh : v∈H) : ¬(G.Adj v p ∧ G.Adj v q) := by
    rintro ⟨vp,vq⟩
    apply absent
    refine ⟨v,vh,fun i hi => ?_⟩
    rcases (show i=p ∨ i=q by simpa using hi) with rfl|rfl
    · exact vp
    · exact vq
  apply bad
  by_cases a : C A
  · by_cases b : C B
    · exact Graph189SmallMixedPair.both hc cap lo minimum big sides rfl ne sc conA conB twoA twoB least a b
    by_cases adj : G.Adj p q
    · exact Graph189AdjacentPrivateCut.above_moderate hc cap sides.swap sc rfl adj lo big (free b)
    exact Graph189SmallMixedPair.nonadjacent_from_seven hc cap lo (by omega) minimum big floor sides sc rfl ne adj
      conA conB a (free b) (Or.inl least)
  by_cases b : C B
  · by_cases adj : G.Adj p q
    · exact Graph189AdjacentPrivateCut.above_moderate hc cap sides sc rfl adj lo big (free a)
    exact Graph189SmallMixedPair.nonadjacent_from_seven hc cap lo (by omega) minimum big floor sides.swap sc rfl ne adj
      conB conA b (free a) (Or.inr (least B A {p,q} sides.swap size))
  exact Graph189SmallPrivatePair.private_from_seven hc cap lo big minimum floor sides rfl ne sc (free a) (free b) conA conB

end Graph189FullProof
#print axioms Graph189FullProof.original
