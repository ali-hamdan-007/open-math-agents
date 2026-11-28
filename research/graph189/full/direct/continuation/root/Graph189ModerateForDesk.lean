import Graph189ModerateSix
import Graph189FiveHighMinimum

open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189ModerateForDesk
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- For k=5 the part outside the short-order theorem consists of order 17
alone. A degree-two vertex forces order at most sixteen. -/
theorem five (hc : G.Connected) (point : ∀v,G.distEven v≤1+G.secondSmallestDegree)
    (conn : 2≤G.vertexConnectivity) (k5 : G.secondSmallestDegree=5)
    (lower : 2*G.secondSmallestDegree+6<Fintype.card V)
    (upper : Fintype.card V≤3*G.secondSmallestDegree+2) :
    ∃a b,∃r : G.Walk a b,r.IsHamiltonian := by
  classical
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  have fd := Graph189CutSides.connectivity_le_degree (G:=G) z
  have localCap (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by simpa only [Nat.add_comm] using point v
  have three : 3≤G.degree z := by
    by_contra! low
    have bd := Graph189LayerCutoff.order_of_small_degree G hc z _ localCap (by omega)
    rw [k5,show G.degree z=2 by omega] at bd
    omega
  have quota (v : V) : (univ.filter (fun w => G.dist v w=2)).card≤5 := by
    let T := univ.filter (fun w => G.dist v w=2)
    have no : v∉T := by simp [T]
    have sub : insert v T⊆univ.filter (fun w => Even (G.dist v w)) := by
      intro w hw
      rcases mem_insert.mp hw with rfl|h
      · simp
      · exact mem_filter.mpr ⟨mem_univ _,by rw [(mem_filter.mp h).2]; decide⟩
    have count := card_le_card sub
    rw [card_insert_of_notMem no] at count
    change T.card+1≤G.distEven v at count
    change T.card≤5
    have := point v
    omega
  have cuts (U : Finset V) (h : U.card<2) := Graph189CutSides.connected_after_smaller_deletion (G:=G) U (h.trans_le conn)
  by_cases low : G.degree z<5
  · exact Graph189FiveHighMinimum.low_traceable cuts z three (fun x ne => by
      have := degree_pair (G:=G) x z ne
      omega) quota (by omega)
  have min (v : V) : 5≤G.degree v := by have := G.minDegree_le_degree v; omega
  obtain ⟨a,b,p,hp,mx⟩ := Graph189ThreeRegularMinimum.longest_path (G:=G) z
  refine ⟨a,b,p,hp.isHamiltonian_of_mem (fun x => ?_)⟩
  by_contra miss
  have size := Graph189FiveTiedExterior.four_omissions p hp mx cuts min quota (by omega) miss
  exact Graph189OrdinaryTwoMarks.exclude p hp mx (m:=4) (by decide) min quota (by omega) size

theorem six (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (uncut : ∀z : V,(G.induce {v : V | v≠z}).Connected) (conn : 2≤G.vertexConnectivity)
    (k6 : G.secondSmallestDegree=6) (lower : 2*G.secondSmallestDegree+3≤Fintype.card V)
    (upper : Fintype.card V≤3*G.secondSmallestDegree+2) :
    ∃a b,∃r : G.Walk a b,r.IsHamiltonian := by
  classical
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  have fd := Graph189CutSides.connectivity_le_degree (G:=G) z
  by_cases low : G.degree z=2
  · have bd := Graph189LayerCutoff.order_of_small_degree G hc z _ point (by omega)
    rw [low,k6] at bd
    exact Graph189SixOrder.of_deletions hc cap k6 (by omega) lower uncut
  exact Graph189SixMinimumThree.traceable conn k6 (by omega) (by omega) point

theorem seven_up (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (conn : 2≤G.vertexConnectivity) (large : 7≤G.secondSmallestDegree)
    (upper : Fintype.card V≤3*G.secondSmallestDegree+2) :
    ∃a b,∃r : G.Walk a b,r.IsHamiltonian := by
  by_cases eight : 8≤G.secondSmallestDegree
  · exact Graph189ModerateEight.traceable_moderate hc cap eight conn upper
  exact Graph189ModerateSeven.seven_two_connected hc cap conn (by omega) (by omega)

/-- Exact moderate statement, specialized throughout to the hypotheses supplied
by the merged parent. The four alternatives have no unproved graph premises. -/
theorem moderate : OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1.H1 := by
  intro V _ _ _ G _ hc point lower uncut upper
  classical
  by_cases short : Fintype.card V≤2*G.secondSmallestDegree+6
  · exact OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R2.thm_D_all hc uncut point lower short
  have cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree := by
    apply max'_le
    intro _ hw
    obtain ⟨w,_,rfl⟩ := mem_image.mp hw
    exact point w
  have conn := Graph189ParentConnectivity.two_of_deletions hc (by omega) uncut
  by_cases k5 : G.secondSmallestDegree=5
  · exact five hc point conn k5 (by omega) upper
  by_cases k6 : G.secondSmallestDegree=6
  · exact six hc cap uncut conn k6 lower upper
  exact seven_up hc cap conn (by omega) upper

end Graph189ModerateForDesk
#print axioms Graph189ModerateForDesk.moderate
