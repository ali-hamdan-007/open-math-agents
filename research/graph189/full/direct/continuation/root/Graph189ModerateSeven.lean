import Graph189ModerateEight
import Graph189SevenRotation
import Graph189SevenProtected
import Graph189HighMinimumGap

open SimpleGraph Finset
namespace Graph189ModerateSeven
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The exceptional endpoint at degree seven with the exact connected-deletion
hypothesis already available as a connectivity bound. -/
theorem seven_two_connected (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (conn : 2≤G.vertexConnectivity) (seven : G.secondSmallestDegree=7) (small : Fintype.card V≤23) :
    ∃ a b, ∃ p : G.Walk a b,p.IsHamiltonian := by
  classical
  have large : 7≤G.secondSmallestDegree := seven.ge
  have point (v : V) : G.distEven v≤1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have localCap (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using point v
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  have lower := Graph189CutSides.connectivity_le_degree (G:=G) z
  by_cases dz : G.degree z=2
  · exact Graph189DegreeTwoOriginal.traceable hc cap conn z dz large
  have min (v : V) : 3≤G.degree v := by have := G.minDegree_le_degree v; omega
  have quota (v : V) : (univ.filter (fun w => G.dist v w=2)).card≤7 := by
    let D := univ.filter (fun w => G.dist v w=2)
    have sub : insert v D⊆univ.filter (fun w => Even (G.dist v w)) := by
      intro w hw
      rcases mem_insert.mp hw with rfl|h
      · simp
      · exact mem_filter.mpr ⟨mem_univ _,by simp [(mem_filter.mp h).2]⟩
    have no : v∉D := by simp [D]
    have bd := card_le_card sub
    rw [card_insert_of_notMem no] at bd
    change D.card+1≤G.distEven v at bd
    have lim := point v
    change D.card≤7
    omega
  obtain ⟨a,b,p,hp,mx⟩ := Graph189ThreeRegularMinimum.longest_path (G:=G) z
  let E := p.support.toFinsetᶜ
  have low (v : V) (hv : v∈E) : G.degree v<7 := by
    by_contra! high
    exact Graph189SevenRotation.no_high p hp mx conn small seven min quota (by simpa [E] using hv) high
  have few : E.card≤1 := by
    apply card_le_one.mpr
    intro u hu v hv
    by_contra ne
    have pair := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) u v ne
    have l1 := low u hu
    have l2 := low v hv
    omega
  have pop := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at pop
  change p.support.length+E.card=Fintype.card V at pop
  by_contra nontrace
  obtain ⟨w,lw,_,_,r,hr⟩ := Graph189ExteriorDegreeCycle.near_longest_has_hamiltonian_low_deletion
    p hp mx (by omega) nontrace (by omega) localCap min
  exact nontrace (Graph189SevenProtected.traceable w lw (min w) seven small localCap r hr)

/-- The full original conjecture at all moderate orders and second-smallest
degree at least seven. -/
theorem original (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 7≤G.secondSmallestDegree) (order : Fintype.card V≤3*G.secondSmallestDegree+2) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  by_cases eight : 8≤G.secondSmallestDegree
  · exact Graph189ModerateEight.original_moderate hc cap eight order
  have seven : G.secondSmallestDegree=7 := by omega
  have small : Fintype.card V≤23 := by omega
  have point (v : V) : G.distEven v≤1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  by_cases short : Fintype.card V≤2*G.secondSmallestDegree+2
  · exact OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.theorem_C hc point short
  by_cases survives : ∀ z : V, (G.induce {v | v≠z}).Connected
  · have conn := Graph189ParentConnectivity.two_of_deletions hc (by omega) survives
    exact seven_two_connected hc cap conn seven small
  push Not at survives
  exact Graph189CutH1.cut_vertex_case G hc point (by omega) survives

end Graph189ModerateSeven
#print axioms Graph189ModerateSeven.original
