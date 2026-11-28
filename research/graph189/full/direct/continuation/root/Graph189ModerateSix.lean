import Graph189ModerateSeven
import Graph189SixOrder
import Graph189SixRotation
import Graph189SixProtected
import Graph189HighMinimumGap

open SimpleGraph Finset
namespace Graph189ModerateSix
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The full original conjecture at all moderate orders and second-smallest
degree at least six. -/
theorem original (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 6≤G.secondSmallestDegree) (order : Fintype.card V≤3*G.secondSmallestDegree+2) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  by_cases seven : 7≤G.secondSmallestDegree
  · exact Graph189ModerateSeven.original hc cap seven order
  have six : G.secondSmallestDegree=6 := by omega
  have small : Fintype.card V≤20 := by omega
  have point (v : V) : G.distEven v≤1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have localCap (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using point v
  by_cases short : Fintype.card V≤2*G.secondSmallestDegree+2
  · exact OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.theorem_C hc point short
  by_cases survives : ∀ z : V, (G.induce {v | v≠z}).Connected
  · have conn := Graph189ParentConnectivity.two_of_deletions hc (by omega) survives
    obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
    have lower := Graph189CutSides.connectivity_le_degree (G:=G) z
    by_cases dz : G.degree z=2
    · exact Graph189SixOrder.traceable_degree_two hc cap six z dz
    have min (v : V) : 3≤G.degree v := by have := G.minDegree_le_degree v; omega
    obtain ⟨a,b,p,hp,mx⟩ := Graph189ThreeRegularMinimum.longest_path (G:=G) z
    let E := p.support.toFinsetᶜ
    have low (v : V) (hv : v∈E) : G.degree v<6 :=
      Graph189SixRotation.omitted_low p hp mx conn small six (by omega) localCap (by simpa [E] using hv)
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
    have high (x : V) (ne : x≠w) : G.secondSmallestDegree≤G.degree x :=
      (OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) x w ne).resolve_right
        (not_le.mpr lw)
    exact nontrace (Graph189SixProtected.traceable w (min w) six high localCap (by omega) r hr)
  push Not at survives
  exact Graph189CutH1.cut_vertex_case G hc point (by omega) survives

end Graph189ModerateSix
#print axioms Graph189ModerateSix.original
