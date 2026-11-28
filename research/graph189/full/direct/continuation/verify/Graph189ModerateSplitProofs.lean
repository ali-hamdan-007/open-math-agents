import Graph189ModerateSplit
import Graph189ModerateForDesk

open SimpleGraph Finset
namespace Graph189ModerateSplitProofs

theorem short : OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1_H1_R1.H1 := by
  intro V _ _ _ G _ hc point lower uncut _upper bound
  exact OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R2.thm_D_all hc uncut point lower bound

theorem five : OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1_H1_R1.H2 := by
  intro V _ _ _ G _ hc point lower uncut upper wide degree
  have conn := Graph189ParentConnectivity.two_of_deletions hc (by omega) uncut
  exact Graph189ModerateForDesk.five hc point conn degree wide upper

private theorem maximum {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (point : ∀ x, G.distEven x ≤ 1+G.secondSmallestDegree) :
    (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree := by
  classical
  apply max'_le
  intro _ hw
  obtain ⟨w,_,rfl⟩ := mem_image.mp hw
  exact point w

theorem six : OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1_H1_R1.H3 := by
  intro V _ _ _ G _ hc point lower uncut upper _wide degree
  have conn := Graph189ParentConnectivity.two_of_deletions hc (by omega) uncut
  exact Graph189ModerateForDesk.six hc (maximum G point) uncut conn degree lower upper

theorem seven : OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1_H1_R1.H4 := by
  intro V _ _ _ G _ hc point lower uncut upper _wide degree
  have conn := Graph189ParentConnectivity.two_of_deletions hc (by omega) uncut
  exact Graph189ModerateForDesk.seven_up hc (maximum G point) conn degree upper
end Graph189ModerateSplitProofs
#print axioms Graph189ModerateSplitProofs.short
#print axioms Graph189ModerateSplitProofs.five
#print axioms Graph189ModerateSplitProofs.six
#print axioms Graph189ModerateSplitProofs.seven
