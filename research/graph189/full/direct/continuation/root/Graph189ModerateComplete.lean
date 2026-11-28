import Graph189ModerateSix
import Graph189FiveOriginal

open Finset SimpleGraph
namespace Graph189ModerateComplete

/-- The exact moderate-order child of the accepted two-connected reduction.
The last clause reuses the short-order proof of @carl2sheriff. -/
theorem moderate : OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1.H1 := by
  intro V _ _ _ G _ hc point lower connected upper
  classical
  have cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree := by
    apply max'_le
    intro _ mem
    obtain ⟨v,_,rfl⟩ := mem_image.mp mem
    exact point v
  by_cases six : 6≤G.secondSmallestDegree
  · exact Graph189ModerateSix.original hc cap six upper
  by_cases five : G.secondSmallestDegree=5
  · exact Graph189FiveOriginal.traceable_five hc cap five
  exact OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R2.thm_D_all
    hc connected point lower (by omega)

end Graph189ModerateComplete
#print axioms Graph189ModerateComplete.moderate
