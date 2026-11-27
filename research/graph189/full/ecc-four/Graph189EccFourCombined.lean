import Graph189EccFourOrder

namespace Graph189EccFour
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At a degree-two root of eccentricity at most four, the sharp order bound
holds for second-smallest degree at least four. -/
theorem order_le_three_sigma_sub_one_of_ecc_le_four (z : V) (h : G.Connected)
    (hz : G.degree z = 2) (hecc : ∀ x, G.dist z x ≤ 4)
    (hs : 4 ≤ G.secondSmallestDegree)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree) :
    Fintype.card V ≤ 3*G.secondSmallestDegree-1 := by
  by_cases hfar : ∃ f, G.dist z f = 4
  · exact order_le_three_sigma_sub_one z h hz hecc hfar hs hσ
  · apply Graph189DegreeTwoRooted.order_le_three_sigma_sub_one z h _ hσ hs hz
    intro x
    have hne : G.dist z x ≠ 4 := fun he => hfar ⟨x,he⟩
    have hle := hecc x
    omega

#print axioms order_le_three_sigma_sub_one_of_ecc_le_four
end Graph189EccFour
