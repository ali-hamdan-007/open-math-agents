import Graph199OrderedConnector

open Finset

namespace Graph199

/-- Choose the larger of keeping a center with its private leaves, and
replacing it with leaves from its overlap with the neighboring center. -/
def endpointKeeps {C : Type*} [DecidableEq C] (R N : Finset C) : Bool :=
  decide ((R ∩ N).card ≤ (R \ N).card + 1)

/-- The leaves chosen at one endpoint. -/
def endpointPool {C : Type*} [DecidableEq C] (R N : Finset C) : Finset C :=
  if endpointKeeps R N then R \ N else R ∩ N

/-- The number of vertices lost from the core when making the choice. -/
def endpointDrop {C : Type*} [DecidableEq C] (R N : Finset C) : ℕ :=
  if endpointKeeps R N then 0 else 1

theorem endpoint_pool_subset {C : Type*} [DecidableEq C] (R N : Finset C) :
    endpointPool R N ⊆ R := by
  unfold endpointPool
  split
  · exact sdiff_subset
  · exact inter_subset_left

/-- The endpoint choice retains at least half the endpoint row and center,
with a rounding gain when that total is odd. -/
theorem endpoint_pool_gain {C : Type*} [DecidableEq C] (R N : Finset C) :
    R.card + 1 + 2 * endpointDrop R N ≤ 2 * (endpointPool R N).card + 2 := by
  have h := card_sdiff_add_card_inter R N
  simp only [endpointPool,endpointDrop,endpointKeeps,decide_eq_true_eq]
  split <;> omega

#print axioms endpoint_pool_gain

end Graph199
