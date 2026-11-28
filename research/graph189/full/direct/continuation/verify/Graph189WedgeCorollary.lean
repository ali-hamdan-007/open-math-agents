import Graph189WedgeOrder

namespace Graph189WedgeOrder
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Above the local degree-excess threshold, this wedge satisfies the local Ore condition. -/
theorem local_ore_of_order (hc : G.Connected) {x y z : V}
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : ¬G.Adj y z)
    {k r : ℕ} (cap : ∀ v, G.distEven v ≤ k+1)
    (hdeg : G.degree x + G.distEven x ≤ G.degree y + G.degree z + r + 1)
    (hn : (3+r)*k+1 < Fintype.card V) :
    (G.neighborFinset x ∪ (G.neighborFinset y ∪ G.neighborFinset z)).card ≤ G.degree y + G.degree z := by
  have h := wedge_order hc hxy hxz hyz cap
  let U := (G.neighborFinset x ∪ (G.neighborFinset y ∪ G.neighborFinset z)).card
  change U ≤ G.degree y + G.degree z
  change Fintype.card V + (k+1)*U ≤ _ at h
  by_contra! bad
  have hm := Nat.mul_le_mul_left k (show G.degree y+G.degree z+1 ≤ U by omega)
  have hd := Nat.mul_le_mul_left k hdeg
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_add k (G.degree x) (G.distEven x)] at h
  rw [Nat.add_mul, Nat.mul_comm r k] at hn
  simp only [Nat.mul_add, Nat.mul_one] at hm hd
  omega

#print axioms local_ore_of_order
end Graph189WedgeOrder
