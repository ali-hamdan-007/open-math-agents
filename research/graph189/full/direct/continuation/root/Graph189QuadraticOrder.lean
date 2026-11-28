import Graph189LayerCutoff
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Degrees

open SimpleGraph Finset
namespace Graph189QuadraticOrder
variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Maximising the existing private-cover bound at a specified root. -/
theorem rooted (hc : G.Connected) (z : V) (k : ℕ) (cap : ∀ v, G.distEven v ≤ k+1) :
    4*Fintype.card V ≤ 4*(1+G.degree z+k)+(k+1)^2 := by
  classical
  have covers : ∀ b ∈ Graph189LayerCover.layer G z 2, ∃ a ∈ G.neighborFinset z, G.Adj a b := by
    intro b hb
    have two := Graph189LayerCover.in_layer.mp hb
    obtain ⟨walk, hlen⟩ := (hc b z).exists_walk_length_eq_dist
    have hdist : G.dist b z = 2 := by rwa [dist_comm]
    rw [hdist] at hlen
    cases walk with
    | nil => simp at hlen
    | cons e walk =>
      rename_i a
      have hlen' : walk.length = 1 := by rw [Walk.length_cons] at hlen; omega
      have hle : G.dist z a ≤ 1 := by rw [dist_comm]; exact hlen' ▸ G.dist_le walk
      have had := e.diff_dist_adj (u := z)
      exact ⟨a, (G.mem_neighborFinset z a).mpr (dist_eq_one_iff_adj.mp (by omega)), e.symm⟩
  obtain ⟨t,_,ht,hn⟩ := Graph189LayerCover.order_of_cover G hc z k cap (G.neighborFinset z)
    (fun a ha => (G.mem_neighborFinset z a).mp ha) covers
  have hrow : 4*t*(k+1-t) ≤ (k+1)^2 := by
    zify [ht]
    nlinarith [sq_nonneg ((k:ℤ)+1-2*t)]
  nlinarith only [hrow,hn]

theorem second_attained [Nontrivial V] : ∃ z : V, G.degree z = G.secondSmallestDegree := by
  classical
  let ds := G.degreeSequence
  have len : 1 < ds.length := by simpa [ds,degreeSequence] using Fintype.one_lt_card (α := V)
  have mem : G.secondSmallestDegree ∈ ds := by
    change ds.getD 1 0 ∈ ds
    cases h : ds with
    | nil => simp [h] at len
    | cons a t =>
      cases h' : t with
      | nil => simp [h,h'] at len
      | cons b t => simp
  have hm : G.secondSmallestDegree ∈ univ.val.map (fun v : V => G.degree v) := by
    simpa [ds,degreeSequence] using mem
  obtain ⟨z,_,hz⟩ := Multiset.mem_map.mp hm
  exact ⟨z,hz⟩

theorem order (hc : G.Connected) [Nontrivial V]
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) :
    4*Fintype.card V ≤ 4+8*G.secondSmallestDegree+(G.secondSmallestDegree+1)^2 := by
  obtain ⟨z,hz⟩ := second_attained (G:=G)
  have bound := rooted hc z G.secondSmallestDegree cap
  rw [hz] at bound
  omega

theorem small_degrees (hc : G.Connected) [Nontrivial V]
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) :
    (G.secondSmallestDegree=3 → Fintype.card V≤11) ∧
    (G.secondSmallestDegree=4 → Fintype.card V≤15) ∧
    (G.secondSmallestDegree=5 → Fintype.card V≤20) := by
  have bound := order hc cap
  constructor
  · intro h
    rw [h] at bound
    omega
  constructor <;> intro h <;> rw [h] at bound <;> omega

#print axioms order
#print axioms small_degrees
end Graph189QuadraticOrder
