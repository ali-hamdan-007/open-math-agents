import Graph189DegreeCeiling
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Degrees

namespace Graph189DegreeCeiling
open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The distance-even hypothesis supplies the exact second-layer cap. -/
theorem degree_le_three_mul (hc : G.Connected) {k : ℕ}
    (cap : ∀ v, G.distEven v ≤ k+1) {z : V} (hz : G.degree z ≤ k) (x : V) :
    G.degree x ≤ 3*k := by
  classical
  let D (v : V) := univ.filter (fun w => G.dist v w = 2)
  have limited (v : V) : (D v).card ≤ k := by
    have sub : insert v (D v) ⊆ univ.filter (fun w => Even (G.dist v w)) := by
      intro w hw
      rcases mem_insert.mp hw with rfl | h
      · exact mem_filter.mpr ⟨mem_univ _,by simp⟩
      · have h2 := (mem_filter.mp h).2
        exact mem_filter.mpr ⟨mem_univ _,by simp [h2]⟩
    have notmem : v ∉ D v := by simp [D]
    have h := card_le_card sub
    rw [card_insert_of_notMem notmem] at h
    change _ ≤ G.distEven v at h
    have := cap v
    omega
  exact degree_le_three_mul_of_distance_two_cap hc limited hz x

/-- The exact maximum-degree ceiling for the hypotheses of WOWII Conjecture 189. -/
theorem maxDegree_le_three_mul_secondSmallestDegree [Nontrivial V] (hc : G.Connected)
    (cap : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree) :
    G.maxDegree ≤ 3 * G.secondSmallestDegree := by
  classical
  let ds := G.degreeSequence
  have len : 1 < ds.length := by
    simpa [ds, degreeSequence] using Fintype.one_lt_card (α := V)
  have mem : G.secondSmallestDegree ∈ ds := by
    change ds.getD 1 0 ∈ ds
    cases he : ds with
    | nil => simp [he] at len
    | cons a tail =>
      cases he2 : tail with
      | nil => simp [he, he2] at len
      | cons b rest => simp
  have hm : G.secondSmallestDegree ∈ Finset.univ.val.map (fun v : V => G.degree v) := by
    simpa [ds, degreeSequence] using mem
  obtain ⟨z,_,hz⟩ := Multiset.mem_map.mp hm
  exact G.maxDegree_le_of_forall_degree_le _
    (degree_le_three_mul hc (fun v => by simpa [Nat.add_comm] using cap v) hz.le)

#print axioms maxDegree_le_three_mul_secondSmallestDegree
end Graph189DegreeCeiling
