import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset SimpleGraph
namespace Graph189SeparatorCover
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- If a family of first steps meets a shortest route from x to every anchor,
its even-distance sets and that of x cover the separated target set B. -/
theorem first_step_cover (hc : G.Connected) (x : V) (B S R : Finset V)
    (hroot : x ∉ B) (outside : ∀ u ∈ R, u ∉ B)
    (edge : ∀ u ∈ R, G.Adj x u)
    (through : ∀ b ∈ B, ∃ a ∈ S, G.dist x b = G.dist x a + G.dist a b)
    (steps : ∀ a ∈ S, ∃ u ∈ R, G.dist x a = G.dist u a + 1)
    (k : ℕ) (cap : ∀ u, G.distEven u ≤ k+1) :
    B.card ≤ (R.card+1)*k := by
  classical
  let E (v : V) := (univ.filter (fun w => Even (G.dist v w))).erase v
  have ecap (v : V) : (E v).card ≤ k := by
    have hv : v ∈ univ.filter (fun w => Even (G.dist v w)) := by simp
    have hsize := Finset.card_erase_of_mem hv
    change ((univ.filter (fun w => Even (G.dist v w))).erase v).card ≤ k
    have h := cap v
    change (univ.filter (fun w => Even (G.dist v w))).card ≤ k+1 at h
    omega
  have member {v b : V} (h : b ≠ v) (p : Even (G.dist v b)) : b ∈ E v :=
    Finset.mem_erase.mpr ⟨h, Finset.mem_filter.mpr ⟨Finset.mem_univ _,p⟩⟩
  have covered : B ⊆ E x ∪ R.biUnion E := by
    intro b hb
    by_cases p : Even (G.dist x b)
    · exact mem_union_left _ (member (fun eq => hroot (eq ▸ hb)) p)
    obtain ⟨a,ha,route⟩ := through b hb
    obtain ⟨u,hu,shorter⟩ := steps a ha
    have hi := hc.dist_triangle (u:=u) (v:=a) (w:=b)
    have lo := hc.dist_triangle (u:=x) (v:=u) (w:=b)
    rw [dist_eq_one_iff_adj.mpr (edge u hu)] at lo
    have e : Even (G.dist u b) := by rw [Nat.even_iff] at p ⊢; omega
    exact mem_union_right _ (mem_biUnion.mpr ⟨u,hu,member (fun eq => outside u hu (eq ▸ hb)) e⟩)
  calc B.card ≤ (E x ∪ R.biUnion E).card := card_le_card covered
       _ ≤ (E x).card + (R.biUnion E).card := card_union_le _ _
       _ ≤ k + ∑ u ∈ R, (E u).card := Nat.add_le_add (ecap x) Finset.card_biUnion_le
       _ ≤ k + ∑ _u ∈ R, k := Nat.add_le_add_left (Finset.sum_le_sum (fun u _ => ecap u)) k
       _ = (R.card + 1)*k := by
         simp [Nat.add_mul, Nat.add_comm]

/-- Requiring every walk from x to B to pass through S gives the shortest-route
hypothesis of the count above. The cut need not be minimum. -/
theorem of_walk_separator (hc : G.Connected) (x : V) (B S R : Finset V)
    (hroot : x ∉ B) (outside : ∀ u ∈ R, u ∉ B) (edge : ∀ u ∈ R, G.Adj x u)
    (cut : ∀ b ∈ B, ∀ p : G.Walk x b, ∃ a ∈ S, a ∈ p.support)
    (steps : ∀ a ∈ S, ∃ u ∈ R, G.dist x a = G.dist u a + 1)
    (k : ℕ) (cap : ∀ u, G.distEven u ≤ k+1) : B.card ≤ (R.card+1)*k := by
  classical
  apply first_step_cover hc x B S R hroot outside edge _ steps k cap
  intro b hb
  obtain ⟨p,hp⟩ := (hc x b).exists_walk_length_eq_dist
  obtain ⟨a,ha,hmem⟩ := cut b hb p
  refine ⟨a,ha,?_⟩
  have split : (p.takeUntil a hmem).append (p.dropUntil a hmem) = p := Walk.take_spec p hmem
  have lengths := congrArg SimpleGraph.Walk.length split
  rw [SimpleGraph.Walk.length_append] at lengths
  have hleft := G.dist_le (p.takeUntil a hmem)
  have hright := G.dist_le (p.dropUntil a hmem)
  have triangle := hc.dist_triangle (u:=x) (v:=a) (w:=b)
  omega

#print axioms of_walk_separator
#print axioms first_step_cover
end Graph189SeparatorCover
