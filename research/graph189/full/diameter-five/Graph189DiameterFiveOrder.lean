import Graph189DistanceLayers
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

namespace Graph189DiameterFiveOrder
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every middle vertex missed at distance two must use one of the
second-layer vertices missed by x. Each such vertex covers at most h
middle vertices. -/
theorem count_middle {B C : Finset V} {x : V} {h i : ℕ}
    (hx : x ∉ C) (hn : ∀ v ∈ C, ¬ G.Adj x v)
    (hpred : ∀ v ∈ C, ∃ b ∈ B, G.Adj b v)
    (hvisible : (C.filter (fun v => G.dist x v = 2)).card ≤ h)
    (hB : (B \ G.neighborFinset x).card ≤ i)
    (hb : ∀ b ∈ B, (C ∩ G.neighborFinset b).card ≤ h) :
    C.card ≤ h * (i+1) := by
  let S := C.filter (fun v => G.dist x v = 2)
  let M := B \ G.neighborFinset x
  let U (b : V) := C ∩ G.neighborFinset b
  have hcover : C ⊆ S ∪ M.biUnion U := by
    intro v hv
    by_cases hd : G.dist x v = 2
    · exact mem_union_left _ (mem_filter.mpr ⟨hv,hd⟩)
    · obtain ⟨b,hbB,hbv⟩ := hpred v hv
      have hmiss : b ∉ G.neighborFinset x := by
        intro hxb
        exact hd (Graph189LowDegreeTwo.two_edges ((G.mem_neighborFinset x b).mp hxb)
          hbv (fun e => hx (e.symm ▸ hv)) (hn v hv))
      exact mem_union_right _ (mem_biUnion.mpr ⟨b,mem_sdiff.mpr ⟨hbB,hmiss⟩,
        mem_inter.mpr ⟨hv,(G.mem_neighborFinset b v).mpr hbv⟩⟩)
  have hcount := (card_le_card hcover).trans (card_union_le S (M.biUnion U))
  have hm := card_biUnion_le_card_mul M U h (fun b hbM => hb b (mem_sdiff.mp hbM).1)
  have hm' : M.card * h ≤ i*h := Nat.mul_le_mul_right h hB
  change S.card ≤ h at hvisible
  nlinarith

/-- A middle vertex missed at distance two has at most i second-layer
neighbors. Its degree bounds the required total number of middle vertices. -/
theorem degree_at_missed_middle {B C D : Finset V} {x v : V} {i s : ℕ}
    (hv : v ∈ C) (hxv : x ≠ v) (hn : ¬ G.Adj x v) (hd : G.dist x v ≠ 2)
    (hB : (B \ G.neighborFinset x).card ≤ i)
    (hcover : G.neighborFinset v ⊆ (B ∪ C) ∪ D) (hdeg : s ≤ G.degree v) :
    s+1 ≤ i + C.card + D.card := by
  have hsub : B ∩ G.neighborFinset v ⊆ B \ G.neighborFinset x := by
    intro b hb
    obtain ⟨hbB,hbv⟩ := mem_inter.mp hb
    refine mem_sdiff.mpr ⟨hbB,fun h => hd ?_⟩
    exact Graph189LowDegreeTwo.two_edges ((G.mem_neighborFinset x b).mp h)
      ((G.mem_neighborFinset v b).mp hbv).symm hxv hn
  let P := B ∩ G.neighborFinset v
  have hp : P.card ≤ i := (card_le_card hsub).trans hB
  have hsub' : G.neighborFinset v ⊆ (P ∪ C.erase v) ∪ D := by
    intro y hy
    rcases mem_union.mp (hcover hy) with hbc | d
    · apply mem_union_left
      rcases mem_union.mp hbc with b | c
      · exact mem_union_left _ (mem_inter.mpr ⟨b,hy⟩)
      · exact mem_union_right _ (mem_erase.mpr ⟨((G.mem_neighborFinset v y).mp hy).ne.symm,c⟩)
    · exact mem_union_right _ d
  have hcount := (card_le_card hsub').trans (card_union_le (P ∪ C.erase v) D)
  rw [G.card_neighborFinset_eq_degree] at hcount
  have hcount' := card_union_le P (C.erase v)
  rw [card_erase_of_mem hv] at hcount'
  have hpos : 0 < C.card := card_pos.mpr ⟨v,hv⟩
  omega

/-- The order bound after collecting the five level inequalities.
In particular the second-smallest degree is bounded quadratically
by the minimum degree. This arithmetic form avoids rounding. -/
theorem quadratic_degree_bound {a c d s i h : ℕ}
    (hgrade : s+1 ≤ i+c+d) (hC : c ≤ h*(i+1))
    (hleft : i+d ≤ a) (hright : h+1 ≤ d) :
    4*(s+1) ≤ 4*a+a*a := by
  have ht : i+1+h ≤ a := by omega
  have hmul : h*(i+1+h) ≤ h*a := Nat.mul_le_mul_left h ht
  have hsq : (2*(h:ℤ)-(a:ℤ))^2 ≥ 0 := sq_nonneg _
  zify at *
  nlinarith

end Graph189DiameterFiveOrder

#print axioms Graph189DiameterFiveOrder.count_middle
#print axioms Graph189DiameterFiveOrder.degree_at_missed_middle
#print axioms Graph189DiameterFiveOrder.quadratic_degree_bound
