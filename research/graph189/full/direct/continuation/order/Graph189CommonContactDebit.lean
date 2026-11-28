import Graph189PrivateContactProfile

open Finset SimpleGraph
namespace Graph189PrivateContactProfile
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B S : Finset V} {p q : V}

/-- On the side opposite a common-free side, a common contact occupies
both anchor columns and is counted once in the side's order. -/
theorem order_of_common (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (pair : S = {p, q}) (ne : p ≠ q) (sc : S.card ≤ G.vertexConnectivity)
    (point : ∀ v, G.distEven v ≤ G.secondSmallestDegree + 1)
    (free : ∀ x ∈ B, ¬ (G.Adj x p ∧ G.Adj x q))
    (common : ∃ x ∈ A, ∀ i ∈ S, G.Adj x i) :
    A.card + 3 ≤ 2 * G.secondSmallestDegree +
      (A.filter (fun x => G.dist p x ≠ 1 ∧ G.dist q x ≠ 1)).card := by
  classical
  let P := A.filter (G.Adj p)
  let Q := A.filter (G.Adj q)
  let R := A.filter (fun x => G.dist p x ≠ 1 ∧ G.dist q x ≠ 1)
  have ps : p ∈ S := by simp [pair]
  have qs : q ∈ S := by simp [pair]
  have contact (i : V) (si : i ∈ S) := (sides.contacts_of_minimum (fun T h =>
    Graph189CutSides.connected_after_smaller_deletion T (h.trans_le sc)) si).2
  obtain ⟨x, xb, xp⟩ := contact p ps
  obtain ⟨y, yb, yq⟩ := contact q qs
  have pbound : P.card + 1 ≤ G.secondSmallestDegree :=
    ports hc sides.swap pair ne sc point xb xp (fun xq => free x xb ⟨xp, xq⟩)
  have qbound : Q.card + 1 ≤ G.secondSmallestDegree :=
    ports hc sides.swap (pair.trans (Finset.pair_comm _ _)) ne.symm sc point
      yb yq (fun yp => free y yb ⟨yp, yq⟩)
  obtain ⟨z, za, both⟩ := common
  have overlap : 1 ≤ (P ∩ Q).card := card_pos.mpr ⟨z, mem_inter.mpr
    ⟨mem_filter.mpr ⟨za, (both p ps).symm⟩, mem_filter.mpr ⟨za, (both q qs).symm⟩⟩⟩
  have cover : A ⊆ (P ∪ Q) ∪ R := by
    intro b ba
    by_cases bp : G.Adj p b
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨ba, bp⟩))
    by_cases bq : G.Adj q b
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨ba, bq⟩))
    exact mem_union_right _ (mem_filter.mpr
      ⟨ba, fun h => bp (dist_eq_one_iff_adj.mp h), fun h => bq (dist_eq_one_iff_adj.mp h)⟩)
  have size := (card_le_card cover).trans (card_union_le _ _)
  have union := card_union_add_card_inter P Q
  change A.card + 3 ≤ 2 * G.secondSmallestDegree + R.card
  omega

#print axioms order_of_common
end Graph189PrivateContactProfile
