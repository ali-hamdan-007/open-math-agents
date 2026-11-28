import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

namespace Graph189RotationGap

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- An endpoint chord past a mark costs the full length of any exterior path
that can enter that mark. The gap is the list strictly between mark and pivot. -/
theorem exterior_length_le_gap_of_endpoint_chord {e v a t : V} (P : G.Walk e v)
    (hP : P.IsPath) (longest : ∀ {u w : V} (Q : G.Walk u w), Q.IsPath → Q.length ≤ P.length)
    (lead gap tail outside : List V)
    (split : P.support = ((e :: lead) ++ [a]) ++ (gap ++ (t :: tail)))
    (chord : G.Adj e t) (external_path : (outside ++ [a]).IsChain G.Adj)
    (external_nodup : outside.Nodup) (disjoint : outside.Disjoint P.support) :
    outside.length ≤ gap.length := by
  let left := (e :: lead) ++ [a]
  let right := t :: tail
  change P.support = left ++ (gap ++ right) at split
  have hchain := P.isChain_adj_support
  rw [split] at hchain
  have leftChain : left.IsChain G.Adj := hchain.left_of_append
  have revChain : left.reverse.IsChain G.Adj :=
    List.isChain_reverse.mpr (leftChain.imp fun _ _ h => h.symm)
  have rightChain : right.IsChain G.Adj := hchain.right_of_append.right_of_append
  have coreChain : (left.reverse ++ right).IsChain G.Adj := by
    apply revChain.append rightChain
    simp only [List.getLast?_reverse]
    simpa [left, right] using chord
  have fullChain : (outside ++ (left.reverse ++ right)).IsChain G.Adj := by
    have base := List.isChain_append.mp external_path
    apply base.1.append coreChain
    simpa [left, right] using base.2.2
  have hn := hP.support_nodup
  rw [split] at hn
  obtain ⟨leftN, remN, separate⟩ := List.nodup_append'.mp hn
  have rightN := (List.nodup_append'.mp remN).2.1
  have LR : left.Disjoint right := fun _ h₁ h₂ => separate h₁ (List.mem_append_right gap h₂)
  have coreN : (left.reverse ++ right).Nodup := by
    exact (left.reverse_perm.append_right right).nodup_iff.mpr
      (List.nodup_append'.mpr ⟨leftN, rightN, LR⟩)
  have fullN : (outside ++ (left.reverse ++ right)).Nodup := by
    apply List.nodup_append'.mpr ⟨external_nodup, coreN, ?_⟩
    intro x ho hc
    apply disjoint ho
    rw [split]
    simp only [List.mem_append, List.mem_reverse] at hc ⊢
    rcases hc with hl | hr
    · exact Or.inl hl
    · exact Or.inr (Or.inr hr)
  let seq := outside ++ (left.reverse ++ right)
  have ne : seq ≠ [] := by simp [seq, right]
  let Q := Walk.ofSupport seq ne fullChain
  have qs : Q.support = seq := Walk.support_ofSupport _ _
  have Qpath : Q.IsPath := Walk.IsPath.mk' (by rw [qs]; exact fullN)
  have hl := longest Q Qpath
  have lp := P.length_support
  have lq := Q.length_support
  rw [split] at lp
  rw [qs] at lq
  simp only [seq, List.length_append, List.length_reverse] at lp lq
  omega

#print axioms exterior_length_le_gap_of_endpoint_chord

end Graph189RotationGap
