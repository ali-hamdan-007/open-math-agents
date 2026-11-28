import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

namespace Graph189CrossPivot

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The two ends of a longest nonspanning path cannot have crossed pivot edges
     along the same oriented path edge. The path is split on that edge. -/
theorem no_crossed_pivots {u a b v : V} (left : G.Walk u a) (right : G.Walk b v)
    (ab : G.Adj a b) (connected : G.Connected)
    (simple : (left.append (.cons ab right)).IsPath)
    (size : 2 ≤ (left.append (.cons ab right)).length)
    (omitted : ∃ x, x ∉ (left.append (.cons ab right)).support)
    (longest : ∀ {i j : V} (Q : G.Walk i j), Q.IsPath →
      Q.length ≤ (left.append (.cons ab right)).length) :
    ¬ (G.Adj a v ∧ G.Adj u b) := by
  classical
  rintro ⟨av,ub⟩
  let P := left.append (.cons ab right)
  let Q := left.append (.cons av right.reverse)
  have ps : P.support = left.support ++ right.support := by simp [P, Walk.support_append]
  have qs : Q.support = left.support ++ right.support.reverse := by simp [Q, Walk.support_append]
  have perm : Q.support.Perm P.support := by
    rw [ps,qs]
    exact right.support.reverse_perm.append_left _
  have qp : Q.IsPath := Walk.IsPath.mk' (perm.nodup_iff.mpr simple.support_nodup)
  have eqLen : Q.length = P.length := by simp [P,Q]
  let C := Walk.cons ub.symm Q
  have cp : C.IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨?_, ?_⟩
    · simpa [C] using qp
    · change 2 ≤ P.length at size
      simp only [C,Walk.length_cons,eqLen]
      omega
  have memC (w : V) : w ∈ C.support ↔ w ∈ P.support := by
    have hb : b ∈ P.support := perm.mem_iff.mp Q.end_mem_support
    simp only [C, Walk.support_cons, List.mem_cons, perm.mem_iff]
    exact ⟨fun h => h.elim (fun eq => eq ▸ hb) id, Or.inr⟩
  obtain ⟨x,hx⟩ := omitted
  change x ∉ P.support at hx
  obtain ⟨W⟩ := connected u x
  obtain ⟨d,_,inside,outside⟩ := W.exists_boundary_dart {w | w ∈ P.support} P.start_mem_support hx
  have dc : d.fst ∈ C.support := (memC _).mpr inside
  let D := C.rotate d.fst dc
  have dp : D.IsCycle := cp.rotate dc
  have missed : d.snd ∉ D.dropLast.support := by
    intro h
    rw [D.support_dropLast dp.not_nil] at h
    have hs : d.snd ∈ D.support := List.mem_of_mem_dropLast h
    have hc : d.snd ∈ C.support := (C.mem_support_rotate_iff _ dc).mp hs
    exact outside ((memC _).mp hc)
  let T := Walk.cons d.adj.symm D.dropLast
  have tp : T.IsPath := dp.isPath_dropLast.cons missed
  have hl := longest T tp
  change T.length ≤ P.length at hl
  have hd := D.length_dropLast_add_one dp.not_nil
  have dl : D.length = Q.length + 1 := by simp [D,C]
  simp only [T,Walk.length_cons] at hl
  omega

#print axioms no_crossed_pivots

end Graph189CrossPivot
