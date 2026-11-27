import Graph199H1Bridge
import Graph199OrderedRegular
import Graph199Block

namespace Graph199
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  {v w : V} {A : Set V}

private theorem regular_of_far_data (D : H1FarData G v w A) (i : Fin D.n)
    (hi : ¬ ∃ a, D.near i = {a}) :
    ∃ a ∈ D.near i, ∃ b ∈ D.near i, ∃ L : List V,
      L.head? = some a ∧ L.getLast? = some b ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      (∀ x, x ∈ L ↔ x ∈ D.near i ∪ D.far i) := by
  apply block_path _ (D.far_nonempty i) _ (D.indepNum_le_two _ (D.near_facts i))
    (D.far_clique i) (fun a ha b hb => D.same_attachment_complete i a b ha hb)
  · obtain ⟨a,ha⟩ := D.near_nonempty i
    refine ⟨a,ha,?_⟩
    by_contra! h
    apply hi
    refine ⟨a, Set.Subset.antisymm ?_ (Set.singleton_subset_iff.mpr ha)⟩
    intro b hb
    exact Set.mem_singleton_iff.mpr (h b hb).symm
  · apply Set.disjoint_left.mpr
    intro x hn hf
    exact (D.far_facts i x hf).2 (D.near_facts i x hn).2

/-- The central path uses one anchored block, the spare group, and all the
other regular blocks. A short anchor retains only its singleton near port. -/
theorem middle_of_far_data (D : H1FarData G v w A) (i : Fin D.n) (I : Finset (Fin D.n))
    (hI : ∀ j ∈ I, j ≠ i ∧ ¬ ∃ a, D.near j = {a})
    (short : Bool) (hcore : if short then (∃ a, D.near i = {a}) else ¬ ∃ a, D.near i = {a}) :
    ∃ a ∈ D.spare ∪ D.near i, ∃ d : V, ∃ W : List V,
      (d ∈ D.spare ∪ D.near i ∨ ∃ j ∈ I, d ∈ D.near j) ∧
      W.head? = some a ∧ W.getLast? = some d ∧ W.Nodup ∧ W.IsChain G.Adj ∧
      (∀ x, x ∈ W ↔
        x ∈ D.spare ∪ (if short then D.near i else D.near i ∪ D.far i) ∨
          ∃ j ∈ I, x ∈ D.near j ∪ D.far j) := by
  let C := if short then D.near i else D.near i ∪ D.far i
  let E := D.spare ∪ D.near i
  have hanchor :
      ∃ a ∈ D.near i, ∃ b ∈ D.near i, ∃ L : List V,
        L.head? = some a ∧ L.getLast? = some b ∧ L.Nodup ∧ L.IsChain G.Adj ∧
        (∀ x, x ∈ L ↔ x ∈ C) := by
    cases short with
    | false =>
      exact regular_of_far_data D i (by simpa using hcore)
    | true =>
      have hsingle : ∃ a, D.near i = {a} := by simpa using hcore
      obtain ⟨a,ha⟩ := hsingle
      refine ⟨a,by simp [ha],a,by simp [ha],[a],rfl,rfl,by simp,List.IsChain.singleton a,?_⟩
      intro x
      simp [C,ha]
  obtain ⟨a,ha,b,hb,L,hLh,hLl,hLn,hLc,hLm⟩ := hanchor
  have hcore_sep : Disjoint D.spare C := by
    apply Set.disjoint_left.mpr
    intro x hs hx
    cases short with
    | false =>
      rcases hx with hn | hf
      · exact D.spare_disjoint i x hs hn
      · exact (D.far_facts i x hf).2 (D.spare_facts x hs).2
    | true => exact D.spare_disjoint i x hs hx
  obtain ⟨s,hs,t,ht,Q,hQh,hQl,hQn,hQc,hQm⟩ :=
    spare_sandwich hLh hLl hLn hLc hLm hcore_sep
      (D.indepNum_le_two _ D.spare_facts)
      (fun x hx => (D.spare_attachment_complete i x a hx ha).symm)
      (fun x hx => (D.spare_attachment_complete i x b hx hb).symm)
  have hend {x : V} (hx : x ∈ D.spare ∪ ({a,b} : Set V)) : x ∈ E := by
    rcases hx with hx | hx
    · exact Or.inl hx
    · apply Or.inr
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
  have separate {j k : Fin D.n} (hjk : j ≠ k) :
      Disjoint (D.near j ∪ D.far j) (D.near k ∪ D.far k) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact D.near_disjoint hjk hx hy
    · exact (D.far_facts k x hy).2 (D.near_facts j x hx).2
    · exact (D.far_facts j x hx).2 (D.near_facts k x hy).2
    · exact (D.far_separated hjk hx hy).1 rfl
  have csub : C ⊆ D.near i ∪ D.far i := by
    cases short with
    | false => exact fun _ h => h
    | true => exact fun _ h => Or.inl h
  have apart (j : Fin D.n) (hj : j ∈ I) : Disjoint (D.spare ∪ C) (D.near j ∪ D.far j) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases hx with hs | hx
    · rcases hy with hy | hy
      · exact D.spare_disjoint j x hs hy
      · exact (D.far_facts j x hy).2 (D.spare_facts x hs).2
    · exact Set.disjoint_left.mp (separate (hI j hj).1.symm) (csub hx) hy
  have starts (j : Fin D.n) (hj : j ∈ I) (x : V) (hx : x ∈ E)
      (y : V) (hy : y ∈ D.near j) : G.Adj x y := by
    rcases hx with hx | hx
    · exact D.spare_attachment_complete j x y hx hy
    · exact D.cross_attachment_complete (hI j hj).1.symm hx hy
  obtain ⟨d,W,hd,hWh,hWl,hWn,hWc,hWm⟩ :=
    append_indexed_blocks I (D.spare ∪ C) E (fun j => D.near j ∪ D.far j) D.near
      Q s t hQh hQl (hend ht) hQn hQc hQm
      (fun j hj => regular_of_far_data D j (hI j hj).2) apart
      (fun _ _ _ _ h => separate h) starts
      (fun _ _ _ _ h _ hx _ hy => D.cross_attachment_complete h hx hy)
  exact ⟨s,hend hs,d,W,hd,hWh,hWl,hWn,hWc,hWm⟩

#print axioms middle_of_far_data
end Graph199
