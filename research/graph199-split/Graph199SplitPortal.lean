import Mathlib.Data.List.Chain

namespace Graph199

private theorem count_marked_of_no_pair {V : Type*} (marked : V → Bool) (L : List V)
    (last : ∀ x ∈ L.getLast?, marked x = false)
    (adj : L.IsChain (fun a b => ¬ (marked a = true ∧ marked b = true))) :
    (L.filter marked).length + (if L.head?.any (fun x => !(marked x)) then 1 else 0) ≤
      (L.filter (fun x => !(marked x))).length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    cases L with
    | nil =>
      have ha : marked a = false := last a (by simp)
      simp [ha]
    | cons b L =>
      have adj' := List.isChain_cons_cons.mp adj
      have last' : ∀ x ∈ (b :: L).getLast?, marked x = false := by
        intro x hx
        exact last x (by simpa using hx)
      have h := ih last' adj'.2
      cases ha : marked a <;> cases hb : marked b <;>
        simp_all only [List.filter_cons, Bool.not_true, Bool.not_false, Bool.false_eq_true,
          if_false, if_true, List.length_cons, List.head?_cons, Option.any_some]
      all_goals first | omega | exact False.elim (adj'.1 ⟨trivial,trivial⟩)

/-- A nonempty list with at least as many marked as unmarked vertices has
a marked endpoint or adjacent marked entries. -/
theorem marked_list_portal {V : Type*} (marked : V → Bool) (L : List V) (hne : L ≠ [])
    (hcount : (L.filter (fun x => !(marked x))).length ≤ (L.filter marked).length) :
    (∃ x ∈ L.head?, marked x = true) ∨ (∃ x ∈ L.getLast?, marked x = true) ∨
      ∃ P S a b, L = P ++ a :: b :: S ∧ marked a = true ∧ marked b = true := by
  classical
  by_contra! hn
  obtain ⟨hfirst,hlast,hpair⟩ := hn
  have hchain : L.IsChain (fun a b => ¬ (marked a = true ∧ marked b = true)) := by
    rw [List.isChain_iff_forall_rel_of_append_cons_cons]
    intro a b P S he ⟨ha,hb⟩
    exact hpair P S a b he ha hb
  have last x (hx : x ∈ L.getLast?) : marked x = false := by
    cases he : marked x
    · rfl
    · exact False.elim (hlast x hx he)
  have h := count_marked_of_no_pair marked L last hchain
  cases L with
  | nil => exact hne rfl
  | cons a L =>
    have ha : marked a = false := by
      cases he : marked a
      · rfl
      · exact False.elim (hfirst a (by simp) he)
    simp only [List.head?_cons, Option.any_some, ha, Bool.not_false, if_true] at h
    omega

#print axioms marked_list_portal

end Graph199
