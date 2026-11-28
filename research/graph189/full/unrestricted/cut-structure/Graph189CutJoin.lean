module

public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Data.Finset.Basic

public section

open SimpleGraph

namespace Graph189CutJoin

variable {V : Type*} {G : SimpleGraph V}

private theorem walk_of_chain {a : V} {xs : List V} (h : (a :: xs).IsChain G.Adj) :
    ∃ b, ∃ w : G.Walk a b, w.support = a :: xs := by
  induction xs generalizing a with
  | nil => exact ⟨a, .nil, rfl⟩
  | cons x xs ih =>
    obtain ⟨e, ht⟩ := List.isChain_cons_cons.mp h
    obtain ⟨b, w, hw⟩ := ih ht
    exact ⟨b, .cons e w, by simp [hw]⟩

/-- Splice two ambient vertex lists rooted at the common cut vertex. -/
theorem hamiltonian_of_rooted_sides [DecidableEq V] {c : V} {A B : Finset V}
    (hdis : Disjoint A B) (hcover : ∀ x, x=c ∨ x∈A ∨ x∈B)
    (rootA : ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ x, x∈L ↔ x=c ∨ x∈A)
    (rootB : ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ x, x∈L ↔ x=c ∨ x∈B) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨left, hlhead, hln, hlc, hlm⟩ := rootA
  obtain ⟨right, hrhead, hrn, hrc, hrm⟩ := rootB
  cases left with
  | nil => simp at hlhead
  | cons l ls =>
    simp only [List.head?_cons, Option.some.injEq] at hlhead
    subst l
    cases right with
    | nil => simp at hrhead
    | cons r rs =>
      simp only [List.head?_cons, Option.some.injEq] at hrhead
      subst r
      obtain ⟨a, p, hp⟩ := walk_of_chain hlc
      obtain ⟨b, q, hq⟩ := walk_of_chain hrc
      refine ⟨a, b, p.reverse.append q, ?_⟩
      intro x
      simp only [Walk.support_append, Walk.support_reverse, hp, hq, List.tail_cons,
        List.count_append, List.count_reverse]
      by_cases hx : x ∈ c :: ls
      · have hr : x ∉ rs := by
          intro hxr
          have hne : x ≠ c := fun he => (List.nodup_cons.mp hrn).1 (he ▸ hxr)
          have ha := (hlm x).mp hx
          have hb := (hrm x).mp (List.mem_cons_of_mem _ hxr)
          exact Finset.disjoint_left.mp hdis (ha.resolve_left hne) (hb.resolve_left hne)
        simp [List.count_eq_one_of_mem hln hx, List.count_eq_zero_of_not_mem hr]
      · have hne : x ≠ c := fun he => hx (he ▸ List.mem_cons_self)
        have hb : x∈B := ((hcover x).resolve_left hne).resolve_left
          (fun ha => hx ((hlm x).mpr (.inr ha)))
        have hxr : x ∈ rs := (List.mem_cons.mp ((hrm x).mpr (.inr hb))).resolve_left hne
        simp [List.count_eq_zero_of_not_mem hx, List.count_eq_one_of_mem
          (List.nodup_cons.mp hrn).2 hxr]

#print axioms hamiltonian_of_rooted_sides
end Graph189CutJoin
