module
public import Graph189Marked
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Nodup
public section

namespace Graph189SmallRoot
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {c : V}

private theorem contact_eq {a : Option V} (h : (marked G c).Adj a none) :
    a = some c := by
  cases a with
  | none => exact False.elim h
  | some a => exact congrArg some h

private theorem endpoint : ∀ (l : List (Option V)), l.Nodup →
    l.IsChain (marked G c).Adj → none ∈ l →
    l.head? = some none ∨ l.getLast? = some none
  | [], _, _, hm => by simp at hm
  | [a], _, _, hm => by
    have h : none = a := by simpa using hm
    exact Or.inl (by simp [← h])
  | a :: b :: l, hn, hc, hm => by
    by_cases ha : a = none
    · exact Or.inl (by simp [ha])
    have mem : none ∈ b :: l := (List.mem_cons.mp hm).resolve_left (Ne.symm ha)
    rcases endpoint (b :: l) (List.nodup_cons.mp hn).2
        (List.isChain_cons_cons.mp hc).2 mem with first | last
    · have hb : b = none := by simpa using first
      subst b
      cases l with
      | nil => exact Or.inr (by simp)
      | cons d t =>
        have links := List.isChain_cons_cons.mp hc
        have ad : a = d := (contact_eq links.1).trans
          (contact_eq (List.isChain_cons_cons.mp links.2).1.symm).symm
        exact False.elim ((List.nodup_cons.mp hn).1 (by simp [ad]))
    · exact Or.inr (by simpa using last)

private theorem all_some : ∀ (l : List (Option V)), none ∉ l →
    ∃ s : List V, l = s.map some
  | [], _ => ⟨[], rfl⟩
  | none :: _, hn => False.elim (hn (by simp))
  | some x :: xs, hn => by
    obtain ⟨ys, hy⟩ := all_some xs (fun h => hn (List.mem_cons_of_mem _ h))
    exact ⟨x :: ys, by simp [hy]⟩

theorem rooted_of_marked_traceable [DecidableEq V]
    (h : ∃ a b, ∃ p : (marked G c).Walk a b, p.IsHamiltonian) :
    ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain G.Adj ∧ ∀ v, v ∈ L := by
  obtain ⟨_, _, p, hp⟩ := h
  have orient : ∃ l : List (Option V), l.head? = some none ∧ l.Nodup ∧
      l.IsChain (marked G c).Adj ∧ ∀ w, w ∈ l := by
    rcases endpoint p.support hp.isPath.support_nodup p.isChain_adj_support
      (hp.mem_support none) with left | right
    · exact ⟨_, left, hp.isPath.support_nodup, p.isChain_adj_support, hp.mem_support⟩
    · refine ⟨p.support.reverse, by simpa using right, by simpa using hp.isPath.support_nodup,
        List.isChain_reverse.mpr (p.isChain_adj_support.imp fun _ _ e => e.symm), ?_⟩
      simpa using hp.mem_support
  obtain ⟨l, first, nodup, chain, full⟩ := orient
  cases l with
  | nil => simp at first
  | cons m r =>
    have hm : m = none := by simpa using first
    subst m
    obtain ⟨s, rfl⟩ := all_some r (List.nodup_cons.mp nodup).1
    have all (v : V) : v ∈ s := by simpa using full (some v)
    have sc : s.IsChain G.Adj :=
      (List.isChain_map some).mp chain.tail
    refine ⟨s, ?_, List.Nodup.of_map some (List.nodup_cons.mp nodup).2, sc, all⟩
    cases s with
    | nil => exact False.elim (by simpa using all c)
    | cons x xs =>
      have hxc : x = c := (List.isChain_cons_cons.mp chain).1
      simp [hxc]
end Graph189SmallRoot

#print axioms Graph189SmallRoot.rooted_of_marked_traceable
