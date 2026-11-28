import Graph189RootedPath
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Graph189RootedOneLow
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V} [DecidableRel H.Adj]

private theorem degree_if_confined {r a : V} (P : H.Walk r a) (v : V)
    (mem : v ∈ P.support) (all : ∀ z, H.Adj v z → z∈P.support) : H.degree v < P.support.length := by
  classical
  have cover : H.neighborFinset v ⊆ P.support.toFinset.erase v := by
    intro z hz
    have e := (H.mem_neighborFinset _ _).mp hz
    exact mem_erase.mpr ⟨e.ne.symm,List.mem_toFinset.mpr (all z e)⟩
  have small := card_le_card cover
  rw [H.card_neighborFinset_eq_degree] at small
  have erase := card_erase_add_one (List.mem_toFinset.mpr mem)
  have bound := List.toFinset_card_le P.support
  omega

/-- A longest path starting at r has at least d+1 vertices when at most one
vertex has degree below d and r is nonisolated. The endpoint can be replaced
by a fresh neighbor of its high-degree predecessor when necessary. -/
theorem rooted_path (r : V) {d : ℕ} (start : ∃ b,H.Adj r b)
    (pair : ∀ a b : V, a≠b → d≤H.degree a ∨ d≤H.degree b) :
    ∃ b, ∃ P : H.Walk r b, P.IsPath ∧ d+1 ≤ P.support.length := by
  classical
  obtain ⟨v,P,hp,maximal⟩ := Graph189RootedPath.exists_rooted_longest H r
  have terminal {a : V} (Q : H.Walk r a) (hq : Q.IsPath) (equal : Q.length=P.length) :
      H.degree a < Q.support.length := by
    apply degree_if_confined (P:=Q) a Q.end_mem_support
    intro t edge
    by_contra no
    have ext := maximal (Q.concat edge) (hq.concat no edge)
    rw [Walk.length_concat,equal] at ext
    omega
  obtain ⟨b,e⟩ := start
  have one := maximal e.toWalk e.isPath_toWalk
  have pos : 0<P.length := by
    have len1 : 1 ≤ P.length := by simpa using one
    omega
  have nn := Walk.not_nil_iff_lt_length.mpr pos
  have edge := P.adj_penultimate nn
  by_cases high : d≤H.degree v
  · exact ⟨v,P,hp,by have := terminal P hp rfl; omega⟩
  have predHigh := (pair v P.penultimate edge.ne.symm).resolve_left high
  by_cases all : ∀ b, H.Adj P.penultimate b → b∈P.support
  · have inside : P.penultimate∈P.support := by
      have h := P.dropLast.end_mem_support
      rw [P.support_dropLast nn] at h
      exact List.mem_of_mem_dropLast h
    have small := degree_if_confined P P.penultimate inside all
    exact ⟨v,P,hp,by omega⟩
  obtain ⟨b,adj⟩ := not_forall.mp all
  have hit : H.Adj P.penultimate b := Classical.byContradiction (fun miss => adj (fun h => (miss h).elim))
  have outside : b∉P.support := fun h => adj (fun _ => h)
  have less : b ≠ v := fun eq => outside (eq.symm ▸ P.end_mem_support)
  have hb := (pair v b less.symm).resolve_left high
  let Q := P.dropLast.concat hit
  have safe : b∉P.dropLast.support := by
    rw [P.support_dropLast nn]
    exact fun h => outside (List.mem_of_mem_dropLast h)
  have hq : Q.IsPath := hp.dropLast.concat safe hit
  have equal : Q.length=P.length := by
    simpa [Q] using P.length_dropLast_add_one nn
  have bound := terminal Q hq equal
  exact ⟨b,Q,hq,by omega⟩

#print axioms rooted_path
end Graph189RootedOneLow
