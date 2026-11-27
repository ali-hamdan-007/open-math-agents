import Graph199BlockChain
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.Group.Fin.Basic

namespace BipartiteMissingMatching
open SimpleGraph
open scoped Fin.CommRing Fin.NatCast

/-- On (k) left vertices and (k+1) right vertices, with (kge 3), a graph that contains
every cross edge except possibly an indexed matching has a Hamiltonian path. -/
theorem hamiltonian {k : ℕ} (hk : 3 ≤ k) (G : SimpleGraph (Fin k ⊕ Option (Fin k)))
    (hcross : ∀ i j : Fin k, i ≠ j → G.Adj (.inl i) (.inr (some j)))
    (hfree : ∀ i : Fin k, G.Adj (.inl i) (.inr none)) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have : NeZero k := ⟨by omega⟩
  let block : Fin k → List (Fin k ⊕ Option (Fin k)) :=
    fun i => [.inr (some i), .inl (i + (2 : Fin k))]
  let last : List (Fin k ⊕ Option (Fin k)) := [.inr none]
  let base := (List.finRange k).map block
  have zero_two : (2 : Fin k) ≠ 0 := by
    intro h
    have he : (2 : Fin k).val = (0 : Fin k).val := congrArg Fin.val h
    change ((2 : ℕ) % k) = 0 at he
    rw [Nat.mod_eq_of_lt (by omega : 2 < k)] at he
    omega
  have one_two : (2 : Fin k) ≠ 1 := by
    intro h
    have he : (2 : Fin k).val = (1 : Fin k).val := congrArg Fin.val h
    change ((2 : ℕ) % k) = 1 % k at he
    rw [Nat.mod_eq_of_lt (by omega : 2 < k), Nat.mod_eq_of_lt (by omega : 1 < k)] at he
    omega
  have hparts (L : List (Fin k ⊕ Option (Fin k))) (hL : L ∈ base ++ [last]) :
      L ≠ [] ∧ L.Nodup ∧ L.IsChain G.Adj := by
    rcases List.mem_append.mp hL with hh | hh
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hh
      have hn : i + (2 : Fin k) ≠ i := fun h => zero_two
        (add_left_cancel (a := i) (by simpa using h))
      simp [block, (hcross _ _ hn).symm]
    · have he : L = last := by simpa using hh
      subst L
      simp [last]
  have hdis (i j : Fin k) (hij : i ≠ j) : List.Disjoint (block i) (block j) := by
    intro x hx hy
    simp only [block, List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with hy | hy
    · exact hij (Option.some.inj (Sum.inr.inj hy))
    · cases hy
    · cases hy
    · exact hij (add_right_cancel (Sum.inl.inj hy))
  have hpair : base.Pairwise List.Disjoint :=
    List.pairwise_map.mpr ((List.nodup_iff_pairwise_ne.mp (List.nodup_finRange k)).imp (fun h => hdis _ _ h))
  have hlastDisjoint (L : List (Fin k ⊕ Option (Fin k))) (hL : L ∈ base) :
      List.Disjoint L last := by
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hL
    intro x hx hy
    have he : x = Sum.inr none := by simpa [last] using hy
    subst x
    simp [block] at hx
  have hlinks : base.IsChain (fun L R =>
      ∀ a ∈ L.getLast?, ∀ b ∈ R.head?, G.Adj a b) := by
    rw [List.isChain_map, List.isChain_iff_getElem]
    intro i hi a ha b hb
    have hi' : i+1 < k := by simpa using hi
    let x : Fin k := ⟨i,by omega⟩
    let y : Fin k := ⟨i+1,hi'⟩
    have hx : (List.finRange k)[i] = x := by
      apply Fin.ext
      simp [List.getElem_finRange,x]
    have hy : (List.finRange k)[i+1] = y := by
      apply Fin.ext
      simp [List.getElem_finRange,y]
    have hs : y = x + (1 : Fin k) := by
      apply Fin.ext
      rw [Fin.val_add]
      change i + 1 = (i + 1 % k) % k
      rw [Nat.mod_eq_of_lt (by omega : 1 < k), Nat.mod_eq_of_lt hi']
    have hne : x + (2 : Fin k) ≠ y := by
      rw [hs]
      exact fun h => one_two (add_left_cancel h)
    have ha' : Sum.inl (x + (2 : Fin k)) = a := by simpa [hx, block] using ha
    have hb' : Sum.inr (some y) = b := by simpa [hy, block] using hb
    exact ha' ▸ hb' ▸ hcross _ _ hne
  have hfullLinks : (base ++ [last]).IsChain (fun L R =>
      ∀ a ∈ L.getLast?, ∀ b ∈ R.head?, G.Adj a b) := by
    apply hlinks.append (by simp)
    intro L hL R hR a ha b hb
    have hLm := List.mem_of_mem_getLast? hL
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hLm
    have hR' : last = R := by simpa using hR
    subst R
    have ha' : Sum.inl (i + (2 : Fin k)) = a := by simpa [block] using ha
    have hb' : Sum.inr none = b := by simpa [last] using hb
    exact ha' ▸ hb' ▸ hfree _
  have hfullDis : (base ++ [last]).Pairwise List.Disjoint := by
    refine List.pairwise_append.mpr ⟨hpair,by simp,?_⟩
    intro L hL R hR
    have hR' : R = last := by simpa using hR
    subst R
    exact hlastDisjoint L hL
  have hcover (x : Fin k ⊕ Option (Fin k)) : ∃ L ∈ base ++ [last], x ∈ L := by
    cases x with
    | inl i =>
      let j := i - (2 : Fin k)
      refine ⟨block j,List.mem_append_left _ (List.mem_map.mpr ⟨j,by simp,rfl⟩),?_⟩
      simp [block,j]
    | inr i =>
      cases i with
      | none => exact ⟨last,by simp,by simp [last]⟩
      | some j =>
        exact ⟨block j,List.mem_append_left _ (List.mem_map.mpr ⟨j,by simp,rfl⟩),by simp [block]⟩
  exact Graph199.hamiltonian_of_ordered_blocks (base ++ [last]) hparts hfullDis hcover hfullLinks

#print axioms hamiltonian
end BipartiteMissingMatching
