import Graph189UpstreamBondy
import Mathlib.Order.Interval.Finset.Nat

open SimpleGraph Finset
namespace Graph189FanCycle
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- If a terminal neighbour occurs earlier than a successor of an initial
neighbour mark, the smallest such gap leaves enough of the path to close a
cycle. The disjointness hypothesis is the complementary case to a Hamiltonian
rotation at a single index. -/
theorem crossing_cycle {l : List V} (hl : l ≠ []) (nd : l.Nodup) (ch : l.IsChain G.Adj)
    (S T : Finset ℕ) (sMark : ∀ j ∈ S, j+1 < l.length ∧ G.Adj (l.head hl) (l.getD (j+1) (l.head hl)))
    (tMark : ∀ i ∈ T, i+1 < l.length ∧ G.Adj (l.getD i (l.head hl)) (l.getLast hl))
    (apart : Disjoint S T) (cross : ∃ i ∈ T, ∃ j ∈ S, i < j) (size : 3 ≤ S.card+T.card) :
    ∃ a, ∃ Q : G.Walk a a, Q.IsCycle ∧ S.card + T.card ≤ Q.length := by
  classical
  let Good := fun d => ∃ i ∈ T, ∃ j ∈ S, i < j ∧ j-i = d
  obtain ⟨i₀,iT₀,j₀,jS₀,lt₀⟩ := cross
  have yes : ∃ d, Good d := ⟨_,i₀,iT₀,j₀,jS₀,lt₀,rfl⟩
  obtain ⟨i,iT,j,jS,ij,gap⟩ := Nat.find_spec yes
  have least (a : ℕ) (aT : a ∈ T) (b : ℕ) (bS : b ∈ S) (ab : a < b) : j-i ≤ b-a := by
    rw [gap]; exact Nat.find_min' yes (show Good (b-a) from ⟨a,aT,b,bS,ab,rfl⟩)
  obtain ⟨jl,xj⟩ := sMark j jS
  obtain ⟨il,iy⟩ := tMark i iT
  have covered : S ∪ T ⊆ range (i+1) ∪ Ico j (l.length-1) := by
    intro a ha
    by_cases ai : a ≤ i
    · exact mem_union_left _ (mem_range.mpr (by omega))
    apply mem_union_right
    rcases mem_union.mp ha with aS|aT
    · have lower := least i iT a aS (by omega)
      have upper := (sMark a aS).1
      exact mem_Ico.mpr ⟨by omega,by omega⟩
    · have upper := (tMark a aT).1
      have ja : j ≤ a := by
        by_contra! aj
        have lower := least a aT j jS aj
        omega
      exact mem_Ico.mpr ⟨ja,by omega⟩
  have cnt := (card_le_card covered).trans (card_union_le _ _)
  rw [card_union_of_disjoint apart,card_range,Nat.card_Ico] at cnt
  let A := l.take (i+1)
  let B := l.drop (j+1)
  let c := A ++ B.reverse
  have len : c.length = i+1+(l.length-(j+1)) := by simp [c,A,B,List.length_take_of_le (by omega : i+1≤l.length)]
  have dis : A.Disjoint B.reverse := by
    have nd' : (A ++ l.drop (i+1)).Nodup := by simpa [A] using nd
    intro a ha hb
    exact nd'.disjoint ha ((List.drop_sublist_drop_left l (by omega : i+1≤j+1)).subset (List.mem_reverse.mp hb))
  have ndc : c.Nodup := (nd.sublist (List.take_sublist _ _)).append
    (List.nodup_reverse.mpr (nd.sublist (List.drop_sublist _ _))) dis
  have e1 : A.getLast? = some (l.getD i (l.head hl)) := by
    rw [show A = l.take (i+1) from rfl,List.getLast?_take,List.getD_eq_getElem _ _ (by omega)]
    simp [List.getElem?_eq_getElem (by omega : i<l.length)]
  have e2 : B.reverse.head? = some (l.getLast hl) := by
    rw [List.head?_reverse,show B = l.drop (j+1) from rfl,List.getLast?_drop,if_neg (by omega),List.getLast?_eq_some_getLast hl]
  have e3 : c.getLast? = some (l.getD (j+1) (l.head hl)) := by
    rw [show c = A ++ B.reverse from rfl,List.getLast?_append,List.getLast?_reverse,show B = l.drop (j+1) from rfl,List.head?_drop,
      List.getElem?_eq_getElem jl,List.getD_eq_getElem _ _ jl]
    rfl
  have e4 : c.head? = some (l.head hl) := by simp [c,A,List.head?_append,List.head?_take,List.head?_eq_some_head hl]
  have cyc : OMA.BondyK.CL G c := by
    refine ⟨List.isChain_append.mpr ⟨ch.take _,List.isChain_reverse.mpr ((ch.drop _).imp fun _ _ h => h.symm),?_⟩,?_⟩
    · intro a ha b hb
      exact (Option.some.inj (e1.symm.trans ha)) ▸ (Option.some.inj (e2.symm.trans hb)) ▸ iy
    · intro a ha b hb
      exact (Option.some.inj (e3.symm.trans ha)) ▸ (Option.some.inj (e4.symm.trans hb)) ▸ xj.symm
  have bound : S.card+T.card ≤ c.length := by omega
  obtain ⟨a,Q,hQ,eq⟩ := OMA.BondyK.cycle_of_CL c ndc cyc (size.trans bound)
  exact ⟨a,Q,hQ,bound.trans_eq eq.symm⟩

end Graph189FanCycle
#print axioms Graph189FanCycle.crossing_cycle
