import Graph189LinkedExterior

namespace Graph189NativeCycleLinked
open SimpleGraph Finset

theorem of_cycle {V : Type*} [DecidableEq V] {G : SimpleGraph V} {r : V}
    (C : G.Walk r r) (hc : C.IsCycle) {l : ℕ} (size : l+1≤C.length)
    (long : 2*l≤C.length+2) : Graph189LinkedExterior.Linked G l := by
  classical
  let S := C.support.toFinset
  have enough : C.length ≤ S.card := by
    have sub : C.support.tail.toFinset ⊆ S := by
      intro v hv
      exact List.mem_toFinset.mpr (List.mem_of_mem_tail (List.mem_toFinset.mp hv))
    have cmp := card_le_card sub
    rw [List.toFinset_card_of_nodup hc.support_nodup,List.length_tail,C.length_support] at cmp
    omega
  refine ⟨S,size.trans enough,?_⟩
  intro a ha b hb ne
  let R := C.rotate a (List.mem_toFinset.mp ha)
  have rc : R.IsCycle := hc.rotate (List.mem_toFinset.mp ha)
  have on : b∈R.support := (C.mem_support_rotate_iff a _).mpr (List.mem_toFinset.mp hb)
  let L := R.takeUntil b on
  let T := R.dropUntil b on
  have split : L.append T=R := R.take_spec on
  have cyc : (L.append T).IsCycle := split ▸ rc
  have lp : L.IsPath := rc.isPath_takeUntil on
  have tp : T.IsPath := cyc.isPath_of_append_right (L.not_nil_of_ne ne)
  have lengths : L.length+T.length=C.length := by
    rw [← Walk.length_append,split]
    exact C.length_rotate _ _
  have inS (v : V) (hv : v∈R.support) : v∈S :=
    List.mem_toFinset.mpr ((C.mem_support_rotate_iff a _).mp hv)
  by_cases large : l≤L.length+1
  · exact ⟨L,lp,by rwa [L.length_support],fun v hv => inS v (R.support_takeUntil_subset_support on hv)⟩
  · refine ⟨T.reverse,tp.reverse,by rw [Walk.length_support,Walk.length_reverse]; omega,?_⟩
    intro v hv
    exact inS v (R.support_dropUntil_subset_support on (by simpa using hv))

#print axioms of_cycle
end Graph189NativeCycleLinked
