import Graph189BondyEquality

open Finset SimpleGraph OMA.BondyK

namespace Graph189BondyEquality

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every consecutive anchor gap accepts the entire saturated exterior clique.
Equality in the order bound therefore leaves only this clique and the cycle. -/
theorem cycle_covers_with_exterior {c l d : ℕ} {f : ℕ → V} {H : Finset V} {s : ℕ → ℕ}
    (cycle : Cy G c f) (layout : Layout G c l d f H s)
    (two : 2≤l) (ld : l≤d)
    (order : Fintype.card V = (l+1)*(d-l+2)-1) :
    c+H.card=Fintype.card V := by
  classical
  let anchors := (range l).image (fun j => f (s j))
  let L := H.toList
  let m := H.card
  have size : m+l=d+1 := layout.size
  have positive : 0<m := by omega
  have listLength : L.length=m := length_toList _
  have listNodup : L.Nodup := nodup_toList _
  have listNe : L≠[] := List.length_pos_iff.mp (by omega)
  have off (x : V) (hx : x∈L) (j : ℕ) : f j≠x :=
    layout.outside x (mem_toList.mp hx) j
  have attached {x a : V} (hx : x∈H) (ha : a∈anchors) : G.Adj x a := by
    apply (G.mem_neighborFinset _ _).mp
    rw [layout.neighbors x hx]
    exact mem_union_right _ ha
  have internal {x y : V} (hx : x∈H) (hy : y∈H) (ne : x≠y) : G.Adj x y := by
    apply (G.mem_neighborFinset _ _).mp
    rw [layout.neighbors x hx]
    exact mem_union_left _ (mem_erase.mpr ⟨ne.symm,hy⟩)
  have chain : L.IsChain G.Adj :=
    List.Pairwise.isChain (listNodup.imp_of_mem (fun {_ _} hx hy ne =>
      internal (mem_toList.mp hx) (mem_toList.mp hy) ne))
  have offList : OffL G f L := ⟨listNe,listNodup,chain,off⟩
  have anchor_mem (j : ℕ) (hj : j≤l) : f (s j)∈anchors := by
    by_cases equal : j=l
    · subst j
      rw [layout.period,cycle.per]
      exact mem_image_of_mem _ (mem_range.mpr (by omega))
    · exact mem_image_of_mem _ (mem_range.mpr (by omega))
  have gap (i : ℕ) (hi : i<l) : m+1≤s (i+1)-s i := by
    let j := s (i+1)-s i
    have lt := layout.sorted i (i+1) (by omega) (by omega)
    have left : s 0≤s i := by
      by_cases zero : i=0
      · simp [zero]
      · exact (layout.sorted 0 i (by omega) (by omega)).le
    have right : s (i+1)≤s l := by
      by_cases last : i+1=l
      · simp [last]
      · exact (layout.sorted (i+1) l (by omega) le_rfl).le
    rw [layout.period] at right
    have finish : s i+j=s (i+1) := by dsimp [j]; omega
    have head (x : V) (hx : x∈L.head?) : G.Adj (f (s i)) x :=
      (attached (mem_toList.mp (List.mem_of_mem_head? hx)) (anchor_mem i hi.le)).symm
    have tail (x : V) (hx : x∈L.getLast?) : G.Adj x (f (s i+j)) := by
      rw [finish]
      exact attached (mem_toList.mp (List.mem_of_mem_getLast? hx)) (anchor_mem (i+1) (by omega))
    have bound := R1 cycle offList (b:=s i) (j:=j)
      (by dsimp [j]; omega) (by dsimp [j]; omega) head tail
    rwa [listLength] at bound
  have accumulated : ∀ j, j≤l → s 0+j*(m+1)≤s j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro upper
      have previous := ih (by omega : j≤l)
      have nextGap := gap j (by omega)
      rw [Nat.succ_mul]
      omega
  have arcs := accumulated l le_rfl
  rw [layout.period] at arcs
  have fullNodup : (L++up f 0 c).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨listNodup,nodup_up cycle le_rfl,?_⟩
    intro x hx y hy equal
    obtain ⟨j,_,_,eq⟩ := mem_up.mp hy
    exact off x hx j (eq.trans equal.symm)
  have cardinal := fullNodup.length_le_card
  rw [List.length_append,listLength,up_length] at cardinal
  have sizeRewrite : d-l+2=m+1 := by omega
  rw [sizeRewrite,Nat.add_mul,one_mul] at order
  omega

#print axioms cycle_covers_with_exterior

end Graph189BondyEquality
