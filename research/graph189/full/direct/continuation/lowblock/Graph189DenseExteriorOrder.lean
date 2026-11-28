import Graph189ExteriorAttachment
import Graph189BoundaryMatching
import Graph189ExteriorMatching
import Mathlib.Tactic.Linarith

open Finset SimpleGraph
namespace Graph189DenseExteriorOrder
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj] {x y : V}

/-- The exterior component's internal order and its actual path contacts
together bound its original closed degree. This applies equally to
paths constrained to contain a prescribed vertex. -/
theorem neighbors_on_path (p : G.Walk x y) (W : Finset V)
    (boundary : ∀ w ∈ W, ∀ v, G.Adj w v → v ∉ W → v ∈ p.support)
    {w : V} (hw : w ∈ W) :
    G.degree w+1 ≤ W.card+((univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] w)).card := by
  classical
  let R := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] w)
  let P := R.image (fun i => p.support[i.val])
  have sub : insert w (G.neighborFinset w) ⊆ W ∪ P := by
    intro v hv
    rcases mem_insert.mp hv with rfl | h
    · exact mem_union_left _ hw
    have edge := (G.mem_neighborFinset _ _).mp h
    by_cases vw : v ∈ W
    · exact mem_union_left _ vw
    obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp (boundary w hw v edge vw)
    exact mem_union_right _ (mem_image.mpr ⟨⟨i,hi⟩,
      mem_filter.mpr ⟨mem_univ _,by simpa only [eq] using edge.symm⟩,eq⟩)
  have h := (card_le_card sub).trans (card_union_le W P)
  rw [card_insert_of_notMem (by simp),G.card_neighborFinset_eq_degree] at h
  exact h.trans (Nat.add_le_add_left card_image_le _)

/-- The exact structural lower bound for a longest path with a
Hamilton-connected exterior component. G is the graph remaining after
deletion of the universal completion vertex, so its order is n−1. -/
theorem order_of_component (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ q : G.Walk a b, q.IsPath → q.length ≤ p.length)
    (W : Finset V) (outside : ∀ w ∈ W, w ∉ p.support)
    (boundary : ∀ w ∈ W, ∀ v, G.Adj w v → v ∉ W → v ∈ p.support)
    (hc : ∀ a b : W, a≠b → ∃ q : (G.induce (W : Set V)).Walk a b, q.IsHamiltonian)
    {s d : ℕ} (sp : 2 ≤ s) (sd : s ≤ d) (sw : s ≤ W.card) (half : d ≤ 2*W.card)
    (deg : ∀ v, d ≤ G.degree v+1)
    (conn : ∀ U : Finset V, U.card < s-1 → (G.induce {v : V | v ∉ U}).Connected) :
    (s+1)*(d-s+2) ≤ Fintype.card V+2 := by
  classical
  let m := W.card
  have sm : s ≤ m := sw
  have hm : d ≤ 2*m := half
  have size : 1 < W.card := by omega
  have num {j : ℕ} (pos : 0 < j) (h : ∃ marks : Finset (Fin p.support.length),
      marks.card = j ∧ ∃ attach : marks ↪ W, ∀ i : marks,
        G.Adj p.support[i.val.val] (attach i).val) :
      (j+2)*m+j ≤ Fintype.card V := by
    obtain ⟨M,sz,e,edges⟩ := h
    subst j
    exact Graph189ExteriorGap.exterior_hamilton_connected_matching p hp longest W size outside hc
      M (card_pos.mp pos) e edges
  by_cases high : d+1 ≤ m+s
  · have long : s-1 ≤ p.support.length := by
      have inc : insert x (G.neighborFinset x) ⊆ p.support.toFinset := by
        intro v hv
        rcases mem_insert.mp hv with rfl | vx
        · exact List.mem_toFinset.mpr p.start_mem_support
        by_contra mis
        have h : v ∉ p.support := fun h => mis (List.mem_toFinset.mpr h)
        have e := ((G.mem_neighborFinset _ _).mp vx).symm
        have path := (Walk.cons_isPath_iff e p).mpr ⟨hp,h⟩
        have bound := longest (Walk.cons e p) path
        simp at bound
      have h := card_le_card inc
      rw [card_insert_of_notMem (by simp),G.card_neighborFinset_eq_degree,
        List.toFinset_card_of_nodup hp.support_nodup] at h
      have := deg x
      omega
    have h := Graph189ExteriorGap.whole_core_order_of_connectivity p hp longest W outside size
      (fun w hw v hv edge => boundary w hw v edge hv) hc (s:=s-1) (by omega) long (by omega) conn
    change (s-1+2)*m+(s-1) ≤ Fintype.card V at h
    zify [show 1 ≤ s by omega,sd] at h ⊢
    have a : 0 ≤ (m:ℤ)+s-d-1 := by omega
    nlinarith only [h,mul_nonneg a (show 0 ≤ (s:ℤ)+1 by omega)]
  · have rows (w : V) (hw : w ∈ W) :
        d-m ≤ ((univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] w)).card := by
      have b := neighbors_on_path p W boundary hw
      have h := deg w
      change G.degree w+1 ≤ m+_ at b
      omega
    have h := num (by omega : 0 < d-m)
      (Graph189ExteriorAttachment.marks_of_many_neighbors p W (d-m) (by change d-m ≤ m; omega) rows)
    zify [show m ≤ d by omega,sd] at h ⊢
    have a : 0 ≤ (m:ℤ)-s := by omega
    have b : 0 ≤ (d:ℤ)-s+1-m := by omega
    nlinarith only [h,mul_nonneg a b]

#print axioms neighbors_on_path
#print axioms order_of_component
end Graph189DenseExteriorOrder
