import Graph189ExteriorPopulation
import Graph189ExteriorDegree

namespace Graph189ExteriorDegreeCycle
open SimpleGraph Finset Graph189ExteriorGap Graph189UniversalCycle
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

/-- Pointwise version for every edge in the exterior of a longest deletion
path. D can be taken as k−1 when the removed vertex has minimum degree. -/
theorem deletion_exterior_local_degree {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (w : V) {u v : {x : V | x ≠ w}}
    (p : (G.induce {x : V | x ≠ w}).Walk u v) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : (G.induce {x : V | x ≠ w}).Walk u v, r.IsPath → r.length ≤ p.length)
    {a b : {x : V | x ≠ w}} (ha : a ∉ p.support) (hb : b ∉ p.support)
    (edge : (G.induce {x : V | x ≠ w}).Adj a b) {k D : ℕ}
    (cap : G.distEven a.val ≤ k+1) (da : D+1 ≤ G.degree a.val) (db : D+1 ≤ G.degree b.val) :
    2*D ≤ k+2*((G.induce {x : V | x ≠ w}).neighborFinset a \ p.support.toFinset).card := by
  classical
  let H := G.induce {x : V | x ≠ w}
  have quota := induced_second_layer (G:=G) {x : V | x ≠ w} a cap
  have contact := cross_contact_degree p hp longest ha hb edge quota
  have split := card_sdiff_add_card_inter (H.neighborFinset a) p.support.toFinset
  rw [H.card_neighborFinset_eq_degree] at split
  have ax := degree_le_deletion_add_one (G:=G) w a
  have by' := degree_le_deletion_add_one (G:=G) w b
  change G.degree a.val ≤ H.degree a+1 at ax
  change G.degree b.val ≤ H.degree b+1 at by'
  change (H.neighborFinset a ∩ p.support.toFinset).card+H.degree b ≤
    k+(H.neighborFinset a \ p.support.toFinset).card at contact
  change 2*D ≤ k+2*(H.neighborFinset a \ p.support.toFinset).card
  omega

/-- An actual outside edge in the deletion yields a cycle with the specified
length. The only metric input is the ambient cap in the original graph. -/
theorem nontrivial_deletion_cycle {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (w : V) {x y : {u : V | u ≠ w}}
    (p : (G.induce {u : V | u ≠ w}).Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : (G.induce {u : V | u ≠ w}).Walk u v, r.IsPath → r.length ≤ p.length)
    (edge : ∃ a ∉ p.support.toFinset, ∃ b ∉ p.support.toFinset, (G.induce {u : V | u ≠ w}).Adj a b)
    {k : ℕ} (cap : ∀ v, G.distEven v ≤ k+1)
    {D d : ℕ} (deg : ∀ v : {u : V | u ≠ w}, D+1 ≤ G.degree v.val)
    (two : 2 ≤ d) (room : k + 2*d ≤ 2*D) :
    ∃ a, ∃ Q : ((G.induce {u : V | u ≠ w}).induce {v | v ∉ p.support.toFinset}).Walk a a,
      Q.IsCycle ∧ d+1 ≤ Q.length := by
  classical
  refine cycle_from_cross_contacts (k:=k) (D:=D) p.support.toFinset two room ?_ edge ?_
  · intro v
    have h := degree_le_deletion_add_one (G:=G) w v
    have := deg v
    omega
  · intro a ha b hb adj
    have quota := induced_second_layer (G:=G) {v : V | v ≠ w} a (cap a.val)
    exact cross_contact_degree p hp longest (fun h => ha (List.mem_toFinset.mpr h))
      (fun h => hb (List.mem_toFinset.mpr h)) adj quota

/-- Repackaging the actual path gap from the original graph into a count of
omitted vertices in its vertex deletion. -/
theorem deletion_gap {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (w : V) {x y : {u : V | u ≠ w}} (p : (G.induce {u : V | u ≠ w}).Walk x y)
    (hp : p.IsPath)
    (gap : ∀ a b, ∀ r : G.Walk a b, r.IsPath → r.support.length + 3 < Fintype.card V) :
    3 ≤ (univ.filter (fun v => v ∉ p.support)).card := by
  classical
  let S := {u : V | u ≠ w}
  let f := (Embedding.induce (G:=G) S).toHom
  have qpath := (Walk.isPath_map_iff_of_injective (p:=p) (f:=f) Subtype.val_injective).mpr hp
  have big := gap _ _ (p.map f) qpath
  rw [Walk.support_map,List.length_map] at big
  have part := card_filter_add_card_filter_not (s:=(univ : Finset S)) (p:=fun v => v ∈ p.support)
  have first : (univ.filter (fun v : S => v ∈ p.support)) = p.support.toFinset := by
    ext t
    simp
  rw [first,List.toFinset_card_of_nodup hp.support_nodup,card_univ] at part
  have sz : Fintype.card S = Fintype.card V - 1 := by
    change Fintype.card {u : V // ¬u = w} = Fintype.card V - 1
    rw [Fintype.card_subtype_compl (fun u : V => u = w),Fintype.card_subtype_eq]
  calc
    3 ≤ ((univ : Finset S).filter (fun t : S => ¬t ∈ p.support)).card := by omega
    _ = _ := by congr 1

/-- A long exterior cycle supplies the literal vertex-counted path appearing in
the large-order Bondy theorem, with no induced-connectivity assumption. -/
theorem path_of_exterior_cycle {V : Type*} {G : SimpleGraph V} {a : V} (C : G.Walk a a)
    (hc : C.IsCycle) : C.dropLast.IsPath ∧ C.dropLast.support.length = C.length := by
  constructor
  · apply Walk.IsPath.mk'
    rw [C.support_dropLast hc.not_nil]
    exact hc.nodup_dropLast_support
  · have drop := C.length_dropLast_add_one hc.not_nil
    rw [C.dropLast.length_support]
    omega

#print axioms deletion_exterior_local_degree
#print axioms nontrivial_deletion_cycle
#print axioms deletion_gap
#print axioms path_of_exterior_cycle
end Graph189ExteriorDegreeCycle
