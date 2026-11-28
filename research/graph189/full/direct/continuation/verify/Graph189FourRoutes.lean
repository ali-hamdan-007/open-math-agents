import Graph189RootedTrace

open Finset SimpleGraph
namespace Graph189FourRoutes
variable {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

omit [DecidableEq W] in
/-- Every root in a graph of minimum degree two starts a path on three vertices. -/
theorem three_from (degrees : ∀ w, 2 ≤ H.degree w) (u : W) :
    ∃ w, ∃ q : H.Walk u w, q.IsPath ∧ 3 ≤ q.support.length := by
  classical
  obtain ⟨v,hv⟩ := card_pos.mp (show 0 < (H.neighborFinset u).card by
    rw [H.card_neighborFinset_eq_degree]; have := degrees u; omega)
  obtain ⟨w,hw,wu⟩ := exists_mem_ne (show 1 < (H.neighborFinset v).card by
    rw [H.card_neighborFinset_eq_degree]; exact degrees v) u
  have uv := (H.mem_neighborFinset u v).mp hv
  have vw := (H.mem_neighborFinset v w).mp hw
  let q : H.Walk u w := Walk.cons uv (Walk.cons vw Walk.nil)
  exact ⟨w,q,Walk.IsPath.mk' (by simp [q,uv.ne,vw.ne,wu.symm]),by simp [q]⟩

/-- In a graph on at most five vertices of minimum degree two, deleting the
edge between any two distinct prescribed vertices leaves them connected.
A path there uses at least three vertices. -/
theorem three_between (size : Fintype.card W ≤ 5) (degrees : ∀ w, 2 ≤ H.degree w) (u v : W) (ne : u≠v) :
    ∃ q : H.Walk u v, q.IsPath ∧ 3 ≤ q.support.length := by
  classical
  let K := H.deleteEdges {s(u,v)}
  let N (r : W) := insert r (H.neighborFinset r)
  have three (r : W) : 3 ≤ (N r).card := by
    rw [show N r=insert r (H.neighborFinset r) from rfl,card_insert_of_notMem (by simp),H.card_neighborFinset_eq_degree]
    have := degrees r
    omega
  have keep {r z : W} (ru : r≠u) (rv : r≠v) (edge : H.Adj r z) : K.Adj r z :=
    SimpleGraph.deleteEdges_adj.mpr ⟨edge,by simp [ru,rv]⟩
  have oneSide {r : W} (ru : r≠u) (rv : r≠v) (z : W) (hz : z∈N r) : K.Reachable r z := by
    rcases mem_insert.mp hz with rfl|on
    · exact Reachable.rfl
    · exact (keep ru rv ((H.mem_neighborFinset _ _).mp on)).reachable
  obtain ⟨c,hc,cv⟩ := exists_mem_ne (show 1 < (H.neighborFinset u).card from degrees u) v
  obtain ⟨d,hd,du⟩ := exists_mem_ne (show 1 < (H.neighborFinset v).card from degrees v) u
  have uc := (H.mem_neighborFinset _ _).mp hc
  have vd := (H.mem_neighborFinset _ _).mp hd
  have uc' := (keep uc.ne.symm cv uc.symm).reachable.symm
  have vd' := (keep du vd.ne.symm vd.symm).reachable.symm
  have reach : K.Reachable u v := by
    by_contra no
    have dis : Disjoint (N c) (N d) := disjoint_left.mpr (by
      intro z h₁ h₂
      exact no ((uc'.trans (oneSide uc.ne.symm cv z h₁)).trans
        (vd'.trans (oneSide du vd.ne.symm z h₂)).symm))
    have count := (N c ∪ N d).card_le_univ
    rw [card_union_of_disjoint dis] at count
    have := three c
    have := three d
    omega
  obtain ⟨q,hq⟩ := reach.exists_isPath
  have zero : q.length≠0 := fun eq => ne (Walk.exists_length_eq_zero_iff.mp ⟨q,eq⟩)
  have one : q.length≠1 := by
    intro eq
    have edge := Walk.adj_of_length_eq_one eq
    simp [K] at edge
  let incl : K ≤ H := deleteEdges_le _
  refine ⟨q.mapLe incl,hq.mapLe incl,?_⟩
  rw [Walk.length_support,Walk.length_mapLe]
  omega

/-- Minimum degree two in a graph of order four yields a spanning path from
any prescribed root, by the verified rooted local Ore criterion. -/
theorem four_from (size : Fintype.card W=4) (degrees : ∀ w, 2 ≤ H.degree w) (u : W) :
    ∃ w, ∃ q : H.Walk u w, q.IsPath ∧ 4 ≤ q.support.length := by
  classical
  have conn : H.Connected := {
    nonempty := ⟨u⟩
    preconnected := by
      intro x y
      by_cases e : x=y
      · exact e ▸ Reachable.refl x
      obtain ⟨q,_,_⟩ := three_between H (by omega) degrees x y e
      exact q.reachable }
  obtain ⟨w,q,hq⟩ := Graph189RootedTrace.rooted_local_ore conn u (by
    intro a b c _ _ _ _ _
    apply (card_le_univ _).trans
    have := degrees a
    have := degrees c
    omega)
  exact ⟨w,q,hq.isPath,by rw [hq.length_support,size]⟩

#print axioms three_between
#print axioms four_from
end Graph189FourRoutes
