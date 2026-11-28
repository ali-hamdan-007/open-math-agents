import Graph189FiveExteriorRoots
import Graph189FourExterior

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189FivePortOrder
variable {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- In a graph on at most seven vertices of minimum degree three, deleting the
edge between any two distinct prescribed vertices leaves them connected.
A path there uses at least three vertices. -/
theorem three_between (size : Fintype.card W ≤ 7) (degrees : ∀ w, 3 ≤ H.degree w) (u v : W) (ne : u≠v) :
    ∃ q : H.Walk u v, q.IsPath ∧ 3 ≤ q.support.length := by
  classical
  let K := H.deleteEdges {s(u,v)}
  let N (r : W) := insert r (H.neighborFinset r)
  have three (r : W) : 4 ≤ (N r).card := by
    rw [show N r=insert r (H.neighborFinset r) from rfl,card_insert_of_notMem (by simp),H.card_neighborFinset_eq_degree]
    have := degrees r
    omega
  have keep {r z : W} (ru : r≠u) (rv : r≠v) (edge : H.Adj r z) : K.Adj r z :=
    SimpleGraph.deleteEdges_adj.mpr ⟨edge,by simp [ru,rv]⟩
  have oneSide {r : W} (ru : r≠u) (rv : r≠v) (z : W) (hz : z∈N r) : K.Reachable r z := by
    rcases mem_insert.mp hz with rfl|on
    · exact Reachable.rfl
    · exact (keep ru rv ((H.mem_neighborFinset _ _).mp on)).reachable
  obtain ⟨c,hc,cv⟩ := exists_mem_ne (show 1 < (H.neighborFinset u).card by have := degrees u; rw [H.card_neighborFinset_eq_degree]; omega) v
  obtain ⟨d,hd,du⟩ := exists_mem_ne (show 1 < (H.neighborFinset v).card by have := degrees v; rw [H.card_neighborFinset_eq_degree]; omega) u
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

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem mapped {W : Finset V} (p : G.Walk a b) (outside : ∀ z∈W, z∉p.support)
    {u v : W} (q : (G.induce (W : Set V)).Walk u v) (hq : q.IsPath) :
    ∃ r : G.Walk u.val v.val, r.IsPath ∧ List.Disjoint r.support p.support ∧ r.support.length=q.support.length := by
  let inc := (Embedding.induce (G:=G) (W : Set V)).toHom
  have ds : List.Disjoint (q.map inc).support p.support := by
    rw [Walk.support_map,List.disjoint_left]
    intro z hz
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hz
    exact outside t.val t.property
  have len : (q.map inc).support.length=q.support.length := by rw [Walk.support_map,List.length_map]
  exact ⟨q.map inc,hq.map Subtype.val_injective,ds,len⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Two rooted exterior tails and a route between two distinct ports give disjoint lower bounds. -/
theorem order (p : G.Walk a b) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (W : Finset V) (outside : ∀ z∈W, z∉p.support)
    {i j : Fin p.support.length} {u v : W}
    (ij : i<j) (left : G.Adj p.support[i.val] u.val) (right : G.Adj p.support[j.val] v.val)
    (l s d : ℕ)
    (leftTail : ∃ w, ∃ q : (G.induce (W : Set V)).Walk u w, q.IsPath ∧ l ≤ q.support.length)
    (rightTail : ∃ w, ∃ q : (G.induce (W : Set V)).Walk v w, q.IsPath ∧ s ≤ q.support.length)
    (inner : ∃ q : (G.induce (W : Set V)).Walk u v, q.IsPath ∧ d ≤ q.support.length) :
    l+s+d+2 ≤ p.support.length := by
  obtain ⟨_,q,hq,l⟩ := leftTail
  obtain ⟨r,hr,dis,len⟩ := mapped p outside q hq
  have rc : List.Disjoint r.reverse.support p.support := by simpa [Walk.support_reverse] using dis
  have f := prefix_of_detour p hp longest i r.reverse hr.reverse rc left.symm
  rw [Walk.support_reverse,List.length_reverse,len] at f
  obtain ⟨_,q',hq',l'⟩ := rightTail
  obtain ⟨r',hr',dis',len'⟩ := mapped p outside q' hq'
  have g := suffix_of_detour p hp longest j r' hr' dis' right
  rw [len'] at g
  obtain ⟨q'',hq'',l''⟩ := inner
  obtain ⟨r'',hr'',dis'',len''⟩ := mapped p outside q'' hq''
  have h := interval_of_detour p hp longest i j ij r'' hr'' dis'' left right.symm
  rw [len''] at h
  omega

#print axioms order
#print axioms three_between
end Graph189FivePortOrder
