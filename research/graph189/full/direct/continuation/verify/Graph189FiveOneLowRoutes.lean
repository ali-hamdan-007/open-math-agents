import Graph189FiveOneLowRoots
import Graph189FourExterior

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189FiveOneLowRoutes
variable {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- In a graph on at most seven vertices of minimum degree two
with at most one vertex below three, deleting the
edge between any two distinct prescribed vertices leaves them connected.
A path there uses at least three vertices. -/
theorem three_between (size : Fintype.card W ≤ 7) (degrees : ∀ w, 2 ≤ H.degree w)
    (pair : ∀ a b, a≠b → 3 ≤ H.degree a ∨ 3 ≤ H.degree b) (u v : W) (ne : u≠v) :
    ∃ q : H.Walk u v, q.IsPath ∧ 3 ≤ q.support.length := by
  classical
  let K := H.deleteEdges {s(u,v)}
  let N (r : W) := insert r (H.neighborFinset r)
  have three (r : W) (high : 3 ≤ H.degree r) : 4 ≤ (N r).card := by
    rw [show N r=insert r (H.neighborFinset r) from rfl,card_insert_of_notMem (by simp),H.card_neighborFinset_eq_degree]
    have := degrees r
    omega
  have keep {r z : W} (ru : r≠u) (rv : r≠v) (edge : H.Adj r z) : K.Adj r z :=
    SimpleGraph.deleteEdges_adj.mpr ⟨edge,by simp [ru,rv]⟩
  have oneSide {r : W} (ru : r≠u) (rv : r≠v) (z : W) (hz : z∈N r) : K.Reachable r z := by
    rcases mem_insert.mp hz with rfl|on
    · exact Reachable.rfl
    · exact (keep ru rv ((H.mem_neighborFinset _ _).mp on)).reachable
  have port (s t : W) : ∃ c ∈ H.neighborFinset s, c≠t ∧ 3 ≤ H.degree c := by
    by_cases high : 3 ≤ H.degree s
    · have lb : 2 ≤ ((H.neighborFinset s).erase t).card := by
        by_cases near : t∈H.neighborFinset s
        · have sz := card_erase_add_one near
          rw [H.card_neighborFinset_eq_degree] at sz
          omega
        · rw [erase_eq_of_notMem near,H.card_neighborFinset_eq_degree]
          omega
      obtain ⟨a,ha,b,hb,ab⟩ := one_lt_card.mp lb
      rcases pair a b ab with qa|qb
      · exact ⟨a,(mem_erase.mp ha).2,(mem_erase.mp ha).1,qa⟩
      · exact ⟨b,(mem_erase.mp hb).2,(mem_erase.mp hb).1,qb⟩
    · obtain ⟨a,ha,ne⟩ := exists_mem_ne (show 1 < (H.neighborFinset s).card from degrees s) t
      exact ⟨a,ha,ne,(pair s a ((H.mem_neighborFinset _ _).mp ha).ne).resolve_left high⟩
  obtain ⟨c,hc,cv,dC⟩ := port u v
  obtain ⟨d,hd,du,dD⟩ := port v u
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
    have := three c dC
    have := three d dD
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

#print axioms three_between
end Graph189FiveOneLowRoutes
