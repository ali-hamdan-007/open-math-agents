import Graph189CutSides
import Graph189HighPredecessor
import Graph189R1Metric
import Graph189SeparatorCover

namespace Graph189PrivatePredecessor
open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A B S : Finset V}

variable [DecidableRel G.Adj]

/-- If y has only one nearest label i at distance two and no adjacent label,
some high private B-neighbor of y meets exactly i. No exception for a low first step. -/
theorem high_private [Nontrivial V] (hc : G.Connected)
    (sides : Graph189CutSides.CutSides G A B S)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    {i y : V} (_hi : i ∈ S) (hy : y ∈ B) (iy : G.dist i y = 2)
    (nonport : ∀ j ∈ S, ¬ G.Adj y j)
    (sole : ∀ j ∈ S, G.dist j y = 2 → j = i) :
    ∃ b ∈ B, G.secondSmallestDegree ≤ G.degree b ∧ G.Adj y b ∧ G.Adj i b ∧
      ∀ j ∈ S, G.Adj j b → j = i := by
  classical
  have iyne : i ≠ y := by intro h; simp [h] at iy
  have iyadj : ¬ G.Adj i y := fun g => by have := dist_eq_one_iff_adj.mpr g; omega
  have info {u : V} (_iu : G.Adj i u) (yu : G.Adj y u) :
      u ∈ B ∧ ∀ j ∈ S, G.Adj j u → j = i := by
    have ub : u ∈ B := by
      rcases sides.cover u with ha | hb | hs
      · exact (sides.no_cross u ha y hy yu.symm).elim
      · exact hb
      · exact (nonport u hs yu).elim
    refine ⟨ub,?_⟩
    intro j hj edge
    have jny : j ≠ y := by
      intro eq
      exact disjoint_left.mp sides.right_cut hy (eq ▸ hj)
    have h1 := hc.one_lt_dist_of_ne_of_not_adj jny (fun g => nonport j hj g.symm)
    have h2 := hc.dist_triangle (u := j) (v := u) (w := y)
    rw [dist_eq_one_iff_adj.mpr edge, dist_eq_one_iff_adj.mpr yu.symm] at h2
    exact sole j hj (by omega)
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist i y
  let b := p.getVert 1
  have ib : G.Adj i b := dist_eq_one_iff_adj.mp (by
    simpa [b] using geodesic hc p hp 0 1 (by decide) (by omega))
  have yb : G.Adj y b := Adj.symm (dist_eq_one_iff_adj.mp (by
    have hh := geodesic hc p hp 1 p.length (by omega) le_rfl
    rw [Walk.getVert_length] at hh
    simpa [b,hp,iy] using hh))
  by_cases hb : G.secondSmallestDegree ≤ G.degree b
  · exact ⟨b,(info ib yb).1,hb,yb,ib,(info ib yb).2⟩
  have hh (a : V) (ne : a ≠ b) : G.secondSmallestDegree ≤ G.degree a := by
    rcases degree_pair (G := G) a b ne with h | h
    · exact h
    · exact (hb h).elim
  obtain ⟨u,ne,iu,yu⟩ := Graph189HighPredecessor.another_common iyne iyadj ib.symm yb.symm
    (cap b) (hh i ib.ne) (hh y yb.ne) (lt_of_not_ge hb)
  exact ⟨u,(info iu yu).1,hh u ne,yu,iu,(info iu yu).2⟩

omit [DecidableRel G.Adj] in
/-- A nonport z with a neighboring full A-port permits a two-root even cover
of the entire opposite side, regardless of the degrees of z and a. -/
theorem nonport_full_neighbor (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    {k : ℕ} (cap : ∀ v, G.distEven v ≤ k+1) {a z : V} (ha : a ∈ A) (hz : z ∈ A)
    (az : G.Adj z a) (full : ∀ i ∈ S, G.Adj a i) (missing : ∀ i ∈ S, ¬ G.Adj z i) :
    B.card ≤ 2*k := by
  classical
  let R : Finset V := {a}
  have rc : R.card = 1 := card_singleton a
  have bnd := Graph189SeparatorCover.of_walk_separator hc z B S R
    (disjoint_left.mp sides.apart hz)
    (fun b hb => by have : b = a := mem_singleton.mp hb; exact this ▸ disjoint_left.mp sides.apart ha)
    (fun b hb => by have : b = a := mem_singleton.mp hb; exact this ▸ az)
    (fun b hb path => sides.meets hz hb path) (k := k) (cap := cap)
  rw [rc] at bnd
  apply bnd
  intro i hi
  refine ⟨a,mem_singleton_self a,?_⟩
  have zni : z ≠ i := fun eq => disjoint_left.mp sides.left_cut hz (eq ▸ hi)
  have h1 := hc.one_lt_dist_of_ne_of_not_adj zni (missing i hi)
  have h2 := hc.dist_triangle (u := z) (v := a) (w := i)
  rw [dist_eq_one_iff_adj.mpr az,dist_eq_one_iff_adj.mpr (full i hi)] at h2
  rw [dist_eq_one_iff_adj.mpr (full i hi)]
  omega

#print axioms high_private
#print axioms nonport_full_neighbor
end Graph189PrivatePredecessor
