import Graph189AdjacentTieOrder
import Graph189DegreeTwoOriginal

open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189AdjacentPrivateCut
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

/-- A common-free side has no high odd tie whenever the opposite side
contains a high nonport. A common-free side whose high vertices are
already ports has the same conclusion. -/
theorem traceable (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (sides : Graph189CutSides.CutSides G A B S) (sc : S.card≤G.vertexConnectivity)
    (sep : S={p,q}) (edge : G.Adj p q) (large : 12≤G.secondSmallestDegree)
    (noCommon : ∀a∈A, ¬(G.Adj a p ∧ G.Adj a q))
    (covered : (∀a∈A, G.secondSmallestDegree≤G.degree a → ∃i∈S,G.Adj a i) ∨
      ∃b∈B,G.secondSmallestDegree≤G.degree b ∧ ∀i∈S,¬G.Adj i b) :
    ∃a b, ∃r : G.Walk a b,r.IsHamiltonian := by
  classical
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have ps : p∈S := by simp [sep]
  have eq (a : V) (as_ : a∈S) : a=p ∨ a=q := by simpa [sep] using as_
  obtain ⟨u,ua,up⟩ := (sides.contacts_of_minimum (fun T h =>
    Graph189CutSides.connected_after_smaller_deletion T (h.trans_le sc)) ps).1
  have two : 2≤G.vertexConnectivity := by simpa [sep,edge.ne] using sc
  apply Graph189DegreeTwoOriginal.traceable_moderate hc cap large two
  apply order hc sides sep edge point ua up (fun uq => noCommon u ua ⟨up,uq⟩)
  intro v va depths odd
  by_contra! high
  have notOne : G.dist p v≠1 := by
    intro h
    exact noCommon v va ⟨(dist_eq_one_iff_adj.mp h).symm,(dist_eq_one_iff_adj.mp (depths ▸ h)).symm⟩
  rcases covered with ports|⟨b,bb,bh,bn⟩
  · obtain ⟨i,si,vi⟩ := ports v va high
    rcases eq i si with rfl|rfl
    · exact notOne (dist_eq_one_iff_adj.mpr vi.symm)
    · exact notOne (depths.trans (dist_eq_one_iff_adj.mpr vi.symm))
  · have bound := high_range hc point high bh
    obtain ⟨w,len⟩ := (hc v b).exists_walk_length_eq_dist
    obtain ⟨a,sa,hit⟩ := sides.meets va bb w
    have wt := congrArg Walk.length (Walk.take_spec w hit)
    rw [Walk.length_append] at wt
    have left := G.dist_le (w.takeUntil a hit)
    have right := G.dist_le (w.dropUntil a hit)
    have apos : G.dist a b≠0 := fun h => Finset.disjoint_left.mp sides.right_cut bb ((hc.dist_eq_zero_iff.mp h) ▸ sa)
    have an : G.dist a b≠1 := fun h => bn a sa (dist_eq_one_iff_adj.mp h)
    have same : G.dist v a=G.dist p v := by
      rw [G.dist_comm (u:=v) (v:=a)]
      exact (eq a sa).elim (by rintro rfl; rfl) (by rintro rfl; exact depths.symm)
    rw [Nat.even_iff] at odd
    omega

#print axioms traceable
end Graph189AdjacentPrivateCut
