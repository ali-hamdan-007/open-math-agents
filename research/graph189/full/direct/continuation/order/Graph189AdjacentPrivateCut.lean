import Graph189ShallowCommonOrder
import Graph189OnePortThreeCut
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
    (sep : S={p,q}) (edge : G.Adj p q) (large : 9≤G.secondSmallestDegree)
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
  apply Graph189OnePortCover.below_four hc cap two large
  suffices pop : Fintype.card V≤3*G.secondSmallestDegree+2 by omega
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

/-- A vertex whose distance to both anchors is the same reaches every
opposite port in exactly one step more. -/
private theorem tied_to_port (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    {x y i : V} (xa : x∈A) (yb : y∈B) (iy : G.Adj i y)
    (same : ∀j∈S, G.dist x j=G.dist x i) : G.dist x y=G.dist x i+1 := by
  obtain ⟨w,len⟩ := (hc x y).exists_walk_length_eq_dist
  obtain ⟨j,sj,hj⟩ := sides.meets xa yb w
  have wt := congrArg Walk.length (Walk.take_spec w hj)
  rw [Walk.length_append] at wt
  have l := G.dist_le (w.takeUntil j hj)
  have r := G.dist_le (w.dropUntil j hj)
  have pos : G.dist j y≠0 := fun h => disjoint_left.mp sides.right_cut yb ((hc.dist_eq_zero_iff.mp h) ▸ sj)
  have upper := hc.dist_triangle (u:=x) (v:=i) (w:=y)
  rw [same j sj] at l
  rw [dist_eq_one_iff_adj.mpr iy] at upper
  omega

/-- A common-free side of any adjacent separating pair suffices, without
restrictions on either side's high nonports. -/
theorem unrestricted (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (sides : Graph189CutSides.CutSides G A B S) (sc : S.card≤G.vertexConnectivity)
    (sep : S={p,q}) (edge : G.Adj p q) (large : 9≤G.secondSmallestDegree)
    (noCommon : ∀a∈A, ¬(G.Adj a p ∧ G.Adj a q)) :
    ∃a b, ∃r : G.Walk a b,r.IsHamiltonian := by
  classical
  let k := G.secondSmallestDegree
  have sz : S.card=2 := by simp [sep,edge.ne]
  have conn : 2≤G.vertexConnectivity := by omega
  have point (v : V) : G.distEven v≤k+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have smaller (T : Finset V) (ht : T.card<S.card) :=
    Graph189CutSides.connected_after_smaller_deletion (G:=G) T (ht.trans_le sc)
  have ps : p∈S := by simp [sep]
  have eq (i : V) (si : i∈S) : i=p ∨ i=q := by simpa [sep] using si
  by_cases every : ∀x∈A, G.dist p x=G.dist q x → ¬Even (G.dist p x) → G.degree x<k
  · obtain ⟨u,ua,up⟩ := (sides.contacts_of_minimum smaller ps).1
    have upper := order hc sides sep edge point ua up (fun uq => noCommon u ua ⟨up,uq⟩) every
    exact Graph189OnePortCover.below_four hc cap conn large (by omega)
  push Not at every
  obtain ⟨x,xa,depth,odd,high⟩ := every
  have uniform (i : V) (si : i∈S) : G.dist x i=G.dist p x := by
    rw [G.dist_comm (u:=x) (v:=i)]
    exact (eq i si).elim (by rintro rfl; rfl) (by rintro rfl; exact depth.symm)
  have np (i : V) (si : i∈S) : ¬G.Adj i x := by
    intro e
    have one := (uniform i si).symm.trans (dist_eq_one_iff_adj.mpr e.symm)
    exact noCommon x xa ⟨(dist_eq_one_iff_adj.mp one).symm,
      (dist_eq_one_iff_adj.mp (depth.symm.trans one)).symm⟩
  let P := B.filter (fun y => ∃i∈S,G.Adj i y)
  have counted : P.filter (fun y => Even (G.dist x y))=P := filter_eq_self.mpr (by
    intro y hy
    obtain ⟨yb,i,si,iy⟩ := mem_filter.mp hy
    rw [tied_to_port hc sides xa yb iy (fun j sj => (uniform j sj).trans (uniform i si).symm),uniform i si]
    rw [Nat.even_iff] at odd ⊢
    omega)
  have support : Graph189PortLabels.support G S x=∅ := eq_empty_iff_forall_notMem.mpr (by
    intro i hi
    obtain ⟨si,xi⟩ := mem_filter.mp hi
    exact np i si xi.symm)
  have budget := Graph189BoundaryDebit.even_quota hc sides smaller point (Y:=P) (filter_subset _ _) xa
  rw [counted,support,card_empty,Nat.add_zero,sz] at budget
  have shallow (b : V) (bb : b∈B) (bh : k≤G.degree b) : ∃i∈S,G.Adj i b := by
    by_contra! bn
    obtain ⟨i,si,ix,_⟩ := Graph189DeepCommonPair.nearest hc sides point
      (x:=x) (y:=b) ⟨xa,high,np⟩ ⟨bb,bh,bn⟩
    have d := uniform i si
    rw [G.dist_comm (u:=x) (v:=i),ix] at d
    exact odd (by rw [←d]; decide)
  by_cases highB : ∃b∈B,k≤G.degree b
  · have upper := Graph189ShallowCommonOrder.few_ports hc sides.swap sz point shallow highB budget
    exact Graph189OnePortCover.below_four hc cap conn large (by omega)
  obtain ⟨b,_,degree⟩ := Graph189ShallowCommonOrder.no_high sides.swap sc sz highB
  exact Graph189DegreeTwoOriginal.traceable hc cap conn b degree (by omega)

#print axioms unrestricted
#print axioms traceable
end Graph189AdjacentPrivateCut
