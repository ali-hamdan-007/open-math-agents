import Graph189PrivateRepresentativeBound
import Graph189EdgeOrder
import Graph189MinimumCutOrder

open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189CleanSideCounts
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B S : Finset V} {p q : V}

/-- In the paper's common-free clean side, each high vertex has one
anchor at distance two, and a high nonport has both there. -/
structure Clean (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (p q : V) : Prop where
  private_ports : ∀x∈A, ¬(G.Adj x p ∧ G.Adj x q)
  at_two : ∀x∈A, G.secondSmallestDegree≤G.degree x → G.dist p x=2 ∨ G.dist q x=2
  nonport : ∀x∈A, G.secondSmallestDegree≤G.degree x → G.dist p x≠1 → G.dist q x≠1 →
    G.dist p x=2 ∧ G.dist q x=2

omit [Nontrivial V] in
private theorem shell (cap : ∀v,G.distEven v≤G.secondSmallestDegree+1)
    (sides : Graph189CutSides.CutSides G A B S) {i : V} (is_ : i∈S) :
    (A.filter (fun x => G.dist i x=2)).card+(B.filter (fun x => G.dist i x=2)).card≤G.secondSmallestDegree := by
  classical
  have dis := sides.apart.mono (filter_subset (fun x => G.dist i x=2) A)
    (filter_subset (fun x => G.dist i x=2) B)
  rw [←card_union_of_disjoint dis,←filter_union]
  have quota := Graph189TwofoldCover.outside_quota cap (A∪B) (u:=i) (fun h =>
    (mem_union.mp h).elim (fun a => Finset.disjoint_left.mp sides.left_cut a is_)
      (fun b => Finset.disjoint_left.mp sides.right_cut b is_))
  apply le_trans (card_le_card ?_) quota
  intro x hx
  exact mem_filter.mpr ⟨(mem_filter.mp hx).1,by rw [(mem_filter.mp hx).2]; decide⟩

private theorem other_weight (a b : ℕ) (ha : 1≤a) (hb : 1≤b) :
    (if a≠1 ∧ b≠1 then 1 else 0)+(if a=2 ∧ b=2 then 1 else 0) ≤
      (if a=2 then 1 else 0)+(if b=2 then 1 else 0)+(if 3≤a ∧ 3≤b then 1 else 0) := by
  split_ifs <;> omega

/-- The first counting inequality in 'Two deep sides without common ports'.
The side A contains the clean representatives. All cardinalities are
measured on the original graph, including the possible exceptional vertex. -/
theorem anchors (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (pair : S={p,q}) (cap : ∀v,G.distEven v≤G.secondSmallestDegree+1) (clean : Clean G A p q) :
    (A.filter (fun x => G.secondSmallestDegree≤G.degree x)).card+
    (A.filter (fun x => G.secondSmallestDegree≤G.degree x ∧ G.dist p x≠1 ∧ G.dist q x≠1)).card+
    (B.filter (fun x => G.dist p x≠1 ∧ G.dist q x≠1)).card+
    (B.filter (fun x => G.dist p x=2 ∧ G.dist q x=2)).card ≤
    2*G.secondSmallestDegree+(B.filter (fun x => 3≤G.dist p x ∧ 3≤G.dist q x)).card := by
  classical
  have ps : p∈S := by simp [pair]
  have qs : q∈S := by simp [pair]
  have left (x : V) (ax : x∈A) :
      (if G.secondSmallestDegree≤G.degree x then 1 else 0)+
      (if G.secondSmallestDegree≤G.degree x ∧ G.dist p x≠1 ∧ G.dist q x≠1 then 1 else 0) ≤
      (if G.dist p x=2 then 1 else 0)+(if G.dist q x=2 then 1 else 0) := by
    by_cases high : G.secondSmallestDegree≤G.degree x
    · have atTwo := clean.at_two x ax high
      have both := clean.nonport x ax high
      split_ifs <;> omega
    · simp [high]
  have pos (i : V) (si : i∈S) (y : V) (yb : y∈B) : 1≤G.dist i y := by
    have ne : G.dist i y≠0 := fun eq => Finset.disjoint_left.mp sides.right_cut yb
      ((hc.dist_eq_zero_iff.mp eq) ▸ si)
    omega
  have right (x : V) (bx : x∈B) := other_weight _ _ (pos p ps x bx) (pos q qs x bx)
  have X := Finset.sum_le_sum left
  have Y := Finset.sum_le_sum right
  simp only [Finset.sum_add_distrib,Finset.sum_boole,Nat.cast_id] at X Y
  have P := shell cap sides ps
  have Q := shell cap sides qs
  omega

/-- In the large-order branch every edge belongs to a triangle. The edge
order inequality applies at a high endpoint of the actual edge. -/
theorem edge_triangle (hc : G.Connected) (cap : ∀v,G.distEven v≤G.secondSmallestDegree+1)
    (big : 3*G.secondSmallestDegree+2<Fintype.card V) {x y : V} (xy : G.Adj x y) :
    ∃z,G.Adj x z ∧ G.Adj y z := by
  classical
  by_contra absent
  have empty {a b : V} (no : ¬∃z,G.Adj a z ∧ G.Adj b z) :
      G.neighborFinset a∩G.neighborFinset b=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z mem
    exact no ⟨z,(G.mem_neighborFinset _ _).mp (mem_inter.mp mem).1,
      (G.mem_neighborFinset _ _).mp (mem_inter.mp mem).2⟩
  have deny {a b : V} (edge : G.Adj a b) (high : G.secondSmallestDegree≤G.degree b)
      (no : ¬∃z,G.Adj a z ∧ G.Adj b z) : False := by
    have order := Graph189EdgeOrder.edge_order hc edge cap
    rw [empty no,card_empty] at order
    simp only [Nat.add_zero] at order
    have product := Nat.mul_le_mul_left G.secondSmallestDegree
      (show G.secondSmallestDegree+1-G.degree b≤1 by omega)
    omega
  rcases degree_pair (G:=G) x y xy.ne with h|h
  · exact deny xy.symm h (fun ⟨z,yz,xz⟩ => absent ⟨z,xz,yz⟩)
  · exact deny xy h absent

/-- A clean side of a minimum separating pair has the two private
representatives required by the bound, even when it contains the low vertex. -/
theorem representatives (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (pair : S={p,q}) (ne : p≠q) (sc : S.card≤G.vertexConnectivity)
    (cap : ∀v,G.distEven v≤G.secondSmallestDegree+1) (big : 3*G.secondSmallestDegree+2<Fintype.card V)
    (clean : Clean G A p q) :
    (∃ u∈A, G.dist u p=1 ∧ G.dist u q=2) ∧ (∃ v∈A,G.dist v p=2 ∧ G.dist v q=1) := by
  classical
  have ps : p∈S := by simp [pair]
  have qs : q∈S := by simp [pair]
  have contact (i : V) (si : i∈S) : ∃ u∈A, G.secondSmallestDegree≤G.degree u ∧ G.Adj u i := by
    obtain ⟨⟨x,xa,xi⟩,_⟩ := sides.contacts_of_minimum (fun T h =>
      Graph189CutSides.connected_after_smaller_deletion (G:=G) T (h.trans_le sc)) si
    obtain ⟨z,xz,iz⟩ := edge_triangle hc cap big xi
    have za : z∈A := by
      rcases sides.cover z with za|zb|zs
      · exact za
      · exact False.elim (sides.no_cross _ xa _ zb xz)
      · have zi : z≠i := iz.ne.symm
        have one : i=p ∨ i=q := by simpa [pair] using si
        have two : z=p ∨ z=q := by simpa [pair] using zs
        rcases one with ip|iq <;> rcases two with zp|zq
        · exact False.elim (zi (zp.trans ip.symm))
        · exact False.elim (clean.private_ports _ xa ⟨ip ▸ xi,zq ▸ xz⟩)
        · exact False.elim (clean.private_ports _ xa ⟨zp ▸ xz,iq ▸ xi⟩)
        · exact False.elim (zi (zq.trans iq.symm))
    rcases degree_pair (G:=G) x z xz.ne with h|h
    · exact ⟨x,xa,h,xi⟩
    · exact ⟨z,za,h,iz.symm⟩
  obtain ⟨u,ua,uh,up⟩ := contact p ps
  obtain ⟨v,va,vh,vq⟩ := contact q qs
  have U := clean.at_two u ua uh
  have W := clean.at_two v va vh
  rw [dist_eq_one_iff_adj.mpr up.symm] at U
  rw [dist_eq_one_iff_adj.mpr vq.symm] at W
  exact ⟨⟨u,ua,dist_eq_one_iff_adj.mpr up,(G.dist_comm (u:=u) (v:=q)).trans (U.resolve_left (by decide))⟩,
    ⟨v,va,(G.dist_comm (u:=v) (v:=p)).trans (W.resolve_right (by decide)),dist_eq_one_iff_adj.mpr vq⟩⟩

#print axioms anchors
#print axioms representatives
end Graph189CleanSideCounts
