import Graph189SmallRootedLeaf
import Graph189DirtyRoutes
import Graph189BalancedSideRoutes

open SimpleGraph Finset Graph189DenseSideRoute
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189SmallPrivatePair
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

private theorem common_degrees (sides : Graph189CutSides.CutSides G A B S) (pair : S={p,q})
    (ne : p≠q) (minimum : 3≤G.minDegree) :
    let J := G.induce (A:Set V)
    let k := G.secondSmallestDegree
    ∃z : A,1≤J.degree z ∧ (∀v : A,v≠z → k-2≤J.degree v) ∧
      (∀v : A,v≠z → ¬G.Adj p v.val → k-1≤J.degree v) ∧ (J.degree z=1 → G.Adj p z.val) := by
  classical
  let k := G.secondSmallestDegree
  let J := G.induce (A:Set V)
  obtain ⟨z,za,others⟩ : ∃z∈A,∀v∈A,v≠z → k≤G.degree v := by
    by_cases all : ∀v∈A,k≤G.degree v
    · obtain ⟨z,za⟩ := sides.left_nonempty
      exact ⟨z,za,fun v va _ => all v va⟩
    push Not at all
    obtain ⟨z,za,low⟩ := all
    exact ⟨z,za,fun v _ ne => (degree_pair (G:=G) v z ne).resolve_right (not_le.mpr low)⟩
  let z' : A := ⟨z,za⟩
  have outer (v : A) (t : V) (vt : G.Adj v.val t) (ta : t∉A) : t∈S := by
    rcases sides.cover t with h|h|h
    · exact (ta h).elim
    · exact (sides.no_cross _ v.property _ h vt).elim
    · exact h
  have sizeS : S.card=2 := by simp [pair,ne]
  have retained (v : A) : G.degree v.val≤J.degree v+2 := by
    have h := Graph189DenseSideRoute.retained (G:=G) A S (fun x xa => outer ⟨x,xa⟩) v
    simpa only [sizeS] using h
  have pos : 1≤J.degree z' := by
    have h := retained z'
    have m := minimum.trans (G.minDegree_le_degree z)
    change G.degree z≤J.degree z'+2 at h
    omega
  have high (v : A) (diff : v≠z') : k-2≤J.degree v := by
    have h := retained v
    have deg := others v.val v.property (fun e => diff (Subtype.ext e))
    omega
  have loss (v : A) (np : ¬G.Adj p v.val) : G.degree v.val≤J.degree v+1 := by
    have h := Graph189BalancedSideRoutes.retained_at A {q} v (fun t e miss => by
      have si := outer v t e miss
      rcases (show t=p ∨ t=q by simpa [pair] using si) with rfl|rfl
      · exact (np e.symm).elim
      · simp)
    simpa only [card_singleton] using h
  change ∃z : A,1≤J.degree z ∧ (∀v : A,v≠z → k-2≤J.degree v) ∧
    (∀v : A,v≠z → ¬G.Adj p v.val → k-1≤J.degree v) ∧ (J.degree z=1 → G.Adj p z.val)
  refine ⟨z',pos,high,?_,?_⟩
  · intro v diff no
    have h := loss v no
    have deg := others v.val v.property (fun e => diff (Subtype.ext e))
    omega
  · intro one
    by_contra no
    have h := loss z' no
    have m := minimum.trans (G.minDegree_le_degree z)
    change G.degree z≤J.degree z'+1 at h
    omega

/-- On a side with common contacts, two incident edges can leave the side.
A vertex missing the chosen anchor loses at most one. The marked leaf theorem
therefore applies to either one anchor's contacts or the union of both sets. -/
theorem common_from_marks_sharp (sides : Graph189CutSides.CutSides G A B S) (pair : S={p,q})
    (ne : p≠q) (con : (G.induce (A:Set V)).Connected)
    (large : 7≤G.secondSmallestDegree) (minimum : 3≤G.minDegree) (P : Finset V) (sub : P⊆A) (two : 2≤P.card)
    (includes : ∀x∈A,G.Adj p x → x∈P)
    (room : A.card<2*(G.secondSmallestDegree-1)+P.card) :
    ∃a∈P, ∃b, ∃w : G.Walk a b,w.IsPath ∧ (∀ v∈w.support,v∈A) ∧
      A.card≤w.support.length+min (max 1 (A.card-(2*G.secondSmallestDegree-4))) (max 2 (A.card-(2*G.secondSmallestDegree-3))) := by
  classical
  let k := G.secondSmallestDegree
  let J := G.induce (A:Set V)
  obtain ⟨z',pos,high,unmarked,_⟩ := common_degrees sides pair ne minimum
  let M := P.subtype (fun v => v∈A)
  have mc : M.card=P.card := by
    change (P.subtype (fun v => v∈A)).card=P.card
    rw [card_subtype,filter_eq_self.mpr sub]
  have strong (v : A) (diff : v≠z') (no : v∉M) : k-1≤J.degree v := by
    have absent : ¬G.Adj p v.val := fun e => no (mem_subtype.mpr (includes _ v.property e))
    exact unmarked v diff absent
  have Mfit := card_le_univ M
  let _ : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have lo : 7≤k := large
  obtain ⟨a,aM,b,Q,hQ,len⟩ := Graph189MarkedHighEnds.leaf_with_bonus (G:=J) con z' (d:=k-2) (u:=k-1) 1 (by decide) (by omega) (by omega)
    pos high M (by omega) strong (by change Fintype.card A<2*(k-1)+M.card; rw [Fintype.card_coe,mc]; exact room)
  let f := (Embedding.induce (G:=G) (A:Set V)).toHom
  let r := Q.map f
  refine ⟨f a,show f a∈P from mem_subtype.mp aM,f b,r,hQ.map Subtype.val_injective,?_,?_⟩
  · intro v hv
    rw [show r.support=Q.support.map f from Walk.support_map _ _] at hv
    obtain ⟨v',_,rfl⟩ := List.mem_map.mp hv
    exact v'.property
  · change Fintype.card A≤Q.support.length+min (max 1 (Fintype.card A-2*(k-2))) (max 2 (Fintype.card A-(2*(k-2)+1))) at len
    rw [Fintype.card_coe] at len
    rw [show r.support=Q.support.map f from Walk.support_map _ _,List.length_map]
    change A.card≤Q.support.length+min (max 1 (A.card-(2*k-4))) (max 2 (A.card-(2*k-3)))
    omega

theorem common_from_marks (sides : Graph189CutSides.CutSides G A B S) (pair : S={p,q})
    (ne : p≠q) (con : (G.induce (A:Set V)).Connected)
    (large : 7≤G.secondSmallestDegree) (minimum : 3≤G.minDegree) (P : Finset V) (sub : P⊆A) (two : 2≤P.card)
    (includes : ∀x∈A,G.Adj p x → x∈P)
    (room : A.card<2*(G.secondSmallestDegree-1)+P.card) :
    ∃a∈P, ∃b, ∃w : G.Walk a b,w.IsPath ∧ (∀ v∈w.support,v∈A) ∧
      A.card≤w.support.length+max 1 (A.card-(2*G.secondSmallestDegree-4)) := by
  obtain ⟨a,ap,b,r,hr,inA,len⟩ := common_from_marks_sharp sides pair ne con large minimum P sub two includes room
  exact ⟨a,ap,b,r,hr,inA,by omega⟩

/-- At a short side any prescribed anchor contact suffices. If the exception
is an internal leaf, degree three forces it to touch both anchors. -/
theorem short_common (sides : Graph189CutSides.CutSides G A B S) (pair : S={p,q}) (ne : p≠q)
    (con : (G.induce (A:Set V)).Connected) (large : 7≤G.secondSmallestDegree) (minimum : 3≤G.minDegree)
    (mark : (A.filter (G.Adj p)).Nonempty) (small : A.card+5≤2*G.secondSmallestDegree) : Route G A p 0 := by
  classical
  let J := G.induce (A:Set V)
  let M := (A.filter (G.Adj p)).subtype (fun v => v∈A)
  obtain ⟨z,pos,high,_,leaf⟩ := common_degrees sides pair ne minimum
  have dz := J.degree_lt_card_verts z
  change J.degree z<Fintype.card A at dz
  change 1≤J.degree z at pos
  let _ : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨v,vm⟩ := mark
  have non : M.Nonempty := ⟨⟨v,(mem_filter.mp vm).1⟩,mem_subtype.mpr vm⟩
  obtain ⟨a,am,b,Q,hQ,len⟩ := Graph189MarkedHighEnds.short_marked (G:=J) con z (by omega : 3≤G.secondSmallestDegree-2)
    pos high M non (fun e => mem_subtype.mpr (mem_filter.mpr ⟨z.property,leaf e⟩))
    (by change Fintype.card A+1≤_; rw [Fintype.card_coe]; omega)
  let f := (Embedding.induce (G:=G) (A:Set V)).toHom
  let r := Q.map f
  refine ⟨f a,f b,r,hQ.map Subtype.val_injective,(mem_filter.mp (mem_subtype.mp am)).2,?_,?_⟩
  · intro v hv
    rw [show r.support=Q.support.map f from Walk.support_map _ _] at hv
    obtain ⟨v',_,rfl⟩ := List.mem_map.mp hv
    exact v'.property
  · change Fintype.card A≤Q.support.length at len
    rw [Fintype.card_coe] at len
    rw [show r.support=Q.support.map f from Walk.support_map _ _,List.length_map]
    omega

end Graph189SmallPrivatePair
#print axioms Graph189SmallPrivatePair.common_from_marks
#print axioms Graph189SmallPrivatePair.common_from_marks_sharp
#print axioms Graph189SmallPrivatePair.short_common
