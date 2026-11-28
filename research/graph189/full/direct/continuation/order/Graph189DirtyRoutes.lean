import Graph189CleanSideCounts
import Graph189CleanSideRoute
import Graph189MarkedException

open Finset SimpleGraph Graph189DenseSideRoute
namespace Graph189DirtyRoutes
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

/-- When every edge has a common neighbor and the two anchor types
are disjoint, each anchor has two distinct contacts in the side. -/
theorem contacts (hc : G.Connected) (cap : ∀v,G.distEven v≤G.secondSmallestDegree+1)
    (sides : Graph189CutSides.CutSides G A B S) (pair : S={p,q})
    (sc : S.card≤G.vertexConnectivity) (big : 3*G.secondSmallestDegree+2<Fintype.card V)
    (free : ∀x∈A,¬(G.Adj x p ∧ G.Adj x q)) : 2≤(A.filter (G.Adj p)).card := by
  classical
  have ps : p∈S := by simp [pair]
  obtain ⟨⟨x,xa,xp⟩,_⟩ := sides.contacts_of_minimum (fun T h =>
    Graph189CutSides.connected_after_smaller_deletion (G:=G) T (h.trans_le sc)) ps
  obtain ⟨v,xv,pv⟩ := Graph189CleanSideCounts.edge_triangle hc cap big xp
  have va : v∈A := by
    rcases sides.cover v with mem|vb|vs
    · exact mem
    · exact (sides.no_cross x xa v vb xv).elim
    · rcases (show v=p ∨ v=q by simpa [pair] using vs) with e|e
      · exact (pv.ne e.symm).elim
      · exact (free x xa ⟨xp,e ▸ xv⟩).elim
  exact one_lt_card.mpr ⟨x,mem_filter.mpr ⟨xa,xp.symm⟩,v,mem_filter.mpr ⟨va,pv⟩,xv.ne⟩

private theorem mark_count (W : Finset V) (pred : V → Prop) [DecidablePred pred] :
    ((W.filter pred).subtype (fun v => v∈W)).card=(W.filter pred).card := by
  rw [card_subtype,filter_eq_self.mpr (fun v h => (mem_filter.mp h).1)]

theorem high {k : ℕ} (large : 10≤k) (sides : Graph189CutSides.CutSides G A B S) (pair : S={p,q})
    (free : ∀x∈A,¬(G.Adj x p ∧ G.Adj x q)) (minimum : ∀x∈A,k≤G.degree x)
    (small : A.card+1≤2*k) (marks : 2≤(A.filter (G.Adj p)).card) : Route G A p 1 := by
  classical
  let H := G.induce (A:Set V)
  let M := (A.filter (G.Adj p)).subtype (fun v => v∈A)
  have count : M.card=(A.filter (G.Adj p)).card := mark_count A (G.Adj p)
  have mcap := card_le_univ M
  rw [Fintype.card_coe] at mcap
  letI : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_coe]; omega)
  have minH (v : A) : k-1≤H.degree v := by
    have loss := Graph189CleanSideRoute.loss sides pair free v
    have enough := minimum v.val v.property
    change G.degree v.val≤H.degree v+1 at loss
    omega
  obtain ⟨x,xM,y,w,hw,len⟩ := Graph189MarkedRotation.from_two_marks M (by omega) minH
    (by change Fintype.card A≤2*(k-1)+1; rw [Fintype.card_coe]; omega)
  let f := (Embedding.induce (G:=G) (A:Set V)).toHom
  let r := w.map f
  have port := (mem_filter.mp (mem_subtype.mp xM)).2
  refine ⟨_,_,r,hw.map Subtype.val_injective,port,?_,?_⟩
  · intro v seen
    rw [show r.support=w.support.map f from Walk.support_map _ _] at seen
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp seen
    exact v.property
  · change Fintype.card A≤w.support.length+1 at len
    rw [Fintype.card_coe] at len
    have eq : r.support.length=w.support.length := by simp [r]
    omega

theorem exceptional {k : ℕ} (large : 10≤k) (sides : Graph189CutSides.CutSides G A B S) (pair : S={p,q})
    (free : ∀x∈A,¬(G.Adj x p ∧ G.Adj x q)) (con : (G.induce (A:Set V)).Connected)
    {z : V} (za : z∈A) (minimum : ∀x∈A,x≠z → k≤G.degree x) (small : A.card+1≤2*k)
    (marksP : 2≤(A.filter (G.Adj p)).card) (marksQ : 2≤(A.filter (G.Adj q)).card) :
    Route G A p 3 ∨ Route G A q 3 := by
  classical
  let H := G.induce (A:Set V)
  let z' : A := ⟨z,za⟩
  let pred (v : V) := G.Adj p v ∨ G.Adj q v
  let M := (A.filter pred).subtype (fun v => v∈A)
  have count : M.card=(A.filter pred).card := mark_count A pred
  have dis : Disjoint (A.filter (G.Adj p)) (A.filter (G.Adj q)) := Finset.disjoint_left.mpr (by
    intro x xp xq
    exact free x (mem_filter.mp xp).1 ⟨(mem_filter.mp xp).2.symm,(mem_filter.mp xq).2.symm⟩)
  have total : A.filter pred=A.filter (G.Adj p) ∪ A.filter (G.Adj q) := by
    ext x
    simp only [mem_filter,mem_union,pred]
    tauto
  rw [total,card_union_of_disjoint dis] at count
  have survive : 3≤(M.erase z').card := by
    by_cases inside : z'∈M
    · have split := card_erase_add_one inside
      omega
    · rw [erase_eq_of_notMem inside]
      omega
  have mcap := card_le_univ M
  rw [Fintype.card_coe] at mcap
  letI : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_coe]; omega)
  have minH (v : A) (diff : v≠z') : k-2+1≤H.degree v := by
    have loss := Graph189CleanSideRoute.loss sides pair free v
    change G.degree v.val≤H.degree v+1 at loss
    have enough := minimum v.val v.property (fun e => diff (Subtype.ext e))
    omega
  obtain ⟨x,xM,y,w,hw,len⟩ := Graph189MarkedException.route con z' M (d:=k-2) (by omega) minH
    (by change Fintype.card A≤2*(k-2)+3; rw [Fintype.card_coe]; omega) survive
  let f := (Embedding.induce (G:=G) (A:Set V)).toHom
  let r := w.map f
  have inside (v : V) (seen : v∈r.support) : v∈A := by
    rw [show r.support=w.support.map f from Walk.support_map _ _] at seen
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp seen
    exact v.property
  change Fintype.card A≤w.support.length+3 at len
  rw [Fintype.card_coe] at len
  have length : A.card≤r.support.length+3 := by simpa [r] using len
  have pm : pred x.val := (mem_filter.mp (mem_subtype.mp xM)).2
  rcases pm with xp|xq
  · exact Or.inl ⟨_,_,r,hw.map Subtype.val_injective,xp,inside,length⟩
  · exact Or.inr ⟨_,_,r,hw.map Subtype.val_injective,xq,inside,length⟩

#print axioms contacts
#print axioms high
#print axioms exceptional
end Graph189DirtyRoutes
