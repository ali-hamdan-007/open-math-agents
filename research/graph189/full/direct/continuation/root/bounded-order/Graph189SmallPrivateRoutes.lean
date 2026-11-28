import Graph189MarkedHighEnds
import Graph189DirtyRoutes

open SimpleGraph Finset Graph189DenseSideRoute
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189SmallPrivatePair
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

/-- A common-free side loses at most one incident edge at each vertex.
The degree-three assumption gives two internal neighbors even to its exception.
The prescribed starting set may be the contacts of one or both anchors. -/
theorem from_marks (sides : Graph189CutSides.CutSides G A B S) (pair : S={p,q})
    (free : ∀x∈A,¬(G.Adj x p ∧ G.Adj x q)) (con : (G.induce (A:Set V)).Connected)
    (minimum : 3≤G.minDegree) (P : Finset V) (sub : P⊆A) (non : P.Nonempty)
    (room : A.card<2*(G.secondSmallestDegree-1)+P.card) :
    ∃a∈P, ∃b, ∃w : G.Walk a b,w.IsPath ∧ (∀ v∈w.support,v∈A) ∧
      A.card≤w.support.length+(A.card-(2*G.secondSmallestDegree-2)) := by
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
  have two : 2≤J.degree z' := by
    have lost := Graph189CleanSideRoute.loss sides pair free z'
    have m := minimum.trans (G.minDegree_le_degree z)
    change G.degree z≤J.degree z'+1 at lost
    omega
  have high (v : A) (ne : v≠z') : k-1≤J.degree v := by
    have lost := Graph189CleanSideRoute.loss sides pair free v
    have deg := others v.val v.property (fun e => ne (Subtype.ext e))
    change G.degree v.val≤J.degree v+1 at lost
    omega
  let M := P.subtype (fun v => v∈A)
  have mc : M.card=P.card := by
    change (P.subtype (fun v => v∈A)).card=P.card
    rw [card_subtype,filter_eq_self.mpr sub]
  have zdeg := J.degree_lt_card_verts z'
  change J.degree z'<Fintype.card A at zdeg
  let _ : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a,aM,b,Q,hQ,len⟩ := Graph189MarkedHighEnds.marked con z' two high M
    (card_pos.mp (mc ▸ non.card_pos)) (by change Fintype.card A<2*(k-1)+M.card; rw [Fintype.card_coe,mc]; exact room)
  let f := (Embedding.induce (G:=G) (A:Set V)).toHom
  let r := Q.map f
  refine ⟨f a,show f a∈P from mem_subtype.mp aM,f b,r,hQ.map Subtype.val_injective,?_,?_⟩
  · intro v hv
    rw [show r.support=Q.support.map f from Walk.support_map _ _] at hv
    obtain ⟨v',_,rfl⟩ := List.mem_map.mp hv
    exact v'.property
  · change Fintype.card A≤Q.support.length+(Fintype.card A-2*(k-1)) at len
    rw [Fintype.card_coe] at len
    rw [show r.support=Q.support.map f from Walk.support_map _ _,List.length_map]
    change A.card≤Q.support.length+(A.card-(2*k-2))
    omega

end Graph189SmallPrivatePair
#print axioms Graph189SmallPrivatePair.from_marks
