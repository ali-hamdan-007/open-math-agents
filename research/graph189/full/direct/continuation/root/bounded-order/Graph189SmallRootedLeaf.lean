import Graph189MarkedLeaf
import Graph189DenseRootedRoute

open SimpleGraph Finset
namespace Graph189MarkedHighEnds
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- For a short side a marked exceptional leaf can itself start the path.
Its unique neighbor starts a Dirac path in the remaining graph. -/
theorem short_marked (hc : G.Connected) (z : V) {d : ℕ} (three : 3≤d) (pos : 1≤G.degree z)
    (high : ∀v,v≠z → d≤G.degree v) (P : Finset V) (non : P.Nonempty)
    (leaf : G.degree z=1 → z∈P) (sz : Fintype.card V+1≤2*d) :
    ∃x∈P, ∃y, ∃r : G.Walk x y,r.IsPath ∧ Fintype.card V≤r.support.length := by
  classical
  by_cases two : 2≤G.degree z
  · obtain ⟨x,xP,y,r,hr,len⟩ := marked hc z two high P non (by omega)
    exact ⟨x,xP,y,r,hr,by omega⟩
  obtain ⟨g,edge⟩ := (G.degree_pos_iff_exists_adj z).mp pos
  let W := (univ:Finset V).erase z
  let H := G.induce (W:Set V)
  let start : W := ⟨g,mem_erase.mpr ⟨edge.ne.symm,mem_univ _⟩⟩
  have count : W.card+1=Fintype.card V := by simpa [W] using card_erase_add_one (mem_univ z)
  have reg (v : W) : d-1≤H.degree v := by
    have h := high v.val (mem_erase.mp v.property).1
    have drop := Graph189DenseSideRoute.retained (G:=G) W {z} (fun _ _ x _ miss => by simpa [W] using miss) v
    rw [card_singleton] at drop
    change G.degree v.val≤H.degree v+1 at drop
    omega
  have fit := H.degree_lt_card_verts start
  change H.degree start<Fintype.card W at fit
  let _ : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by have := reg start; omega)
  obtain ⟨y,q,hq⟩ := Graph189DenseRootedRoute.from_vertex (G:=H) start reg (by change Fintype.card W≤2*(d-1); rw [Fintype.card_coe]; omega)
  let f := (Embedding.induce (G:=G) (W:Set V)).toHom
  let r := q.map f
  have fresh : z∉r.support := by
    rw [show r.support=q.support.map f from Walk.support_map _ _]
    rintro h
    obtain ⟨v,_,eq⟩ := List.mem_map.mp h
    exact (mem_erase.mp v.property).1 eq
  have e : G.Adj z (f start) := edge
  refine ⟨z,leaf (by omega),f y,r.cons e,(Walk.cons_isPath_iff e r).mpr ⟨hq.isPath.map Subtype.val_injective,fresh⟩,?_⟩
  have len := hq.length_support
  change q.support.length=Fintype.card W at len
  rw [Fintype.card_coe] at len
  change Fintype.card V≤r.support.length+1
  rw [show r.support=q.support.map f from Walk.support_map _ _,List.length_map]
  omega

end Graph189MarkedHighEnds
#print axioms Graph189MarkedHighEnds.short_marked
