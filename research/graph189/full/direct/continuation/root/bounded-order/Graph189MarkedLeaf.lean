import Graph189MarkedHighEnds
import Graph189DenseSideRoute

open SimpleGraph Finset
namespace Graph189MarkedHighEnds
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- If the exception is a leaf, remove it and use its unique neighbor as
the new exception. Only the leaf is charged in the short-side case. -/
theorem including_leaf (hc : G.Connected) (z : V) {d u : ℕ} (three : 3≤d) (positive : 1≤G.degree z)
    (high : ∀v,v≠z → d≤G.degree v) (P : Finset V) (marks : 2≤P.card)
    (strong : ∀v,v≠z → v∉P → u≤G.degree v) (room : Fintype.card V<2*u+P.card) :
    ∃x∈P, ∃y, ∃r : G.Walk x y,r.IsPath ∧ Fintype.card V≤r.support.length+max 1 (Fintype.card V-2*d) := by
  classical
  by_cases low : 2≤G.degree z
  · obtain ⟨x,xP,y,r,hr,sz⟩ := marked_using_unmarked hc z low high P (card_pos.mp (by omega))
      (fun a b ha hb am bm => by have := strong a ha am; have := strong b hb bm; omega)
    exact ⟨x,xP,y,r,hr,by omega⟩
  have one : G.degree z=1 := by omega
  obtain ⟨g,zg,only⟩ := degree_eq_one_iff_existsUnique_adj.mp one
  let W := (univ : Finset V).erase z
  let H := G.induce (W:Set V)
  let g' : W := ⟨g,mem_erase.mpr ⟨zg.ne.symm,mem_univ _⟩⟩
  have sz : W.card+1=Fintype.card V := by simpa [W] using card_erase_add_one (mem_univ z)
  have con : H.Connected := by
    let _ : Nonempty W := ⟨g'⟩
    apply SimpleGraph.Connected.mk
    apply hc.preconnected.induce_of_degree_eq_one
    intro x outside
    have eq : x=z := by simpa [W] using outside
    subst x
    intro a ha b hb
    exact (only a ha).trans (only b hb).symm
  have nz (v : W) : v.val≠z := (mem_erase.mp v.property).1
  have same (v : W) (ne : v≠g') : G.degree v.val=H.degree v := by
    rw [Graph189ExteriorDegreeCycle.degree_induce_filter]
    have sub : (G.neighborFinset v.val).filter (fun w => w∈(W:Set V))=G.neighborFinset v.val := filter_eq_self.mpr (by
      intro w hw
      apply mem_erase.mpr
      refine ⟨?_,mem_univ _⟩
      rintro rfl
      exact ne (Subtype.ext (only _ ((G.mem_neighborFinset _ _).mp hw).symm)))
    rw [sub,G.card_neighborFinset_eq_degree]
  have gtwo : 2≤H.degree g' := by
    have h := Graph189DenseSideRoute.retained (G:=G) W {z} (fun _ _ v _ vm => by simpa [W] using vm) g'
    rw [card_singleton] at h
    have hd := high g zg.ne.symm
    change G.degree g≤H.degree g'+1 at h
    omega
  have deg := H.degree_lt_card_verts g'
  change H.degree g'<Fintype.card W at deg
  let _ : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let M := (P.erase z).subtype (fun v => v∈W)
  have mc : M.card=(P.erase z).card := by
    change ((P.erase z).subtype (fun v => v∈W)).card=_
    rw [card_subtype,filter_eq_self.mpr (fun x hx => mem_erase.mpr ⟨(mem_erase.mp hx).1,mem_univ _⟩)]
  have cnt : P.card≤M.card+1 := by
    by_cases here : z∈P
    · have e := card_erase_add_one here
      omega
    · rw [mc,erase_eq_of_notMem here]; omega
  have notMarked (v : W) (no : v∉M) : v.val∉P := fun h => no (mem_subtype.mpr (mem_erase.mpr ⟨nz v,h⟩))
  obtain ⟨a,am,b,Q,hQ,len⟩ := marked_using_unmarked (G:=H) con g' gtwo
    (fun v ne => (high v.val (nz v)).trans_eq (same v ne)) M (card_pos.mp (by omega))
    (fun a b ha hb am bm => by
      have left := (strong a.val (nz a) (notMarked a am)).trans_eq (same a ha)
      have right := (strong b.val (nz b) (notMarked b bm)).trans_eq (same b hb)
      change Fintype.card W<_
      rw [Fintype.card_coe]; omega)
  let f := (Embedding.induce (G:=G) (W:Set V)).toHom
  refine ⟨f a,show f a∈P from (mem_erase.mp (mem_subtype.mp am)).2,f b,Q.map f,hQ.map Subtype.val_injective,?_⟩
  change Fintype.card W≤Q.support.length+(Fintype.card W-2*d) at len
  rw [Fintype.card_coe] at len
  rw [Walk.support_map,List.length_map]
  omega

end Graph189MarkedHighEnds
#print axioms Graph189MarkedHighEnds.including_leaf
