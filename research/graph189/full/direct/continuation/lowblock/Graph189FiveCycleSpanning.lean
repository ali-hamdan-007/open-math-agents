import Graph189FiveExteriorData
import Graph189FiveCycleExchange

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189FiveCycleSpanning
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A five-cycle spanning the entire exterior of an ordinary longest
path is impossible in the true minimum-degree-three, degree-six case. -/
theorem excluded (hcG : G.Connected) (degree : G.secondSmallestDegree=6)
    (cap : ∀ v, G.distEven v≤7) (minimum : ∀ v, 3≤G.degree v)
    {a b r : V} (p : G.Walk a b) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (C : G.Walk r r) (hc : C.IsCycle) (five : C.length=5) (off : ∀ v∈C.support,v∉p.support)
    (size : p.support.toFinsetᶜ.card=5) : False := by
  classical
  let E := p.support.toFinsetᶜ
  let W := C.support.toFinset
  have we : W=E := eq_of_subset_of_card_le (fun v hv => mem_compl.mpr fun h =>
    off v (List.mem_toFinset.mp hv) (List.mem_toFinset.mp h)) (by
      have n : W.card=5 := (Graph189SixCycleExtra.cycle_card C hc).trans five
      change E.card=5 at size
      omega)
  have order : Fintype.card V≤25 := by
    obtain ⟨z,sz⟩ := Graph189QuadraticOrder.second_attained (G:=G)
    have quad := Graph189QuadraticOrder.rooted hcG z 6 cap
    rw [sz,degree] at quad
    omega
  have limit (M : Finset (Fin p.support.length)) (three : M.card=3) (f : M↪E)
      (contact : ∀ i : M, G.Adj p.support[i.val.val] (f i).val) : False := by
    let incl : E↪W := ⟨fun u => ⟨u.val,we.symm ▸ u.property⟩,fun _ _ e => Subtype.ext (congrArg (fun t : W => t.val) e)⟩
    have lower := Graph189FiveCycleContacts.triple p hp mx C hc five off M three (f.trans incl) contact
    omega
  obtain ⟨M,two,full,_,clique,short⟩ := Graph189FiveExteriorData.data p hcG degree cap size limit
  obtain ⟨z,high⟩ : ∃ z, ∀ u, u≠z → 6≤G.degree u := by
    by_cases high : ∀ u, 6≤G.degree u
    · exact ⟨a,fun u _ => high u⟩
    push Not at high
    obtain ⟨z,lo⟩ := high
    exact ⟨z,fun u ne => by
      have h := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) u z ne
      omega⟩
  have many : 2≤(E.erase z).card := by
    change E.card=5 at size
    by_cases inE : z∈E
    · rw [card_erase_of_mem inE,size]; decide
    · rw [erase_eq_of_notMem inE,size]; decide
  obtain ⟨x,xx,y,yy,xy⟩ := one_lt_card.mp (show 1<(E.erase z).card by omega)
  obtain ⟨xz,xe⟩ := mem_erase.mp xx
  obtain ⟨yz,ye⟩ := mem_erase.mp yy
  let X : E := ⟨x,xe⟩
  let Y : E := ⟨y,ye⟩
  let H := G.induce (E : Set V)
  have all : H=⊤ := by
    ext u v
    constructor
    · exact fun h => h.ne
    · exact fun h => clique u.property v.property (fun eq => h (Subtype.ext eq))
  obtain ⟨s,hs⟩ : ∃ s : H.Walk X Y, s.IsHamiltonian := by
    rw [all]
    exact Graph189TerminalLeafClosure.complete_prescribed _ _ (fun e => xy (congrArg Subtype.val e))
  let inc := (Embedding.induce (G:=G) (E : Set V)).toHom
  let q := s.map inc
  have qp : q.IsPath := hs.isPath.map Subtype.val_injective
  have qlen : q.support.length=5 := by
    change (s.map inc).support.length=5
    rw [Walk.support_map,List.length_map,hs.length_support,Fintype.card_coe]
    exact size
  have onQ {v : V} (ve : v∈E) : v∈q.support := by
    change v∈(s.map inc).support
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨⟨v,ve⟩,hs.mem_support ⟨v,ve⟩,rfl⟩
  have dis : List.Disjoint q.support p.support := by
    apply List.disjoint_left.mpr
    intro v hv
    change v∈(s.map inc).support at hv
    rw [Walk.support_map] at hv
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hv
    exact fun hit => (mem_compl.mp u.property) (List.mem_toFinset.mpr hit)
  have pop := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at pop
  change p.support.length+E.card=Fintype.card V at pop
  let t : Fin p.support.length := if on : z∈p.support then
    ⟨p.support.idxOf z,List.idxOf_lt_length_iff.mpr on⟩ else ⟨0,by have := p.length_support; omega⟩
  have keep {L : List V} (old : p.support[t.val]∈L) (new : q.support⊆L) : z∈L := by
    by_cases on : z∈p.support
    · simpa [t,on,List.getElem_idxOf] using old
    · exact new (onQ (mem_compl.mpr (fun h => on (List.mem_toFinset.mp h))))
  apply Graph189FiveCycleExchange.impossible p hp t mx q qp dis qlen (by change E.card=5 at size; omega)
    M two (full x xe (high x xz)) (fun i mi => (full y ye (high y yz) i).mpr mi) _ (cap x)
  intro a' b' s' path old new eq c seen u un w wn cu
  have sz := s'.length_support
  have pp := p.length_support
  let F := s'.support.toFinsetᶜ
  have pop' := card_add_card_compl s'.support.toFinset
  rw [List.toFinset_card_of_nodup path.support_nodup] at pop'
  change s'.support.length+F.card=Fintype.card V at pop'
  change E.card=5 at size
  have sf : F.card=5 := by omega
  have max' : ∀ {u v}, ∀ t : G.Walk u v, t.IsPath → t.length≤s'.length := fun t ht => eq ▸ mx t ht
  have away (v : V) (vf : v∈F) : v∉s'.support := fun h => (mem_compl.mp vf) (List.mem_toFinset.mpr h)
  have large (v : V) (vf : v∈F) : 6≤G.degree v := high v (fun e => away _ vf (e ▸ keep old new))
  have quota (v : V) : (univ.filter (fun w => G.dist v w=2)).card≤6 := by
    let D := univ.filter (fun w => G.dist v w=2)
    have inc : insert v D⊆univ.filter (fun w => Even (G.dist v w)) := by
      intro w hw
      rcases mem_insert.mp hw with rfl|h
      · simp
      · exact mem_filter.mpr ⟨mem_univ _,by simp [(mem_filter.mp h).2]⟩
    have bound := card_le_card inc
    rw [card_insert_of_notMem (by simp [D])] at bound
    change D.card+1≤G.distEven v at bound
    exact Nat.le_of_succ_le_succ (bound.trans (cap v))
  let J := G.induce (F : Set V)
  have dense (v : F) : Fintype.card F+1≤2*J.degree v := by
    have half := (high_exterior_half s' path max' (away v.val v.property) (quota v.val) (large _ v.property)
      minimum (fun a b la lb => by
        by_contra ne
        have h := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) a b ne
        omega)).2
    have int : J.degree v=(G.neighborFinset v.val\s'.support.toFinset).card := by
      rw [degree_induce_filter]
      congr 1
      ext w
      simp [F]
    rw [Fintype.card_coe,sf,int]
    have := large _ v.property
    omega
  have bounds (N : Finset (Fin s'.support.length)) (three : N.card=3) (f : N↪F)
      (edges : ∀ i : N, G.Adj s'.support[i.val.val] (f i).val) : False := by
    have n := exterior_hamilton_connected_matching s' path max' F (by omega) away
      (fun i j ne => by
        apply Graph189TerminalLeafClosure.prescribed_of_supergraph (G:=J) le_top _
          (Graph189TerminalLeafClosure.complete_prescribed i j ne)
        intro u v _ _
        have h := dense u
        have h' := dense v
        change Fintype.card F+1≤J.degree u+J.degree v
        omega) N
      (card_pos.mp (by omega)) f edges
    rw [three,sf] at n
    omega
  obtain ⟨M',_,full',_⟩ := Graph189FiveExteriorData.data s' hcG degree cap sf bounds
  obtain ⟨i,hi,val⟩ := List.mem_iff_getElem.mp seen
  let I : Fin s'.support.length := ⟨i,hi⟩
  have eu : u∈F := mem_compl.mpr (fun h => un (List.mem_toFinset.mp h))
  have ew : w∈F := mem_compl.mpr (fun h => wn (List.mem_toFinset.mp h))
  have im := (full' u eu (large u eu) I).mp (by change G.Adj s'.support[i] u; rwa [val])
  have want := (full' w ew (large w ew) I).mpr im
  simpa only [I,val] using want

#print axioms excluded
end Graph189FiveCycleSpanning
