import Graph189EndpointPivotCount
import Graph189EndpointShell
import Graph189OrdinaryRotationWindow

open SimpleGraph Finset Graph189ExteriorGap
namespace Graph189SixFullPorts
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Three high full ports in a four-vertex exterior window force any
endpoint of the longest path to have degree at most five in order at most 25. -/
theorem initial {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (W D : Finset V) (size : W.card=4) (rank : 3≤D.card) (sub : D⊆W)
    (off : ∀ w∈W,w∉p.support) (clique : G.IsClique (W : Set V))
    (bound : ∀ u∈D, ∀ v, G.Adj u v → v∉W → v∈p.support)
    (high : ∀ u∈D, 6≤G.degree u) (quota : ∀ v, (univ.filter (fun z => G.dist v z=2)).card≤6)
    (order : Fintype.card V≤25) : G.degree a≤5 := by
  classical
  let H := G.induce (W : Set V)
  have top : H=⊤ := by
    ext u v
    constructor
    · intro e
      exact e.ne
    · intro e
      exact clique u.property v.property (fun eq => e (Subtype.ext eq))
  have path {u v : V} (uw : u∈W) (vw : v∈W) (ne : u≠v) : ExteriorRoute p u v 4 := by
    let X : W := ⟨u,uw⟩
    let Y : W := ⟨v,vw⟩
    obtain ⟨q,hq⟩ : ∃ q : H.Walk X Y, q.IsHamiltonian := by
      rw [top]
      exact Graph189TerminalLeafClosure.complete_prescribed _ _ (fun h => ne (congrArg Subtype.val h))
    simpa only [size] using route_of_induced_hamilton p W off hq
  have tail {u : V} (uw : u∈W) : ∃ v, ExteriorRoute p u v 4 := by
    obtain ⟨v,vw,ne⟩ := exists_mem_ne (show 1<W.card by omega) u
    exact ⟨v,path uw vw ne.symm⟩
  let row (u : V) := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] u)
  have rows (u : V) (du : u∈D) : 3≤(row u).card := by
    let P := (row u).image (fun i => p.support[i.val])
    have inc : insert u (G.neighborFinset u)⊆W∪P := by
      intro v hv
      rcases mem_insert.mp hv with rfl|h
      · exact mem_union_left _ (sub du)
      by_cases vw : v∈W
      · exact mem_union_left _ vw
      have e := (G.mem_neighborFinset _ _).mp h
      obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp (bound u du v e vw)
      exact mem_union_right _ (mem_image.mpr ⟨⟨i,hi⟩,mem_filter.mpr ⟨mem_univ _,by simpa only [eq] using e.symm⟩,eq⟩)
    have h := (card_le_card inc).trans (card_union_le W P)
    rw [card_insert_of_notMem (by simp),G.card_neighborFinset_eq_degree,size] at h
    have pc : P.card≤(row u).card := card_image_le
    have d := high u du
    omega
  have counts (u : V) (hu : u∈D) : 3≤(contactPositions p u).card := by
    have inc : (row u).image Fin.val⊆contactPositions p u := by
      intro i hi
      obtain ⟨t,ht,rfl⟩ := mem_image.mp hi
      exact (mem_contactPositions p u _).mpr ⟨t.isLt,by simpa only [get_at] using (mem_filter.mp ht).2⟩
    have n := card_le_card inc
    rw [card_image_of_injective _ Fin.val_injective] at n
    exact (rows u hu).trans n
  have margins {u : V} (uw : u∈W) {i : ℕ} (iu : i∈contactPositions p u) :
      4≤ i ∧ i+5≤p.support.length := by
    obtain ⟨ir,edge⟩ := (mem_contactPositions p u i).mp iu
    obtain ⟨v,q,hq,out,len⟩ := tail uw
    have e : G.Adj p.support[i] u := by simpa only [get_at] using edge
    have l := prefix_of_detour p hp mx ⟨i,ir⟩ q.reverse hq.reverse
      (by simpa [Walk.support_reverse] using out) e.symm
    have r := suffix_of_detour p hp mx ⟨i,ir⟩ q hq out e
    rw [Walk.support_reverse,List.length_reverse] at l
    change q.support.length≤ i at l
    change i+1+q.support.length≤p.support.length at r
    omega
  have miss {u : V} (ud : u∈D) {i : ℕ} (iu : i∈contactPositions p u) : ¬G.Adj a (p.getVert i) := by
    obtain ⟨v,vd,ne⟩ := exists_mem_ne (show 1<D.card by omega) u
    apply Graph189EndpointShell.no_mark p hp mx (off u (sub ud)) (off v (sub vd))
      (clique (sub ud) (sub vd) ne.symm) _ _ iu
    · have h := quota u
      have := counts u ud
      have := counts v vd
      omega
    · intro j mem
      rcases mem with h|h
      · have m := (margins (sub ud) h).1; omega
      · have m := (margins (sub vd) h).1; omega
  obtain ⟨M,sz,f,edges⟩ := Graph189ExteriorAttachment.marks_of_many_neighbors p D 3 rank rows
  let pos := M.orderEmbOfFin sz
  let mem (i : Fin 3) : M := ⟨pos i,M.orderEmbOfFin_mem sz i⟩
  let leaf (i : Fin 3) := (f (mem i)).val
  have hd (i : Fin 3) : leaf i∈D := (f (mem i)).property
  have contact (i : Fin 3) : G.Adj p.support[(pos i).val] (leaf i) := edges (mem i)
  have mark (i : Fin 3) : (pos i).val∈contactPositions p (leaf i) :=
    (mem_contactPositions _ _ _).mpr ⟨(pos i).isLt,by simpa only [get_at] using contact i⟩
  have spread (i j : Fin 3) (ij : i<j) : (pos i).val+5≤(pos j).val := by
    have diff : leaf i≠leaf j := by
      intro e
      have eq : f (mem i)=f (mem j) := Subtype.ext e
      exact ij.ne (pos.injective (congrArg Subtype.val (f.injective eq)))
    obtain ⟨q,hq,out,len⟩ := path (sub (hd i)) (sub (hd j)) diff
    have w := interval_of_detour p hp mx _ _ (pos.strictMono ij) q hq out (contact i) (contact j).symm
    omega
  have total := card_outside_add_path p hp W off
  have resolve {t : ℕ} (h : t∈({(pos 0).val,(pos 1).val,(pos 2).val} : Finset ℕ)) :
      ∃ i : Fin 3, (pos i).val=t := by
    simp only [mem_insert,mem_singleton] at h
    rcases h with h|h|h
    · exact ⟨0,h.symm⟩
    · exact ⟨1,h.symm⟩
    · exact ⟨2,h.symm⟩
  apply Graph189EndpointPivotCount.degree p hp mx (pos 0).val (pos 1).val (pos 2).val
    (by have := (margins (sub (hd 0)) (mark 0)).1; omega)
    (spread 0 1 (by decide)) (spread 1 2 (by decide)) (margins (sub (hd 2)) (mark 2)).2 (by omega)
  · intro t h
    obtain ⟨i,rfl⟩ := resolve h
    exact miss (hd i) (mark i)
  · intro t h
    obtain ⟨i,rfl⟩ := resolve h
    obtain ⟨v,q,hq,out,len⟩ := tail (sub (hd i))
    exact ⟨leaf i,v,q,hq,out,by simpa only [get_at] using contact i,len⟩

#print axioms initial
end Graph189SixFullPorts
