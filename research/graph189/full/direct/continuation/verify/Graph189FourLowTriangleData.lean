import Graph189FourNarrowPorts
import Graph189FourTriangle

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189FourLowTriangle
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}

/-- For a three-vertex exterior with a unique possible low vertex, all high
rows see exactly positions 3 and 7. The path must have eleven vertices. -/
theorem data (p : G.Walk a b) (hp : p.IsPath)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (z : V) (degree : ∀ v, v≠z → 4 ≤ G.degree v)
    (retained : ∀ v, v≠z → v∉p.support → 2 ≤ (G.neighborFinset v \ p.support.toFinset).card)
    (order : Fintype.card V ≤ 14) (size : (p.support.toFinsetᶜ : Finset V).card = 3) :
    let E := (p.support.toFinsetᶜ : Finset V)
    p.support.length=11 ∧
    (∀ u v : E, u≠v → ∃ q : (G.induce (E : Set V)).Walk u v, q.IsHamiltonian) ∧
    ∀ v∈E, v≠z → contactPositions p v={3,7} := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  let H := G.induce (E : Set V)
  change E.card=3 at size
  have out {x : V} (hx : x∈E) : x∉p.support := by simpa [E] using hx
  have completeRow {x : V} (hx : x∈E) (nz : x≠z) :
      G.neighborFinset x \ p.support.toFinset=E.erase x := by
    have sub : G.neighborFinset x \ p.support.toFinset ⊆ E.erase x := by
      intro y hy
      obtain ⟨edge,off⟩ := mem_sdiff.mp hy
      exact mem_erase.mpr ⟨((G.mem_neighborFinset _ _).mp edge).ne.symm,mem_compl.mpr off⟩
    apply eq_of_subset_of_card_le sub
    rw [card_erase_of_mem hx,size]
    exact retained x nz (out hx)
  have links {x y : E} (ne : x≠y) (xz : x.val≠z) : H.Adj x y := by
    have inRow : y.val∈G.neighborFinset x.val \ p.support.toFinset := by
      rw [completeRow x.property xz]
      exact mem_erase.mpr ⟨fun e => ne (Subtype.ext e.symm),y.property⟩
    exact (G.mem_neighborFinset _ _).mp (mem_sdiff.mp inRow).1
  have allAdj {x y : E} (ne : x≠y) : H.Adj x y := by
    by_cases xz : x.val=z
    · exact (links ne.symm (fun yz => ne (Subtype.ext (xz.trans yz.symm)))).symm
    · exact links ne xz
  have eqTop : H=⊤ := by
    ext x y
    exact ⟨fun h => h.ne,fun h => allAdj h⟩
  have routes (x y : E) (ne : x≠y) : ∃ q : H.Walk x y, q.IsHamiltonian := by
    rw [eqTop]
    exact Graph189TerminalLeafClosure.complete_prescribed x y ne
  have other (x : E) : ∃ w : E, w≠x ∧ w.val≠z := by
    by_contra! no
    have sub : E ⊆ {x.val,z} := by
      intro w hw
      by_cases same : w=x.val
      · exact mem_insert.mpr (Or.inl same)
      · exact mem_insert.mpr (Or.inr (mem_singleton.mpr (no ⟨w,hw⟩
          (fun e => same (congrArg Subtype.val e)))))
    have bound := (card_le_card sub).trans card_le_two
    omega
  have markCount (x : E) (xz : x.val≠z) : 2 ≤ (contactPositions p x.val).card := by
    rw [contact_card_neighbors p hp]
    have count := card_sdiff_add_card_inter (G.neighborFinset x.val) p.support.toFinset
    rw [completeRow x.property xz,card_erase_of_mem x.property,size,G.card_neighborFinset_eq_degree] at count
    have := degree x.val xz
    omega
  have total := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at total
  change p.support.length+E.card=Fintype.card V at total
  have route (x y : E) (ne : x≠y) : ExteriorRoute p x.val y.val 3 := by
    obtain ⟨q,hq⟩ := routes x y ne
    have e := route_of_induced_hamilton p E (fun _ hx => out hx) hq
    rwa [size] at e
  have tails (x : E) {i : ℕ} (hi : i∈contactPositions p x.val) :
      3 ≤ i ∧ i+4 ≤ p.support.length := by
    obtain ⟨y,ny,_⟩ := other x
    obtain ⟨q,hq,dis,s⟩ := route x y ny.symm
    obtain ⟨ir,ie⟩ := (mem_contactPositions p x.val i).mp hi
    have e : G.Adj p.support[i] x.val := by simpa only [get_at] using ie
    have rdis : List.Disjoint q.reverse.support p.support := by simpa [Walk.support_reverse] using dis
    have lo := prefix_of_detour p hp maximal ⟨i,ir⟩ q.reverse hq.reverse rdis e.symm
    have up := suffix_of_detour p hp maximal ⟨i,ir⟩ q hq dis e
    rw [Walk.support_reverse,List.length_reverse] at lo
    change q.support.length ≤ i at lo
    change i+1+q.support.length ≤ p.support.length at up
    omega
  have apart (x y : E) (ne : x≠y) {i j : ℕ}
      (hi : i∈contactPositions p x.val) (hj : j∈contactPositions p y.val) (lt : i<j) : i+4 ≤ j := by
    obtain ⟨q,hq,dis,s⟩ := route x y ne
    obtain ⟨ir,ie⟩ := (mem_contactPositions p x.val i).mp hi
    obtain ⟨jr,je⟩ := (mem_contactPositions p y.val j).mp hj
    have bound := interval_of_detour p hp maximal ⟨i,ir⟩ ⟨j,jr⟩ lt q hq dis
      (by simpa only [get_at] using ie) (by simpa only [get_at] using je.symm)
    change i+1+q.support.length ≤ j at bound
    omega
  have highRows (x : E) (xz : x.val≠z) : contactPositions p x.val={3,7} := by
    obtain ⟨y,ne,yz⟩ := other x
    exact (Graph189FourNarrowPorts.two_rows _ _ (markCount x xz) (markCount y yz)
      (fun i hi => by have := tails x hi; omega)
      (fun j hj => by have := tails y hj; omega)
      (by intro i hi j hj
          rcases lt_trichotomy i j with h|h|h
          · exact Or.inr (Or.inl (apart x y ne.symm hi hj h))
          · exact Or.inl h
          · exact Or.inr (Or.inr (apart y x ne hj hi h)))).1
  obtain ⟨w,hw⟩ := card_pos.mp (show 0 < E.card by omega)
  obtain ⟨x,_,xz⟩ := other ⟨w,hw⟩
  have seven := tails x (i:=7) (by rw [highRows x xz]; simp)
  exact ⟨by omega,routes,fun v hv nz => highRows ⟨v,hv⟩ nz⟩

#print axioms data
end Graph189FourLowTriangle
