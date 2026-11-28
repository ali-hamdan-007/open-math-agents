import Graph189FourTriangle

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189FiveLowMarks
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}

/-- Four omitted vertices with three internal neighbors at every high
vertex form a tetrahedron. Its high vertices share precisely two contacts. -/
theorem data (p : G.Walk a b) (hp : p.IsPath)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (z : V) (degree : ∀ v, v≠z → 5 ≤ G.degree v)
    (retained : ∀ v, v≠z → v∉p.support → 3 ≤ (G.neighborFinset v \ p.support.toFinset).card)
    (order : Fintype.card V ≤ 19) (size : (p.support.toFinsetᶜ : Finset V).card = 4) :
    let E := (p.support.toFinsetᶜ : Finset V)
    (∀ u v : E, u≠v → ∃ q : (G.induce (E : Set V)).Walk u v, q.IsHamiltonian) ∧
    ∃ M : Finset (Fin p.support.length), M.card=2 ∧
      ∀ v∈E, v≠z → ∀ i : Fin p.support.length, G.Adj p.support[i.val] v ↔ i∈M := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  let H := G.induce (E : Set V)
  change E.card=4 at size
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
  let K := E.erase z
  have ksize : 2 < K.card := by
    by_cases hz : z∈E
    · have cnt := card_erase_add_one hz
      change 2 < (E.erase z).card
      omega
    · simp [K,erase_eq_of_notMem hz,size]
  let N (v : V) := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] v)
  let A := K.biUnion N
  have rows (v : V) (hv : v∈K) : 2 ≤ (N v).card := by
    obtain ⟨vz,vE⟩ := mem_erase.mp hv
    have lower := degree v vz
    have amount := Graph189DenseExteriorOrder.neighbors_on_path p E
      (fun _ _ t _ absent => by simpa [E] using absent) vE
    change G.degree v+1 ≤ E.card+(N v).card at amount
    omega
  have bound : A.card ≤ 2 := by
    by_contra! extra
    obtain ⟨B,n,f,edge⟩ := Graph189ExteriorAttachment.extra_port p K 2 ksize rows extra
    let inc : K ↪ E := ⟨fun w => ⟨w.val,(mem_erase.mp w.property).2⟩,fun _ _ h => Subtype.ext (congrArg (fun w : E => w.val) h)⟩
    have deb := exterior_hamilton_connected_matching p hp maximal E (by omega) (fun _ hw => out hw) routes
      B (card_pos.mp (by omega)) (f.trans inc) (fun i => edge i)
    rw [size,n] at deb
    omega
  have sub (v : V) (hv : v∈K) : N v ⊆ A := fun _ hi => mem_biUnion.mpr ⟨v,hv,hi⟩
  have same (v : V) (hv : v∈K) : N v=A := eq_of_subset_of_card_le (sub v hv) (bound.trans (rows v hv))
  obtain ⟨w,hw⟩ := card_pos.mp (show 0 < K.card by omega)
  refine ⟨routes,A,le_antisymm bound ((rows w hw).trans (card_le_card (sub w hw))),?_⟩
  intro v vE vz i
  rw [←same v (mem_erase.mpr ⟨vz,vE⟩)]
  simp [N]

#print axioms data
end Graph189FiveLowMarks
