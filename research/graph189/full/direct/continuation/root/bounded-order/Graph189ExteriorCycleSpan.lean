import Graph189ThreeExteriorLinks
import Graph189ChosenExterior

open SimpleGraph Finset Graph189TwoExteriorLinks Graph189ExteriorGap Graph189OptimalExterior
namespace Graph189ExteriorLeaf
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The entire exterior component contributes to order even when the three
disjoint links are routed only to a cycle strictly inside it. -/
theorem cycle_span {a b r : V} {p : G.Walk a b} {C : Finset V} {k : ℕ} (h : Chosen p C k)
    (conn : 3≤G.vertexConnectivity) (Z : G.Walk r r) (cycle : Z.IsCycle) (inC : ∀v∈Z.support,v∈C) :
    C.card+2*Z.length+2*((Z.length+1)/2)+5≤Fintype.card V := by
  classical
  let W := Z.support.toFinset
  have outside (v : V) (hw : v∈W) := h.outside _ (inC _ (List.mem_toFinset.mp hw))
  obtain ⟨width,start,join⟩ := cycle_routes Z cycle
  obtain ⟨_,s,hs,sl,_⟩ := start r (List.mem_toFinset.mpr Z.start_mem_support)
  have enough := h.longest s hs
  have ps := p.length_support
  have ss := s.length_support
  have three := cycle.three_le_length
  obtain ⟨A,inj,apart⟩ := arms p h.path W outside 3 conn (by change 3≤Z.support.toFinset.card; omega) (by omega)
  let M := univ.image (fun i : Fin 3 => (A i).mark)
  have number : M.card=3 := by simp [M,card_image_of_injective _ inj]
  let iso := M.orderIsoOfFin number
  let mark := M.orderEmbOfFin number
  have has (j : Fin 3) : ∃i : Fin 3,(A i).mark=mark j := by
    obtain ⟨i,_,e⟩ := mem_image.mp (iso j).property
    exact ⟨i,e⟩
  let idx (i : Fin 3) := (has i).choose
  have eq (i : Fin 3) : (A (idx i)).mark=mark i := (has i).choose_spec
  have lt (i j : Fin 3) (ij : i<j) : (A (idx i)).mark<(A (idx j)).mark := by
    rw [eq,eq]; exact mark.strictMono ij
  have sep (i j : Fin 3) (ij : i<j) : idx i≠idx j := fun e =>
    (lt i j ij).ne (congrArg (fun m => (A m).mark) e)
  obtain ⟨l,g,_⟩ := ordered_positions h.path h.longest outside _ _
    (lt 0 1 (by decide)) (apart _ _ (sep 0 1 (by decide))) start join
  obtain ⟨_,g',suf⟩ := ordered_positions h.path h.longest outside _ _
    (lt 1 2 (by decide)) (apart _ _ (sep 1 2 (by decide))) start join
  have total := card_outside_add_path p h.path C h.outside
  omega

end Graph189ExteriorLeaf
#print axioms Graph189ExteriorLeaf.cycle_span
