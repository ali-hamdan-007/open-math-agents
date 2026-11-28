import Graph189ExteriorHalf
import Graph189DenseExteriorOrder
import Graph189ExtraPort
import Graph189ExteriorPopulation
import Graph189PrescribedBatch

open Finset SimpleGraph Graph189ExteriorGap

namespace Graph189FourTriangle
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}

theorem exterior_degree (p : G.Walk a b) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (minimum : ∀ v, 4 ≤ G.degree v)
    (quota : ∀ v, (univ.filter (fun w => G.dist v w = 2)).card ≤ 4)
    (x : (p.support.toFinsetᶜ : Finset V)) :
    2 ≤ (G.induce ((p.support.toFinsetᶜ : Finset V) : Set V)).degree x := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  have outside : x.val ∉ p.support := fun h => (mem_compl.mp x.property) (List.mem_toFinset.mpr h)
  have half := (high_exterior_half p hp longest outside (quota _) (minimum _)
    (fun v => by have := minimum v; omega) (fun u _ hu _ => by have := minimum u; omega)).2
  change 2 ≤ (G.induce (E : Set V)).degree x
  rw [Graph189ExteriorDegreeCycle.degree_induce_filter]
  have same : (G.neighborFinset x.val).filter (fun v => v ∈ (E : Set V)) =
      G.neighborFinset x.val \ p.support.toFinset := by ext v; simp [E]
  rw [same]
  have := minimum x.val
  omega

/-- If a longest path omits three vertices, they can be routed in any prescribed
order and share exactly two path contacts. -/
theorem triangle_contacts (p : G.Walk a b) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (minimum : ∀ v, 4 ≤ G.degree v)
    (quota : ∀ v, (univ.filter (fun w => G.dist v w = 2)).card ≤ 4)
    (order : Fintype.card V ≤ 15) (size : (p.support.toFinsetᶜ : Finset V).card = 3) :
    let E := (p.support.toFinsetᶜ : Finset V)
    (∀ x y : E, x≠y → ∃ q : (G.induce (E : Set V)).Walk x y, q.IsHamiltonian) ∧
      ∃ M : Finset (Fin p.support.length), M.card=2 ∧
        ∀ w∈E, ∀ i : Fin p.support.length, G.Adj p.support[i.val] w ↔ i∈M := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  change E.card=3 at size
  have out (w : V) (hw : w ∈ E) : w ∉ p.support :=
    fun h => (mem_compl.mp hw) (List.mem_toFinset.mpr h)
  let H := G.induce (E : Set V)
  have routes (x y : E) (ne : x≠y) : ∃ q : H.Walk x y, q.IsHamiltonian := by
    apply Graph189TerminalLeafClosure.prescribed_of_supergraph (G:=H) le_top _
      (Graph189TerminalLeafClosure.complete_prescribed x y ne)
    intro u v _ _
    have du := exterior_degree p hp longest minimum quota u
    have dv := exterior_degree p hp longest minimum quota v
    change 2 ≤ H.degree u at du
    change 2 ≤ H.degree v at dv
    change Fintype.card E+1 ≤ H.degree u + H.degree v
    rw [Fintype.card_coe,size]
    omega
  let N (w : V) := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] w)
  let A := E.biUnion N
  have rows (w : V) (hw : w ∈ E) : 2 ≤ (N w).card := by
    have d := Graph189DenseExteriorOrder.neighbors_on_path p E
      (fun _ _ v _ no => by simpa [E] using no) hw
    change G.degree w+1 ≤ E.card+(N w).card at d
    have := minimum w
    omega
  have bound : A.card ≤ 2 := by
    by_contra! extra
    obtain ⟨B,n,f,edge⟩ := Graph189ExteriorAttachment.extra_port p E 2 (by omega) rows extra
    have bd := exterior_hamilton_connected_matching p hp longest E (by omega) out routes B
      (card_pos.mp (by omega)) f edge
    rw [n,size] at bd
    omega
  have sub {w : V} (hw : w∈E) : N w ⊆ A := fun _ hi => mem_biUnion.mpr ⟨w,hw,hi⟩
  have same {w : V} (hw : w∈E) : N w=A := eq_of_subset_of_card_le (sub hw) (bound.trans (rows w hw))
  obtain ⟨w,hw⟩ := card_pos.mp (show 0 < E.card by omega)
  exact ⟨routes,A,le_antisymm bound ((rows w hw).trans (card_le_card (sub hw))),fun v hv i => by
    rw [← same hv]
    simp [N]⟩

#print axioms triangle_contacts
end Graph189FourTriangle
