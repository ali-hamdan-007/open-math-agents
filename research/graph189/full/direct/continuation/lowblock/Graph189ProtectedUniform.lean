import Graph189ExtraPort
import Graph189ProtectedSaturation
import Mathlib.Combinatorics.SimpleGraph.Clique

open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b : V}

/-- If an additional matched port would exceed the order of the graph, the
entire Hamilton-connected exterior has exactly the same s contacts. -/
theorem uniform_contacts_of_order (Q : G.Walk a b) (hQ : Q.IsPath)
    (t : Fin Q.support.length)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → Q.support[t.val] ∈ r.support → r.length ≤ Q.length)
    (E : Finset V) (outside : ∀ w ∈ E, w ∉ Q.support) (many : 1 < E.card)
    (routes : ∀ x y : E, x ≠ y → ∃ q : (G.induce (E : Set V)).Walk x y, q.IsHamiltonian)
    (s : ℕ) (small : s < E.card) (upper : Fintype.card V < (s+2)*E.card+(s+1))
    (rows : ∀ v ∈ E, s ≤ ((univ : Finset (Fin Q.support.length)).filter
      (fun i => G.Adj Q.support[i.val] v)).card) :
    ∃ marks : Finset (Fin Q.support.length), marks.card = s ∧
      ∀ w ∈ E, ∀ i : Fin Q.support.length, G.Adj Q.support[i.val] w ↔ i ∈ marks := by
  classical
  let N (w : V) := (univ : Finset (Fin Q.support.length)).filter (fun i => G.Adj Q.support[i.val] w)
  let A := E.biUnion N
  have bound : A.card ≤ s := by
    by_contra! extra
    obtain ⟨marks,number,f,edge⟩ := Graph189ExteriorAttachment.extra_port Q E s small rows extra
    have order := protected_hamilton_connected_matching Q hQ t maximal E many outside routes marks
      (card_pos.mp (by omega)) f edge
    rw [number] at order
    exact (not_lt_of_ge order) upper
  have incl {w : V} (hw : w ∈ E) : N w ⊆ A := fun _ hi => mem_biUnion.mpr ⟨w,hw,hi⟩
  have same {w : V} (hw : w ∈ E) : N w = A :=
    eq_of_subset_of_card_le (incl hw) (bound.trans (rows w hw))
  obtain ⟨w,hw⟩ := card_pos.mp (show 0 < E.card by omega)
  exact ⟨A,le_antisymm bound ((rows w hw).trans (card_le_card (incl hw))),fun v hv i => by
    rw [← same hv]
    simp [N]⟩

/-- The high degree of every omitted vertex forces it to use every other
omitted vertex once its set of possible neighbors has cardinal at most k. -/
theorem exterior_clique_of_common_contacts (Q : G.Walk a b)
    (marks : Finset (Fin Q.support.length)) (k : ℕ)
    (fits : (Q.support.toFinsetᶜ : Finset V).card+marks.card ≤ k+1)
    (high : ∀ w ∈ (Q.support.toFinsetᶜ : Finset V), k ≤ G.degree w)
    (contacts : ∀ w ∈ (Q.support.toFinsetᶜ : Finset V), ∀ i : Fin Q.support.length,
      G.Adj Q.support[i.val] w → i ∈ marks) :
    G.IsClique ((Q.support.toFinsetᶜ : Finset V) : Set V) := by
  classical
  let E := (Q.support.toFinsetᶜ : Finset V)
  let A := marks.image (fun i => Q.support[i.val])
  have small : A.card ≤ marks.card := card_image_le
  intro w hw v hv ne
  change w ∈ E at hw
  change v ∈ E at hv
  let candidates := E.erase w ∪ A
  have included : G.neighborFinset w ⊆ candidates := by
    intro x hx
    have edge := (G.mem_neighborFinset _ _).mp hx
    by_cases h : x ∈ E
    · exact mem_union_left _ (mem_erase.mpr ⟨edge.ne.symm,h⟩)
    have member : x ∈ Q.support := by simpa [E] using h
    obtain ⟨i,hi,value⟩ := List.mem_iff_getElem.mp member
    let pos : Fin Q.support.length := ⟨i,hi⟩
    have marked := contacts w hw pos (by simpa [pos,value] using edge.symm)
    exact mem_union_right _ (mem_image.mpr ⟨pos,marked,value⟩)
  have cap := card_union_le (E.erase w) A
  have erased := card_erase_add_one hw
  have large := high w hw
  rw [←G.card_neighborFinset_eq_degree] at large
  change E.card+marks.card ≤ k+1 at fits
  have all : G.neighborFinset w = candidates :=
    eq_of_subset_of_card_le included (by change candidates.card ≤ _ at cap; omega)
  apply (G.mem_neighborFinset _ _).mp
  rw [all]
  exact mem_union_left _ (mem_erase.mpr ⟨ne.symm,hv⟩)

variable [Nontrivial V]

/-- Every longest path through the low vertex, when its deletion has a
Hamilton path, omits a clique complete to exactly deg(z) marked positions. -/
theorem protected_uniform_clique (hc : G.Connected) (z : V)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (nontrace : ¬ ∃ u v, ∃ r : G.Walk u v, r.IsHamiltonian)
    {x y : {v : V | v ≠ z}} (p : (G.induce {v : V | v ≠ z}).Walk x y) (hp : p.IsHamiltonian)
    (Q : G.Walk a b) (hQ : Q.IsPath) (t : Fin Q.support.length) (eq : Q.support[t.val]=z)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z ∈ r.support → r.length ≤ Q.length)
    (pos : 3 ≤ G.degree z) (ratio : 3*G.degree z < G.secondSmallestDegree) :
    ∃ marks : Finset (Fin Q.support.length), marks.card = G.degree z ∧
      (∀ w ∈ (Q.support.toFinsetᶜ : Finset V), ∀ i : Fin Q.support.length,
        G.Adj Q.support[i.val] w ↔ i ∈ marks) ∧
      G.IsClique ((Q.support.toFinsetᶜ : Finset V) : Set V) := by
  classical
  let E := (Q.support.toFinsetᶜ : Finset V)
  let m := E.card
  let k := G.secondSmallestDegree
  let s := G.degree z
  obtain ⟨count,small,upper,rows⟩ := protected_saturation_data hc z cap nontrace p hp Q hQ t eq maximal pos ratio
  change m=k+1-s at count
  change s < m at small
  change 3 ≤ s at pos
  change 3*s < k at ratio
  have low : G.degree Q.support[t.val] < k := by rw [eq]; change s < k; omega
  have max' : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → Q.support[t.val] ∈ r.support → r.length ≤ Q.length :=
    fun r hr h => maximal r hr (eq ▸ h)
  have outside (w : V) (hw : w ∈ E) : w ∉ Q.support :=
    fun member => (mem_compl.mp hw) (List.mem_toFinset.mpr member)
  have routes := protected_exterior_hamilton_connected Q hQ t max' low cap (by change m+2 ≤ k; omega)
  obtain ⟨marks,card,links⟩ := uniform_contacts_of_order Q hQ t max' E outside (by change 1 < m; omega)
    routes s small upper rows
  refine ⟨marks,card,links,exterior_clique_of_common_contacts Q marks k ?_ ?_ (fun w hw i => (links w hw i).mp)⟩
  · change m+marks.card ≤ k+1
    omega
  · intro w hw
    have ne : w ≠ Q.support[t.val] := fun h => outside w hw (h ▸ List.getElem_mem _)
    exact (degree_pair (G:=G) w _ ne).resolve_right (Nat.not_le.mpr low)

#print axioms protected_uniform_clique
end Graph189ExteriorGap
