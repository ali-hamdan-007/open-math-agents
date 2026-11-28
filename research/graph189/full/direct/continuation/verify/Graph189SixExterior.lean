import Graph189AllHighExterior
import Graph189ProtectedTripleFloor
import Graph189ProtectedUniform
import Graph189TwoMarkExchange

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189SixExterior
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At degree six and order at most nineteen, a nonempty exterior of at most
five high vertices on a longest protected path has exactly two common contacts. -/
theorem data {u v : V} (p : G.Walk u v) (hp : p.IsPath) (t : Fin p.support.length)
    (mx : ∀ {a b}, ∀ q : G.Walk a b, q.IsPath → p.support[t.val]∈q.support → q.length≤p.length)
    (six : G.secondSmallestDegree=6) (order : Fintype.card V≤19)
    (cap : ∀ w, G.distEven w≤G.secondSmallestDegree+1)
    (high : ∀ {w : V}, w∉p.support → G.secondSmallestDegree≤G.degree w)
    (present : (p.support.toFinsetᶜ : Finset V).Nonempty)
    (small : (p.support.toFinsetᶜ : Finset V).card≤5) :
    let E := (p.support.toFinsetᶜ : Finset V)
    E.card=5 ∧ (∀ x y : E, x≠y → ∃ q : (G.induce (E : Set V)).Walk x y, q.IsHamiltonian) ∧
      ∃ M : Finset (Fin p.support.length), M.card=2 ∧
        ∀ w∈E, ∀ i : Fin p.support.length, G.Adj p.support[i.val] w ↔ i∈M := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  let H := G.induce (E : Set V)
  change E.card≤5 at small
  have out (w : V) (hw : w∈E) : w∉p.support := by simpa [E] using hw
  have deg (w : E) : 3≤H.degree w := by
    have d := Graph189AllHighExterior.minimum p hp t mx (by omega) high cap w
    rw [six] at d
    exact d
  obtain ⟨x,hx⟩ := present
  let X : E := ⟨x,hx⟩
  have four : 4≤E.card := by
    have h := H.degree_lt_card_verts X
    change H.degree X<Fintype.card E at h
    rw [Fintype.card_coe] at h
    have := deg X
    omega
  have routes (x y : E) (ne : x≠y) : ∃ q : H.Walk x y, q.IsHamiltonian := by
    apply Graph189TerminalLeafClosure.prescribed_of_supergraph (G:=H) le_top _ (Graph189TerminalLeafClosure.complete_prescribed x y ne)
    intro i j _ _
    have := deg i
    have := deg j
    change Fintype.card E+1≤H.degree i+H.degree j
    rw [Fintype.card_coe]
    omega
  have rows (w : V) (hw : w∈E) := Graph189DenseExteriorOrder.neighbors_on_path p E
    (fun _ _ x _ nx => by simpa [E] using nx) hw
  have five : E.card=5 := by
    by_contra diff
    have bound := Graph189ProtectedTripleFloor.order p hp t mx E out (by omega) routes (by
      intro w hw
      have A := rows w hw
      have B := high (out w hw)
      omega)
    omega
  refine ⟨five,routes,uniform_contacts_of_order p hp t mx E out (by omega) routes 2 (by omega) (by omega) ?_⟩
  intro w hw
  have A := rows w hw
  have B := high (out w hw)
  omega

#print axioms data
end Graph189SixExterior
