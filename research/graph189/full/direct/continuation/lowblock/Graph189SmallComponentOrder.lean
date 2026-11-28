import Graph189DenseExteriorOrder
import Graph189ExteriorPopulation
import Graph189HighExteriorDegree
import Graph189PrescribedBatch

open Finset SimpleGraph
namespace Graph189DenseExteriorOrder
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj] {x y : V}

/-- In an entire exterior component, the omitted neighbors counted by
the two-step estimate are exactly the neighbors in the induced graph. -/
theorem component_internal_degree (p : G.Walk x y) (W : Finset V)
    (outside : ∀ w ∈ W, w ∉ p.support)
    (boundary : ∀ w ∈ W, ∀ v, G.Adj w v → v ∉ W → v ∈ p.support)
    (a : W) : (G.induce (W : Set V)).degree a =
      (G.neighborFinset a.val \ p.support.toFinset).card := by
  classical
  have same : (G.neighborFinset a.val).filter (fun v => v ∈ (W : Set V)) =
      G.neighborFinset a.val \ p.support.toFinset := by
    ext v
    simp only [mem_filter,mem_sdiff,List.mem_toFinset,mem_coe]
    constructor
    · intro h
      exact ⟨h.1,outside v h.2⟩
    · intro h
      refine ⟨h.1,?_⟩
      by_contra no
      exact h.2 (boundary a a.property v ((G.mem_neighborFinset _ _).mp h.1) no)
  rw [Graph189ExteriorDegreeCycle.degree_induce_filter,same]

/-- In a deletion with closed degree at least the two-step cap, a
nontrivial exterior component of order at most cap minus three already
forces the full baseline lower bound. The path, contacts, induced
Hamilton paths, and the final order comparison are all in the same graph. -/
theorem baseline_of_small_component (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ q : G.Walk a b, q.IsPath → q.length ≤ p.length)
    (W : Finset V) (nonempty : W.Nonempty) (outside : ∀ w ∈ W, w ∉ p.support)
    (boundary : ∀ w ∈ W, ∀ v, G.Adj w v → v ∉ W → v ∈ p.support)
    (neighbor : ∀ a : W, ∃ b : W, G.Adj a.val b.val)
    {s k : ℕ} (two : 2 ≤ s) (range : 2*s ≤ k) (small : W.card+3 ≤ k)
    (deg : ∀ v, k ≤ G.degree v+1)
    (quota : ∀ v, (univ.filter (fun z => G.dist v z = 2)).card ≤ k)
    (conn : ∀ U : Finset V, U.card < s-1 → (G.induce {v : V | v ∉ U}).Connected) :
    (s+1)*(k-s+2) ≤ Fintype.card V+2 := by
  classical
  let H := G.induce (W : Set V)
  have localdeg (a : W) : k ≤ 2*H.degree a+2 := by
    obtain ⟨b,edge⟩ := neighbor a
    have count := Graph189ExteriorGap.adjacent_ambient_degree_sum p hp longest
      (outside a a.property) (outside b b.property) edge (quota a)
    rw [← component_internal_degree p W outside boundary a] at count
    change k ≤ 2*(G.induce (W : Set V)).degree a+2
    have := deg a
    have := deg b
    omega
  obtain ⟨v,hv⟩ := nonempty
  have bound := H.degree_lt_card_verts (⟨v,hv⟩ : W)
  change H.degree (⟨v,hv⟩ : W) < Fintype.card W at bound
  rw [Fintype.card_coe] at bound
  have mn := localdeg ⟨v,hv⟩
  have half : k ≤ 2*W.card := by omega
  apply order_of_component p hp longest W outside boundary _ two (by omega) (by omega) half deg conn
  intro a b ne
  apply Graph189TerminalLeafClosure.prescribed_of_supergraph (le_top : H ≤ ⊤) _
    (Graph189TerminalLeafClosure.complete_prescribed a b ne)
  intro u v _ _
  change Fintype.card W+1 ≤ H.degree u+H.degree v
  rw [Fintype.card_coe]
  have := localdeg u
  have := localdeg v
  omega

#print axioms baseline_of_small_component
end Graph189DenseExteriorOrder
