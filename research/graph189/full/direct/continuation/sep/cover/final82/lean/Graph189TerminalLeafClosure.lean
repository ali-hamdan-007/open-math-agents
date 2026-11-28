import Graph189TraceClosurePublic
import Mathlib.Combinatorics.SimpleGraph.Finite

open SimpleGraph Finset
namespace Graph189TerminalLeafClosure
variable {V : Type*}

def terminalAdj (G : SimpleGraph V) (u v : V) : V ⊕ Bool → V ⊕ Bool → Prop
  | .inl a, .inl b => G.Adj a b
  | .inl a, .inr leaf => a = (if leaf then v else u)
  | .inr leaf, .inl a => a = (if leaf then v else u)
  | .inr _, .inr _ => False

def terminalLeaves (G : SimpleGraph V) (u v : V) : SimpleGraph (V ⊕ Bool) where
  Adj := terminalAdj G u v
  symm := by
    constructor
    intro a b h
    cases a <;> cases b
    · exact G.adj_symm h
    · exact h
    · exact h
    · exact h
  loopless := by
    constructor
    intro a
    cases a with
    | inl a => exact G.irrefl
    | inr l => exact id

instance terminalDecidable (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] (u v : V) :
    DecidableRel (terminalLeaves G u v).Adj := by
  intro a b
  cases a <;> cases b <;> simp only [terminalLeaves,terminalAdj] <;> infer_instance

theorem core_degree_le [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v z : V) : G.degree z ≤ (terminalLeaves G u v).degree (.inl z) := by
  classical
  have inc : (G.neighborFinset z).image (Sum.inl : V → V ⊕ Bool) ⊆
      (terminalLeaves G u v).neighborFinset (.inl z) := by
    intro b hb
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
    simp only [SimpleGraph.mem_neighborFinset] at hc ⊢
    exact hc
  have h := Finset.card_le_card inc
  rw [Finset.card_image_of_injective _ (fun _ _ h => Sum.inl.inj h)] at h
  exact h

theorem terminalLeaves_sup_edge (G : SimpleGraph V) (u v a b : V) :
    terminalLeaves (G ⊔ edge a b) u v =
      terminalLeaves G u v ⊔ edge (.inl a) (.inl b) := by
  ext x y
  cases x <;> cases y <;> simp [terminalLeaves,terminalAdj,SimpleGraph.edge_adj]

/-- The existing spanning-path edge closure, in the graph with two prescribed leaves,
has exactly the degree-sum threshold n+1 in the original graph. -/
theorem leaf_traceable_of_core_edge [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (u v a b : V) (hne : a≠b) (hab : ¬G.Adj a b)
    (degree : Fintype.card V + 1 ≤ G.degree a + G.degree b)
    (path : ∃ x y, ∃ p : (terminalLeaves (G ⊔ edge a b) u v).Walk x y, p.IsHamiltonian) :
    ∃ x y, ∃ p : (terminalLeaves G u v).Walk x y, p.IsHamiltonian := by
  rw [terminalLeaves_sup_edge] at path
  apply Graph189.traceable_of_sup_edge (G := terminalLeaves G u v) (x := .inl a) (y := .inl b)
  · exact fun h => hne (Sum.inl.inj h)
  · exact hab
  · have ha := core_degree_le G u v a
    have hb := core_degree_le G u v b
    simp only [Fintype.card_sum, Fintype.card_bool]
    omega
  · exact path

#print axioms core_degree_le
#print axioms leaf_traceable_of_core_edge
end Graph189TerminalLeafClosure
