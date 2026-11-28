module

public import Graph189CutInterface
public import Graph189CutExtract
public import Graph189CutExtreme
public import Graph189CutBounds
public import Graph189CutJoin
import all Graph189CutCore

public section
namespace Graph189CutH1Assembly
open SimpleGraph Finset Graph189CutCore
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- It suffices to construct the rooted path on components of order at most
twice the degree threshold minus one. The saturated size is proved outright. -/
theorem h1_of_small_rooted (hc : G.Connected)
    (hσ : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree)
    (horder : 2 * G.secondSmallestDegree + 3 ≤ Fintype.card V)
    (hcut : ∃ c : V, ¬ (G.induce {v | v ≠ c}).Connected)
    (small : ∀ {c : V} {A : Finset V}, Side G c A →
      A.card ≤ 2 * G.secondSmallestDegree - 1 →
      ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain G.Adj ∧
        ∀ x, x ∈ L ↔ x = c ∨ x ∈ A) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  obtain ⟨c,cc⟩ := hcut
  have htwo := Graph189CutInterface.components_after_cut_eq_two hc hσ horder cc
  obtain ⟨A,B,hA,hB,hAB,hcover,hconnA,hconnB⟩ := Graph189CutExtract.two_connected_sides c htwo
  have roots {S T : Finset V} (hs : Side G c S) (ht : Side G c T) (hd : Disjoint S T)
      (hconn : (G.induce (S : Set V)).Connected) :
      ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain G.Adj ∧
        ∀ x, x ∈ L ↔ x = c ∨ x ∈ S := by
    have hu := Graph189CutBounds.side_card_le_two_k hc hσ hs ht hd
    by_cases heq : S.card = 2 * G.secondSmallestDegree
    · have hlo := (ht.card_bounds hc hσ horder (Graph189CutCore.degree_pair (G := G))).2.1
      exact Graph189CutExtreme.rooted_at_two_k hc hσ hs ht hd hconn heq hlo
    · exact small hs (by omega)
  exact Graph189CutJoin.hamiltonian_of_rooted_sides hAB hcover (roots hA hB hAB hconnA)
    (roots hB hA hAB.symm hconnB)

#print axioms h1_of_small_rooted
end Graph189CutH1Assembly
