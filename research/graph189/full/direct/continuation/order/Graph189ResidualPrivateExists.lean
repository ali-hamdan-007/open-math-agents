import Graph189ResidualPrivatePort
import Graph189ResidualWindows

namespace Graph189ResidualPrivatePort
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B S : Finset V}

/-- In the residual-singleton case, absent private B contacts on the common
labels imply the sharp upper bound on the opposite high population.
The displayed bound is twice the undivided population. -/
theorem absent_bound (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (C : Finset V) (cs : C ⊆ S) (two : 2 ≤ (S \ C).card)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (contacts : ∀ i ∈ S \ C, ∃ a ∈ A, G.secondSmallestDegree ≤ G.degree a ∧ G.Adj a i)
    (common : ∀ a ∈ A, G.secondSmallestDegree ≤ G.degree a → ∀ i ∈ C, G.Adj a i)
    (single : ∀ a ∈ A, G.secondSmallestDegree ≤ G.degree a →
      (Graph189PortLabels.support G S a \ C).card ≤ 1)
    (absent : ¬ ∃ i ∈ C, ∃ b ∈ B, G.secondSmallestDegree ≤ G.degree b ∧
      S.filter (G.Adj b) = {i}) :
    let X := A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)
    let Y := B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)
    2*Y.card ≤ (2*(S \ C).card+C.card)*G.secondSmallestDegree+X.card+
      (S \ C).card*(C.card+1) := by
  classical
  let Y := B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)
  let Z (i : V) := Y.filter (fun v => G.dist i v = 2)
  have debit := Graph189PrivateQuota.residual_even_windows hc sides C cap contacts single Z
    (fun _ _ _ hy => (mem_filter.mp (mem_filter.mp hy).1).1)
    (fun _ _ _ hy => (mem_filter.mp hy).2)
  have covered := double_cover hc sides C cs two cap contacts common single absent
  change 2*Y.card ≤ _ + ∑ i ∈ S \ C, (Z i).card at covered
  have total := Nat.add_le_add_left debit ((2*(S \ C).card+C.card)*G.secondSmallestDegree)
  exact covered.trans (by simpa only [Nat.add_assoc] using total)

/-- A high opposite private port exists on a common label. There are at
least three common and two residual labels, and k≥2d suffices. The smaller
side's population bound X≤k follows from any B contact at a common label. -/
theorem private_exists (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (smaller : ∀ T : Finset V, T.card < S.card → (G.induce {u : V | u ∉ T}).Connected)
    (C : Finset V) (cs : C ⊆ S) (three : 3 ≤ C.card) (two : 2 ≤ (S \ C).card)
    (degree : 2*(S \ C).card ≤ G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (contacts : ∀ i ∈ S \ C, ∃ a ∈ A, G.secondSmallestDegree ≤ G.degree a ∧ G.Adj a i)
    (common : ∀ a ∈ A, G.secondSmallestDegree ≤ G.degree a → ∀ i ∈ C, G.Adj a i)
    (single : ∀ a ∈ A, G.secondSmallestDegree ≤ G.degree a →
      (Graph189PortLabels.support G S a \ C).card ≤ 1)
    (big : S.card*G.secondSmallestDegree <
      (B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card) :
    ∃ i ∈ C, ∃ b ∈ B, G.secondSmallestDegree ≤ G.degree b ∧ S.filter (G.Adj b) = {i} := by
  classical
  by_contra absent
  let X := A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)
  let Y := B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)
  obtain ⟨i,hi⟩ := card_pos.mp (show 0 < C.card by omega)
  obtain ⟨b,hb,bi⟩ := (sides.contacts_of_minimum smaller (cs hi)).2
  have xcap := Graph189PortDifference.common_label_capacity hc sides (X := X)
    (filter_subset _ _) (fun a ha => common a (mem_filter.mp ha).1 (mem_filter.mp ha).2 i hi) hb bi cap
  have bound := absent_bound hc sides C cs two cap contacts common single absent
  have total := Graph189ResidualDoubleCharge.within_cut C.card (S \ C).card
    G.secondSmallestDegree X.card Y.card three degree xcap bound
  have part := card_sdiff_add_card_eq_card cs
  have eq : C.card+(S \ C).card=S.card := by omega
  rw [eq] at total
  exact (not_lt_of_ge total) big

#print axioms absent_bound
#print axioms private_exists
end Graph189ResidualPrivatePort
