import Graph189PrivatePortRecut
import Graph189FiniteDomain

namespace Graph189CutSides
open SimpleGraph Finset Graph189FiniteDomain

/-- The order hypothesis for reorientation follows from the validity
predicate on every terminal band, independently of its tabulation. -/
theorem valid_recut_order {r : Band} (ok : valid r = true) : 6*r.k+r.s+1 ≤ r.low := by
  simp only [valid,decide_eq_true_eq] at ok
  obtain ⟨hs,hk,_,_,_,_,_,hn,_⟩ := ok
  have excess := mul_nonneg (show 0 ≤ r.s-5 by omega) (show 0 ≤ r.k by omega)
  nlinarith only [excess,hn,hs]

namespace CutSides
variable {V : Type*} [Fintype V] [Nontrivial V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B S : Finset V}

/-- The repeated-cut contradiction applies to the actual graph parameters of
any valid terminal band. Its private label may be shared by every high vertex
of A or have enough contacts by a different route. -/
theorem private_port_terminal_band (sides : CutSides G A B S) (hc : G.Connected)
    (cap : ∀ y, G.distEven y ≤ 1+G.secondSmallestDegree)
    (minimum : S.card = G.vertexConnectivity) {r : Band} (ok : valid r = true)
    (rs : r.s = (S.card : ℤ)) (rk : r.k = (G.secondSmallestDegree : ℤ))
    (order : r.low ≤ (Fintype.card V : ℤ))
    (uniform : ∀ W F T : Finset V, CutSides G W F T → T.card = G.vertexConnectivity →
      (W.filter (fun y => G.secondSmallestDegree ≤ G.degree y)).card ≤
      (F.filter (fun y => G.secondSmallestDegree ≤ G.degree y)).card →
      ∀ y ∈ W, G.secondSmallestDegree ≤ G.degree y → 2 ≤ (T.filter (G.Adj y)).card)
    {v i : V} (hv : v ∈ B) (high : G.secondSmallestDegree ≤ G.degree v)
    (support : S.filter (G.Adj v) = {i})
    (many : G.secondSmallestDegree+1 ≤ S.card+(A ∩ G.neighborFinset i).card) : False := by
  have bound := (valid_recut_order ok).trans order
  rw [rs,rk] at bound
  exact sides.no_high_private_at_large_label hc cap minimum (by exact_mod_cast bound)
    uniform hv high support many

omit [Nontrivial V] in
/-- A common label has enough contacts as soon as the smaller high
population is at least k−s+1, written without truncated subtraction. -/
theorem common_label_contacts {i : V}
    (common : ∀ y ∈ A, G.secondSmallestDegree ≤ G.degree y → G.Adj y i)
    (pop : G.secondSmallestDegree + 1 ≤ S.card+
      (A.filter (fun y => G.secondSmallestDegree ≤ G.degree y)).card) :
    G.secondSmallestDegree + 1 ≤ S.card+(A ∩ G.neighborFinset i).card := by
  have incl : A.filter (fun y => G.secondSmallestDegree ≤ G.degree y) ⊆
      A ∩ G.neighborFinset i := by
    intro y hy
    obtain ⟨ha,hh⟩ := mem_filter.mp hy
    exact mem_inter.mpr ⟨ha,(G.mem_neighborFinset _ _).mpr (common y ha hh).symm⟩
  exact pop.trans (Nat.add_le_add_left (card_le_card incl) _)

end CutSides
#print axioms valid_recut_order
#print axioms CutSides.private_port_terminal_band
#print axioms CutSides.common_label_contacts
end Graph189CutSides
