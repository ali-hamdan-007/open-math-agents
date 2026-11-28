import Graph189CutClassification

open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189PrivatePorts

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V}
variable [DecidableRel G.Adj] {A B S : Finset V}

/-- If one high vertex of the smaller side has no separator neighbor, every
vertex on its side touches at most one label. Low vertices can serve as
representatives on the cut. -/
theorem private_of_high_nonport (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (smaller : ∀ T : Finset V, T.card < S.card → (G.induce {v : V | v ∉ T}).Connected)
    (cap : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree)
    (big : S.card*G.secondSmallestDegree <
      (B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card)
    {x : V} (hx : x ∈ A) (high : G.secondSmallestDegree ≤ G.degree x)
    (nonport : ∀ i ∈ S, ¬ G.Adj x i) :
    ∀ y ∈ A, (Graph189PortLabels.support G S y).card ≤ 1 := by
  classical
  let Y := B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)
  have c' (v : V) : G.distEven v ≤ G.secondSmallestDegree+1 := by simpa [Nat.add_comm] using cap v
  have diam (v : V) (hv : v ∈ Y) : G.dist x v ≤ 4 := by
    have d := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc) (u:=x) (v:=v)).trans
      (diameter_le_five hc cap)
    have nf : G.dist x v ≠ 5 := by
      intro eq
      rcases five_endpoints hc c' x v eq with h | h
      · exact (not_lt_of_ge high) h
      · exact (not_lt_of_ge (mem_filter.mp hv).2) h
    omega
  have empty : Graph189PortLabels.support G S x = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hs,edge⟩ := mem_filter.mp hv
    exact nonport v hs edge
  intro y hy
  have h := Graph189PortDifference.one_new_label (Y := Y) hc sides (filter_subset _ _)
    hx hy diam (fun i hi => (sides.contacts_of_minimum smaller hi).1) c' big
  simpa [empty] using h

#print axioms private_of_high_nonport
end Graph189PrivatePorts
