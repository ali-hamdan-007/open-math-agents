import Graph189AlmostFullColumn

open Finset SimpleGraph
namespace Graph189CutColumnCaps
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S X Y : Finset V}

/-- Above order 2k+t on the other side, each source column loses at
least t+1 units of its initial k allowance. -/
theorem below_threshold (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (smaller : ∀ T : Finset V, T.card<S.card → (G.induce {v : V | v∉T}).Connected)
    {k t : ℕ} (cap : ∀ v, G.distEven v≤k+1) (xs : X⊆A) (ys : Y⊆B)
    (room : 2*t<S.card) (many : 2*k+t<Y.card) {i : V} (hi : i∈S) :
    (X.filter (G.Adj i)).card+t<k := by
  classical
  by_contra! near
  have close := Graph189AlmostFullColumn.opposite_population hc cut smaller cap xs ys hi near room
  obtain ⟨a,aa,ai⟩ := (cut.contacts_of_minimum smaller hi).1
  have bound := Graph189PortDifference.common_label_capacity hc cut.swap
    (X:=Y.filter (G.Adj i)) ((filter_subset _ _).trans ys)
    (fun b hb => (mem_filter.mp hb).2.symm) aa ai cap
  omega

/-- If all high source vertices share the relevant label, the bound
on that column is a bound on the entire high source side. -/
theorem common_below_threshold (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (smaller : ∀ T : Finset V, T.card<S.card → (G.induce {v : V | v∉T}).Connected)
    {k t : ℕ} (cap : ∀ v, G.distEven v≤k+1) (xs : X⊆A) (ys : Y⊆B)
    (room : 2*t<S.card) (many : 2*k+t<Y.card) {i : V} (hi : i∈S)
    (common : ∀ x∈X,G.Adj x i) : X.card+t<k := by
  classical
  have bound := below_threshold hc cut smaller cap xs ys room many hi
  rwa [filter_eq_self.mpr (fun x hx => (common x hx).symm)] at bound

#print axioms below_threshold
#print axioms common_below_threshold
end Graph189CutColumnCaps
