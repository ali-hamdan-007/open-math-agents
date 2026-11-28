import Graph189ClosedSide
import Graph189ThreeColumns

open SimpleGraph Finset Graph189PositiveEvenCut
namespace Graph189SaturatedOpposite
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B S X Y : Finset V}

/-- One saturated target column already bounds y+s*x at **any** minimum
cut of size s when x>k. The proof controls the opposite closed neighborhood
of its contact, so no assumption on the target size is needed. -/
theorem population (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (smaller : ∀ T : Finset V, T.card<S.card → (G.induce {v : V | v∉T}).Connected)
    (cap : ∀ v,G.distEven v≤1+G.secondSmallestDegree)
    (xs : X⊆A) (ys : Y⊆B) (xh : ∀ a∈X,G.secondSmallestDegree≤G.degree a)
    (yh : ∀ b∈Y,G.secondSmallestDegree≤G.degree b) (many : G.secondSmallestDegree<X.card)
    {i : V} (hi : i∈S) (sat : G.secondSmallestDegree≤(Y.filter (G.Adj i)).card) :
    Y.card+S.card*X.card≤G.secondSmallestDegree+S.card*(2*G.secondSmallestDegree) := by
  classical
  let k := G.secondSmallestDegree
  let U := Y.filter (G.Adj i)
  let A1 (j : V) := X.filter (G.Adj j)
  let A2 (j : V) := X.filter (fun v => G.dist j v=2)
  let B2 (j : V) := Y.filter (fun v => G.dist j v=2)
  have cp (v : V) : G.distEven v≤k+1 := by have h := cap v; change _≤1+k at h; omega
  obtain ⟨a,aa,ai⟩ := (cut.contacts_of_minimum smaller hi).1
  have us : U⊆B := (filter_subset _ _).trans ys
  have u2 (u : V) (hu : u∈U) : G.dist a u=2 :=
    Graph189PortDifference.cross_two hc cut aa (us hu) ai (mem_filter.mp hu).2
  have uEven : U⊆evenOthers G a :=
    fun u hu => mem_even_others (fun h => disjoint_left.mp cut.apart aa (h ▸ us hu)) (by simp [u2 u hu])
  change k≤U.card at sat
  have em := even_others_card (cp a)
  have eq : U=evenOthers G a := eq_of_subset_of_card_le uEven (em.trans sat)
  have support := Graph189BoundaryDebit.even_quota hc cut smaller cp us aa
  have hfilter : U.filter (fun u => Even (G.dist a u))=U :=
    filter_eq_self.mpr fun u hu => by simp [u2 u hu]
  rw [hfilter] at support
  have full : Graph189PortLabels.support G S a=S :=
    eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  have all (j : V) (hj : j∈S) : G.Adj a j :=
    (mem_filter.mp (show j∈Graph189PortLabels.support G S a from full ▸ hj)).2
  have spos : 0<(Graph189PortLabels.support G S a).card := card_pos.mpr ⟨i,mem_filter.mpr ⟨hi,ai⟩⟩
  have cover : Y⊆U∪S.biUnion B2 := by
    intro v hv
    by_cases some : ∃ j∈S,G.Adj j v
    · obtain ⟨j,hj,jv⟩ := some
      have ne : v≠a := fun h => disjoint_left.mp cut.apart aa (h ▸ ys hv)
      have d := Graph189PortDifference.cross_two hc cut aa (ys hv) (all j hj) jv
      exact mem_union_left _ (eq ▸ mem_even_others ne (by simp [d]))
    · obtain ⟨j,hj,d⟩ := Graph189ThreeColumns.nonport_second hc cut cap xs xh many (ys hv) (yh v hv)
          (fun j hj jv => some ⟨j,hj,jv⟩)
      exact mem_union_right _ (mem_biUnion.mpr ⟨j,hj,mem_filter.mpr ⟨hv,d⟩⟩)
  have row (j : V) (hj : j∈S) : (B2 j).card+X.card≤2*k := by
    obtain ⟨b,bb,bj⟩ := (cut.contacts_of_minimum smaller hj).2
    have a1 := Graph189PortDifference.common_label_capacity hc cut (X:=A1 j)
      ((filter_subset _ _).trans xs) (fun v hv => (mem_filter.mp hv).2.symm) bb bj cp
    have known := Graph189ClosedSide.second_column cut.swap smaller aa (cp a) us uEven
      (t:=0) (by omega) spos hc xs hj (all j hj)
    change X.card≤(A1 j).card+(A2 j).card+0 at known
    have quota := Graph189PrivateQuota.two_layer_budget G (cp j) (A2 j) (B2 j)
      (cut.apart.mono ((filter_subset _ _).trans xs) ((filter_subset _ _).trans ys))
      (fun v hv => (mem_filter.mp hv).2) (fun v hv => (mem_filter.mp hv).2)
    omega
  have rows := Finset.sum_le_sum row
  simp only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul] at rows
  have reach := (card_le_card cover).trans (card_union_le _ _)
  have layers : (S.biUnion B2).card≤∑ j∈S,(B2 j).card := card_biUnion_le
  have uk := (card_le_card uEven).trans em
  change Y.card+S.card*X.card≤k+S.card*(2*k)
  omega

#print axioms population
end Graph189SaturatedOpposite
