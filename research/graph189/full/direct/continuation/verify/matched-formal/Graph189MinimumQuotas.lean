import Graph189ResidualSingleton
import Graph189BoundaryDebit
import Graph189PortDifference
import Graph189FiniteDomain

namespace Graph189MinimumQuotas
open Finset SimpleGraph Graph189FiniteDomain

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V}
variable [DecidableRel G.Adj] {A B S : Finset V}

/-- Removing the separator and the only possible low vertex leaves the two high populations. -/
theorem high_population_lower (sides : Graph189CutSides.CutSides G A B S) :
    (Fintype.card V : ℤ) - S.card - 1 ≤
      ((A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card : ℤ) +
      ((B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card : ℤ) := by
  classical
  let X := A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)
  let Y := B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)
  let L := univ.filter (fun v => ¬G.secondSmallestDegree ≤ G.degree v)
  have small : L.card ≤ 1 := by
    apply card_le_one.mpr
    intro u hu v hv
    by_contra hne
    exact (OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) u v hne).elim
      (mem_filter.mp hu).2 (mem_filter.mp hv).2
  have cover : univ ⊆ ((X ∪ Y) ∪ S) ∪ L := by
    intro v hv
    by_cases high : G.secondSmallestDegree ≤ G.degree v
    · apply mem_union_left
      rcases sides.cover v with h|h|h
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨h,high⟩))
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨h,high⟩))
      · exact mem_union_right _ h
    · exact mem_union_right _ (mem_filter.mpr ⟨hv,high⟩)
  have h := card_le_card cover
  rw [card_univ] at h
  have h₁ := card_union_le X Y
  have h₂ := card_union_le (X ∪ Y) S
  have h₃ := card_union_le ((X ∪ Y) ∪ S) L
  have full : Fintype.card V ≤ X.card+Y.card+S.card+1 := by omega
  have fullI : (Fintype.card V : ℤ) ≤ X.card+Y.card+S.card+1 := by exact_mod_cast full
  change _ ≤ (X.card : ℤ)+Y.card
  omega

/-- Private high supports are impossible in every valid terminal interval. -/
theorem private_impossible (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (smaller : ∀ T : Finset V, T.card < S.card → (G.induce {v : V | v ∉ T}).Connected)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (contacts : ∀ i ∈ S, ∃ a ∈ A, G.secondSmallestDegree ≤ G.degree a ∧ G.Adj a i)
    (privatePorts : ∀ a ∈ A, G.secondSmallestDegree ≤ G.degree a →
      (Graph189PortLabels.support G S a).card ≤ 1)
    {r : Band} (validity : valid r = true)
    (rs : r.s = S.card) (rk : r.k = G.secondSmallestDegree)
    (bound : ((A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card : ℤ) ≤ r.cap)
    (size : r.low-r.s-1 ≤
      ((A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card : ℤ) +
      ((B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card : ℤ)) : False := by
  classical
  let X := A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)
  let Y := B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)
  have quota := Graph189PrivateQuota.private_from_residual hc sides cap contacts privatePorts
    (fun a ha => Graph189BoundaryDebit.even_quota hc sides smaller cap (Y:=Y) (filter_subset _ _) ha)
  have quota' : ((X.card : ℤ)+Y.card)*r.s ≤
      (r.s*r.k-r.s*(r.s-1)+X.card+1)*r.s+X.card := by
    rw [rs,rk]
    exact quota
  have h := validity
  simp only [valid,decide_eq_true_eq] at h
  obtain ⟨hs,_,_,_,_,_,_,_,_,hq,_,_,_⟩ := h
  have hs0 : 0 ≤ r.s := by omega
  change (X.card : ℤ) ≤ r.cap at bound
  change r.low-r.s-1 ≤ (X.card : ℤ)+Y.card at size
  have h₁ := mul_le_mul_of_nonneg_right size hs0
  have h₂ := mul_le_mul_of_nonneg_right bound hs0
  nlinarith only [quota',bound,hq,h₁,h₂]

/-- The one- and two-common-label residual singleton cases of every valid terminal interval. -/
theorem small_common_impossible (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (smaller : ∀ T : Finset V, T.card < S.card → (G.induce {v : V | v ∉ T}).Connected)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (C : Finset V) (csub : C ⊆ S) (csmall : C.card = 1 ∨ C.card = 2)
    (contacts : ∀ i ∈ S \ C, ∃ a ∈ A, G.secondSmallestDegree ≤ G.degree a ∧ G.Adj a i)
    (common : ∀ a ∈ A, G.secondSmallestDegree ≤ G.degree a → ∀ i ∈ C, G.Adj a i)
    (privatePorts : ∀ a ∈ A, G.secondSmallestDegree ≤ G.degree a →
      (Graph189PortLabels.support G S a \ C).card ≤ 1)
    {r : Band} (validity : valid r = true)
    (rs : r.s = S.card) (rk : r.k = G.secondSmallestDegree)
    (size : r.low-r.s-1 ≤
      ((A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card : ℤ) +
      ((B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card : ℤ)) : False := by
  classical
  let X := A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)
  let Y := B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)
  let c : ℤ := C.card
  let d := r.s-c
  have h := validity
  simp only [valid,decide_eq_true_eq] at h
  obtain ⟨hs,_,_,_,_,_,_,_,_,_,_,h1,h2⟩ := h
  have hcsmall : c = 1 ∨ c = 2 := by
    rcases csmall with h|h
    · exact Or.inl (by simp [c,h])
    · exact Or.inr (by simp [c,h])
  have dpos : 0 < d := by dsimp only [d]; omega
  have remEq : ((S \ C).card : ℤ) = d := by
    have hn := card_sdiff_add_card_eq_card csub
    have hi : ((S \ C).card : ℤ) + C.card = S.card := by exact_mod_cast hn
    dsimp only [d,c]
    omega
  have nonempty : (S \ C).Nonempty := card_pos.mp (by omega)
  have quota := Graph189PrivateQuota.residual_singleton_quota hc sides C csub nonempty cap contacts common privatePorts
    (fun a ha => Graph189BoundaryDebit.even_quota hc sides smaller cap (Y:=Y) (filter_subset _ _) ha)
  have quota' : ((X.card : ℤ)+Y.card)*d ≤
      (r.s*r.k-d*(d-1)+X.card+c+1)*d+X.card := by
    change ((X.card : ℤ)+Y.card)*((S \ C).card : ℤ) ≤ _ at quota
    rw [rs,rk,← remEq]
    exact quota
  have highCap : (X.card : ℤ) ≤ r.k := by
    obtain ⟨i,hi⟩ := card_pos.mp (show 0 < C.card by omega)
    obtain ⟨b,hb,bi⟩ := (sides.contacts_of_minimum smaller (csub hi)).2
    have h := Graph189PortDifference.common_label_capacity hc sides (X:=X) (filter_subset _ _)
      (fun a ha => common a (mem_filter.mp ha).1 (mem_filter.mp ha).2 i hi) hb bi cap
    rw [rk]
    exact_mod_cast h
  have hq : quotaPass r c = true := by rcases hcsmall with eq|eq <;> rw [eq] <;> assumption
  simp only [quotaPass,decide_eq_true_eq] at hq
  change (r.s*r.k+r.k-d*(d-1)+c+1)*d+r.k < (r.low-r.s-1)*d at hq
  change r.low-r.s-1 ≤ (X.card : ℤ)+Y.card at size
  have h₁ := mul_le_mul_of_nonneg_right size dpos.le
  have h₂ := mul_le_mul_of_nonneg_right highCap dpos.le
  nlinarith only [quota',highCap,hq,h₁,h₂]

#print axioms private_impossible
#print axioms small_common_impossible
end Graph189MinimumQuotas
