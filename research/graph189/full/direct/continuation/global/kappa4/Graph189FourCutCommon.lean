import Graph189FourCutSaturationFacts
import Graph189CutFamilies
import Graph189CrossBoundaryProduct
import Graph189MinimumCutOrder
import Graph189MinimumQuotas

open Finset SimpleGraph

namespace Graph189FourCut

/-- The two high-order ranges for the four-cut population argument. -/
def Range (k n : ℕ) : Prop :=
  ((26 : ℤ) ≤ k ∧ 6 * (k : ℤ) ≤ (n : ℤ) + 10) ∨
  ((33 : ℤ) ≤ k ∧ 6 * (k : ℤ) ≤ (n : ℤ) + 19)

private theorem large_population {k x y d : ℤ} (hk : 0 < k) (hd : 0 ≤ d)
    (margin : 3*d < 2*k) (total : 6*k-d ≤ x+y) (orient : x ≤ y)
    (product : x*y ≤ x*k+4*k*k) : 4*k < y := by
  by_contra! hy
  have yk : 0 ≤ y-k := by omega
  have right : 0 ≤ y-(3*k-d) := by omega
  have first := mul_nonneg (show 0 ≤ x-(6*k-d-y) by omega) yk
  have second := mul_nonneg (show 0 ≤ 4*k-y by omega) right
  have strict := mul_pos hk (show 0 < 2*k-3*d by omega)
  nlinarith

private theorem population_bounds {k n x y : ℤ}
    (region : (26 ≤ k ∧ 6*k ≤ n+10) ∨ (36 ≤ k ∧ 6*k ≤ n+19))
    (nonneg : 0 ≤ x) (total : n-5 ≤ x+y) (orient : x ≤ y)
    (product : x*y ≤ x*k+4*k*k)
    (charged : x*y+4*x ≤ x*k+4*k*k+4*k) :
    4*k < y ∧ 16*k-44+x < 4*y ∧ (x ≤ k → 12*k-12+x < 3*y) := by
  have hk : 0 < k := by rcases region with ⟨_,_⟩|⟨_,_⟩ <;> omega
  have big : 4*k < y := by
    rcases region with ⟨_,_⟩|⟨_,_⟩
    · exact large_population (d:=15) hk (by decide) (by omega) (by omega) orient product
    · by_cases boundary : k = 36
      · subst k
        by_contra! upper
        have first := mul_nonneg (show 0 ≤ x-(192-y) by omega) (show 0 ≤ y-32 by omega)
        have second := mul_nonneg (show 0 ≤ 144-y by omega) (show 0 ≤ y-80 by omega)
        nlinarith
      · exact large_population (d:=24) hk (by decide) (by omega) (by omega) orient product
  have extra := mul_nonneg nonneg (show 0 ≤ y-(4*k+1) by omega)
  have small : 3*x < 4*k := by
    by_contra! fail
    have m := mul_nonneg (show 0 ≤ 3*x-4*k by omega) (le_of_lt hk)
    nlinarith
  refine ⟨big, ?_, ?_⟩
  · rcases region with ⟨_,_⟩|⟨_,_⟩
    · omega
    · by_cases eq : k = 37
      · subst k
        have : x ≤ 48 := by nlinarith
        omega
      · omega
  · intro xk
    rcases region with ⟨_,_⟩|⟨_,_⟩ <;> omega

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B S : Finset V}

/-- Every oriented minimum four-cut in the stated range has at least two
labels adjacent to every high vertex of its smaller side. -/
theorem two_common (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (deletion : ∀ z : V, (G.induce {v : V | v ≠ z}).Connected)
    (minimum : S.card = G.vertexConnectivity) (four : S.card = 4)
    (cap : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree)
    (orient : (A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card ≤
      (B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card)
    (region : Range G.secondSmallestDegree (Fintype.card V)) :
    S.card*G.secondSmallestDegree < (B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card ∧
    (S.card+1)*G.secondSmallestDegree+S.card+1 < Fintype.card V ∧
    2 ≤ (S.filter (fun i => ∀ a ∈ A, G.secondSmallestDegree ≤ G.degree a → G.Adj a i)).card := by
  classical
  let k := G.secondSmallestDegree
  let X := A.filter (fun v => k ≤ G.degree v)
  let Y := B.filter (fun v => k ≤ G.degree v)
  let C := S.filter (fun i => ∀ a ∈ A, k ≤ G.degree a → G.Adj a i)
  have cs : C ⊆ S := filter_subset _ _
  have sm (T : Finset V) (lt : T.card < S.card) :=
    Graph189CutSides.connected_after_smaller_deletion (G:=G) T (lt.trans_eq minimum)
  have cp (v : V) : G.distEven v ≤ k+1 := by simpa only [k,Nat.add_comm] using cap v
  have total := Graph189MinimumQuotas.high_population_lower cut
  have prod := cut.high_product hc sm cap
  have debited := Graph189CrossBoundaryProduct.high_product cut hc sm cap
  change X.card*Y.card+X.card*S.card ≤ X.card*k+S.card*(k*k)+S.card*k at debited
  change X.card*Y.card ≤ X.card*k+S.card*(k*k) at prod
  change (Fintype.card V : ℤ)-S.card-1 ≤ (X.card:ℤ)+Y.card at total
  rw [four] at prod total debited
  have prodZ : (X.card:ℤ)*Y.card ≤ X.card*k+4*((k:ℤ)*k) := by exact_mod_cast prod
  have debitZ : (X.card:ℤ)*Y.card+X.card*4 ≤ X.card*k+4*((k:ℤ)*k)+4*k := by exact_mod_cast debited
  have bounds : 4*(k:ℤ)<Y.card ∧ 16*(k:ℤ)-44+X.card<4*Y.card ∧
      ((X.card:ℤ)≤k → 12*(k:ℤ)-12+X.card<3*Y.card) := by
    by_cases old : ((26:ℤ)≤k ∧ 6*(k:ℤ)≤(Fintype.card V:ℤ)+10) ∨
        ((36:ℤ)≤k ∧ 6*(k:ℤ)≤(Fintype.card V:ℤ)+19)
    · exact population_bounds old (by positivity) (by omega) (by exact_mod_cast orient)
        (by nlinarith) (by nlinarith)
    · change ((26:ℤ)≤k ∧ 6*(k:ℤ)≤(Fintype.card V:ℤ)+10) ∨
          ((33:ℤ)≤k ∧ 6*(k:ℤ)≤(Fintype.card V:ℤ)+19) at region
      have special := Graph189FourCutSaturationFacts.quotas hc cut minimum four cap
        (by change 33≤k; omega) (by change k≤35; omega)
        (by change 6*k≤Fintype.card V+19; omega) orient
      change 4*k<Y.card ∧ 16*k+X.card<4*Y.card+44 ∧ (X.card≤k → 12*k+X.card<3*Y.card+12) at special
      omega
  obtain ⟨large,noPrivate,noResidual⟩ := bounds
  have big : S.card*k < Y.card := by rw [four]; exact_mod_cast large
  have room : (S.card+1)*k+S.card+1 < Fintype.card V := by
    rw [four]
    rcases region with ⟨_,_⟩|⟨_,_⟩ <;> dsimp only [k] <;> omega
  refine ⟨big,room,?_⟩
  change 2 ≤ C.card
  have contact (i : V) (hi : i ∈ S) := Graph189HighLabel.all_labels_in_order_range hc cut deletion sm cp
    (big.trans_le (card_le_card (show Y ⊆ B from filter_subset _ _))) room hi
  have debit (a : V) (ha : a ∈ A) := Graph189BoundaryDebit.even_quota hc cut sm cp (Y:=Y) (filter_subset _ _) ha
  have common (a : V) (ha : a ∈ A) (ah : k ≤ G.degree a) (j : V) (jc : j ∈ C) :=
    (mem_filter.mp jc).2 a ha ah
  have missing {j : V} (js : j ∈ S) : j ∉ C ↔ ∃ y ∈ X, ¬G.Adj y j := by
    constructor
    · intro miss
      by_contra! all
      exact miss (mem_filter.mpr ⟨js,fun a ha ah => all a (mem_filter.mpr ⟨ha,ah⟩)⟩)
    · rintro ⟨a,ha,miss⟩ jc
      exact miss (common a (mem_filter.mp ha).1 (mem_filter.mp ha).2 j jc)
  have part := card_sdiff_add_card_eq_card cs
  rcases Graph189CutFamilies.singleton_or_two_missing hc cut sm deletion cap big room with singles|few
  · have privatePorts (a : V) (ha : a ∈ A) (ah : k ≤ G.degree a) :
        (Graph189PortLabels.support G S a \ C).card ≤ 1 := by
      have eq : (Graph189PortLabels.support G S a \ C) =
          (Graph189PortLabels.support G S a).filter (fun i => ∃ y ∈ X, ¬G.Adj y i) := by
        ext i
        constructor
        · intro h
          obtain ⟨hi,nc⟩ := mem_sdiff.mp h
          exact mem_filter.mpr ⟨hi,(missing (mem_filter.mp hi).1).mp nc⟩
        · intro h
          obtain ⟨hi,miss⟩ := mem_filter.mp h
          exact mem_sdiff.mpr ⟨hi,(missing (mem_filter.mp hi).1).mpr miss⟩
      rw [eq]
      exact singles a (mem_filter.mpr ⟨ha,ah⟩)
    by_contra! thin
    by_cases empty : C = ∅
    · have one (a : V) (ha : a ∈ A) (ah : k ≤ G.degree a) := privatePorts a ha ah
      simp only [empty,sdiff_empty] at one
      have q := Graph189PrivateQuota.private_from_residual hc cut cp contact one debit
      change ((X.card:ℤ)+Y.card)*S.card ≤ ((S.card:ℤ)*k-S.card*((S.card:ℤ)-1)+X.card+1)*S.card+X.card at q
      rw [four] at q
      omega
    · have pos := card_pos.mpr (nonempty_iff_ne_empty.mpr empty)
      have cc : C.card=1 := by omega
      have dd : (S \ C).card=3 := by omega
      obtain ⟨i,ic⟩ := card_pos.mp pos
      obtain ⟨b,hb,bi⟩ := (cut.contacts_of_minimum sm (cs ic)).2
      have xk := Graph189PortDifference.common_label_capacity hc cut (X:=X) (filter_subset _ _)
        (fun a ha => common a (mem_filter.mp ha).1 (mem_filter.mp ha).2 i ic) hb bi cp
      have contradiction := noResidual (by exact_mod_cast xk)
      have q := Graph189PrivateQuota.residual_singleton_quota hc cut C cs (card_pos.mp (by omega)) cp
        (fun j hj => contact j (mem_sdiff.mp hj).1) common privatePorts debit
      change ((X.card:ℤ)+Y.card)*((S \ C).card:ℤ) ≤ ((S.card:ℤ)*k-((S \ C).card:ℤ)*(((S \ C).card:ℤ)-1)+X.card+C.card+1)*((S \ C).card:ℤ)+X.card at q
      rw [four,cc,dd] at q
      omega
  · have eq : (S \ C) = S.filter (fun i => ∃ y ∈ X, ¬G.Adj y i) := by
      ext i
      constructor
      · intro h
        obtain ⟨hi,nc⟩ := mem_sdiff.mp h
        exact mem_filter.mpr ⟨hi,(missing hi).mp nc⟩
      · intro h
        obtain ⟨hi,miss⟩ := mem_filter.mp h
        exact mem_sdiff.mpr ⟨hi,(missing hi).mpr miss⟩
    change (S.filter (fun i => ∃ y ∈ X, ¬G.Adj y i)).card ≤ 2 at few
    rw [← eq] at few
    omega

#print axioms two_common
end Graph189FourCut
