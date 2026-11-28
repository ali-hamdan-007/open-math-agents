import Graph189ThreeDensityWindow
import Graph189FullLabelExit
import Graph189TwoRootRecut

namespace Graph189ThreeCut

/-- Consequences of an oriented three-cut's population product at the
two lifted order thresholds. The estimates use integral populations. -/
theorem sharp_numerical {x y k : ℤ} (deg : 26≤k)
    (region : (5*k-6≤x+y) ∨ (38≤k ∧ 5*k-15≤x+y) ∨ (67≤k ∧ 5*k-25≤x+y))
    (nonnegative : 0≤x) (oriented : x≤y) (product : x*y≤k*x+3*k*k) :
    3*k<y ∧ 9*k-15+x<3*y ∧ (x≤k → 6*k+x<2*y) := by
  have yy := mul_nonneg nonnegative (sub_nonneg.mpr oriented)
  have upper : 13*x≤30*k := by
    by_contra! high
    have h := mul_nonneg (show 0≤13*x-30*k by omega) (show 0≤13*x+17*k by omega)
    nlinarith only [h,yy,product,sq_nonneg (k-1),deg]
  rcases region with h|h|h
  · obtain ⟨small,large⟩ := numerical deg nonnegative oriented h product
    omega
  · obtain ⟨hk,sum⟩ := h
    have up : x≤3*k-27 := by
      by_contra! bad
      have eq : k=38 := by omega
      have xx : x=87 := by omega
      rw [eq,xx] at product
      omega
    have small : x≤k+11 := by
      by_contra! high
      have q := mul_nonneg (show 0≤x-k-12 by omega) (show 0≤3*k-27-x by omega)
      have t := mul_nonneg nonnegative (show 0≤x+y-5*k+15 by omega)
      nlinarith only [product,q,t,hk]
    omega
  · obtain ⟨hk,sum⟩ := h
    have small : x≤k+18 := by
      by_contra! high
      have q := mul_nonneg (show 0≤x-k-19 by omega) (show 0≤3*k-44-x by omega)
      have t := mul_nonneg nonnegative (show 0≤x+y-5*k+25 by omega)
      nlinarith only [product,q,t,hk]
    omega

#print axioms sharp_numerical
end Graph189ThreeCut

open SimpleGraph Finset
namespace Graph189ThreeCut
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V}

def HighOrder (k n : ℕ) : Prop :=
  5*k≤n+2 ∨ (38≤k ∧ 5*k≤n+11) ∨ (67≤k ∧ 5*k≤n+21)

theorem quotas (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (minimum : S.card = G.vertexConnectivity) (three : S.card=3)
    (cap : ∀ v, G.distEven v ≤ 1+G.secondSmallestDegree)
    (degree : 26 ≤ G.secondSmallestDegree) (region : HighOrder G.secondSmallestDegree (Fintype.card V))
    (orient : (A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card ≤
      (B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card) :
    let k : ℤ := G.secondSmallestDegree
    let x : ℤ := (A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card
    let y : ℤ := (B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card
    3*k<y ∧ 9*k-15+x<3*y ∧ (x≤k → 6*k+x<2*y) := by
  classical
  let k := G.secondSmallestDegree
  let X := A.filter (fun v => k ≤ G.degree v)
  let Y := B.filter (fun v => k ≤ G.degree v)
  have smaller (T : Finset V) (lt : T.card<S.card) := Graph189CutSides.connected_after_smaller_deletion (G:=G) T (lt.trans_eq minimum)
  have natProd := cut.high_product hc smaller cap
  change X.card*Y.card ≤ X.card*k+S.card*(k*k) at natProd
  rw [three] at natProd
  have prod : (X.card:ℤ)*Y.card ≤ (k:ℤ)*X.card+3*k*k := by
    exact_mod_cast (show X.card*Y.card ≤ k*X.card+3*k*k by simpa only [Nat.mul_comm X.card k,Nat.mul_assoc] using natProd)
  have total := Graph189MinimumQuotas.high_population_lower cut
  change (Fintype.card V:ℤ)-S.card-1 ≤ (X.card:ℤ)+Y.card at total
  rw [three] at total
  change 26≤k at degree
  change HighOrder k (Fintype.card V) at region
  change 3*(k:ℤ)<Y.card ∧ 9*(k:ℤ)-15+X.card<3*(Y.card:ℤ) ∧
    ((X.card:ℤ)≤k → 6*(k:ℤ)+X.card<2*(Y.card:ℤ))
  rcases region with h|h|h
  · exact sharp_numerical (by exact_mod_cast degree) (Or.inl (by omega))
      (Int.natCast_nonneg X.card) (show (X.card:ℤ)≤Y.card by exact_mod_cast orient) prod
  · obtain ⟨h1,h2⟩ := h
    exact sharp_numerical (by exact_mod_cast degree) (Or.inr (Or.inl ⟨by omega,by omega⟩))
      (Int.natCast_nonneg X.card) (show (X.card:ℤ)≤Y.card by exact_mod_cast orient) prod
  · obtain ⟨h1,h2⟩ := h
    exact sharp_numerical (by exact_mod_cast degree) (Or.inr (Or.inr ⟨by omega,by omega⟩))
      (Int.natCast_nonneg X.card) (show (X.card:ℤ)≤Y.card by exact_mod_cast orient) prod

theorem order_room {k n : ℕ} (hk : 26≤k) (hr : HighOrder k n) : 4*k+4<n := by
  rcases hr with h|h|h <;> omega

#print axioms quotas
end Graph189ThreeCut

open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189ThreeCut
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V}

/-- The explicit large-degree estimates and the finite degree thresholds
both supply the same three numerical conditions used in the graph argument. -/
def Supported (k n : ℕ) : Prop :=
  (26≤k ∧ HighOrder k n) ∨ Graph189ThreeCutThresholds.Certified k n

private theorem supported_quotas (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (minimum : S.card = G.vertexConnectivity) (three : S.card=3)
    (cap : ∀ v, G.distEven v ≤ 1+G.secondSmallestDegree)
    (region : Supported G.secondSmallestDegree (Fintype.card V))
    (orient : (A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card ≤
      (B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card) :
    let k : ℤ := G.secondSmallestDegree
    let x : ℤ := (A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card
    let y : ℤ := (B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card
    3*k<y ∧ 9*k-15+x<3*y ∧ (x≤k → 6*k+x<2*y) := by
  rcases region with ⟨degree,region⟩ | region
  · exact quotas hc cut minimum three cap degree region orient
  · exact Graph189ThreeCutThresholds.quotas hc cut minimum three cap region orient

private theorem supported_room {k n : ℕ} (region : Supported k n) : 4*k+4<n :=
  region.elim (fun h => order_room h.1 h.2) Graph189ThreeCutThresholds.order_room

def Covered (k n : ℕ) : Prop := Supported k n ∨ (33≤k ∧ k≤36 ∧ 5*k≤n+11)

private theorem covered_room {k n : ℕ} (region : Covered k n) : 4*k+4<n := by
  rcases region with old|⟨lo,_,floor⟩
  · exact supported_room old
  · omega

private theorem covered_quotas (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (minimum : S.card = G.vertexConnectivity) (three : S.card=3)
    (cap : ∀ v, G.distEven v ≤ 1+G.secondSmallestDegree)
    (region : Covered G.secondSmallestDegree (Fintype.card V))
    (orient : (A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card ≤
      (B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card) :
    let k : ℤ := G.secondSmallestDegree
    let x : ℤ := (A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card
    let y : ℤ := (B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card
    3*k<y ∧ (9*k-15+x<3*y ∨ ((A.card:ℤ)<2*k ∧ 12*k<2*x+3*y+12)) ∧ (x≤k → 6*k+x<2*y) := by
  rcases region with old|⟨lo,hi,floor⟩
  · obtain ⟨big,privateBound,last⟩ := supported_quotas hc cut minimum three cap old orient
    exact ⟨big,Or.inl privateBound,last⟩
  · exact Graph189ThreeDensityWindow.quotas hc cut minimum three cap lo hi floor orient

def PortQuotas (G : SimpleGraph V) [DecidableRel G.Adj] (A B S : Finset V) : Prop :=
  let k : ℤ := G.secondSmallestDegree
  let x : ℤ := (A.filter (fun v => G.secondSmallestDegree≤G.degree v)).card
  let y : ℤ := (B.filter (fun v => G.secondSmallestDegree≤G.degree v)).card
  3*k<y ∧ (9*k-15+x<3*y ∨ ((A.card:ℤ)<2*k ∧ 12*k<2*x+3*y+12)) ∧
    ∀ i∈S, (∀a∈A, G.secondSmallestDegree≤G.degree a → G.Adj a i) → 6*k+x<2*y

private theorem covered_port_quotas (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (minimum : S.card=G.vertexConnectivity) (three : S.card=3)
    (cap : ∀v,G.distEven v≤1+G.secondSmallestDegree)
    (region : Covered G.secondSmallestDegree (Fintype.card V))
    (orient : (A.filter (fun a => G.secondSmallestDegree≤G.degree a)).card≤
      (B.filter (fun b => G.secondSmallestDegree≤G.degree b)).card) : PortQuotas G A B S := by
  obtain ⟨big,privateBound,last⟩ := covered_quotas hc cut minimum three cap region orient
  refine ⟨big,privateBound,?_⟩
  intro i hi all
  have smaller (T : Finset V) (lt : T.card<S.card) :=
    Graph189CutSides.connected_after_smaller_deletion (G:=G) T (lt.trans_eq minimum)
  obtain ⟨b,hb,bi⟩ := (cut.contacts_of_minimum smaller hi).2
  have few := Graph189PortDifference.common_label_capacity hc cut
    (X:=A.filter (fun a => G.secondSmallestDegree≤G.degree a)) (filter_subset _ _)
    (fun v hv => all v (mem_filter.mp hv).1 (mem_filter.mp hv).2) hb bi
    (fun v => by simpa only [Nat.add_comm 1] using cap v)
  exact last (by exact_mod_cast few)

/-- Every smaller high side has a common anchor and a high vertex joined to
all three anchors. Each high vertex of that side has at least two contacts. -/
theorem ports_of_quotas (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (minimum : S.card = G.vertexConnectivity) (three : S.card=3)
    (deletion : ∀ z : V, (G.induce {v : V | v≠z}).Connected)
    (cap : ∀ v, G.distEven v ≤ 1+G.secondSmallestDegree)
    (roomOrder : 4*G.secondSmallestDegree+4<Fintype.card V)
    (data : PortQuotas G A B S) :
    (∃ i∈S, ∀ a∈A, G.secondSmallestDegree≤G.degree a → G.Adj a i) ∧
    (∃ a∈A, G.secondSmallestDegree≤G.degree a ∧ ∀ i∈S, G.Adj a i) ∧
    ∀ a∈A, G.secondSmallestDegree≤G.degree a → 2≤(S.filter (G.Adj a)).card := by
  classical
  let k := G.secondSmallestDegree
  let X := A.filter (fun v => k≤G.degree v)
  let Y := B.filter (fun v => k≤G.degree v)
  change 3*(k:ℤ)<Y.card ∧ (9*(k:ℤ)-15+X.card<3*(Y.card:ℤ) ∨
      ((A.card:ℤ)<2*k ∧ 12*(k:ℤ)<2*X.card+3*Y.card+12)) ∧
    (∀i∈S, (∀a∈A,k≤G.degree a → G.Adj a i) → 6*(k:ℤ)+X.card<2*(Y.card:ℤ)) at data
  obtain ⟨largeY,notPrivate,notResidual⟩ := data
  have big : S.card*k<Y.card := by
    rw [three]
    exact_mod_cast largeY
  have nbig : (S.card+1)*k+S.card+1<Fintype.card V := by
    rw [three]
    exact roomOrder
  have big' := big.trans_le (card_le_card (show Y⊆B from filter_subset _ _))
  have sm (T : Finset V) (lt : T.card<S.card) := Graph189CutSides.connected_after_smaller_deletion (G:=G) T (lt.trans_eq minimum)
  have cp (v : V) : G.distEven v≤k+1 := by simpa only [k,Nat.add_comm] using cap v
  have contacts (i : V) (hi : i∈S) := Graph189HighLabel.all_labels_in_order_range hc cut deletion sm cp big' nbig hi
  have debit (a : V) (ha : a∈A) := Graph189BoundaryDebit.even_quota hc cut sm cp (Y:=Y) (filter_subset _ _) ha
  have common : ∃ i∈S, ∀ a∈A, k≤G.degree a → G.Adj a i := by
    by_contra! no
    have missed (i : V) (hi : i∈S) : ∃ y∈X, ¬G.Adj y i := by
      obtain ⟨y,ya,high,absent⟩ := no i hi
      exact ⟨y,mem_filter.mpr ⟨ya,high⟩,absent⟩
    rcases Graph189CutFamilies.singleton_or_two_missing hc cut sm deletion cap big nbig with singles|few
    · have privatePorts (a : V) (aa : a∈A) (ah : k≤G.degree a) : (Graph189PortLabels.support G S a).card≤1 := by
        have h := singles a (mem_filter.mpr ⟨aa,ah⟩)
        have equal : ((Graph189PortLabels.support G S a).filter (fun i => ∃ y∈X, ¬G.Adj y i))=Graph189PortLabels.support G S a :=
          filter_eq_self.mpr (fun i hi => missed i (mem_filter.mp hi).1)
        rwa [equal] at h
      have q := Graph189PrivateQuota.private_from_residual hc cut cp contacts privatePorts debit
      change ((X.card:ℤ)+Y.card)*S.card ≤ ((S.card:ℤ)*k-S.card*((S.card:ℤ)-1)+X.card+1)*S.card+X.card at q
      rw [three] at q
      rcases notPrivate with old | ⟨smallA,strong⟩
      · omega
      · have density := Graph189ThreePrivateDensity.dense_private_quota hc cut sm three
          (by exact_mod_cast smallA) cp contacts privatePorts
        change 2*X.card+3*Y.card+12≤12*k at density
        omega
    · have equal : (S.filter (fun i => ∃ y∈X, ¬G.Adj y i))=S := filter_eq_self.mpr missed
      rw [equal,three] at few
      omega
  obtain ⟨i,hi,all⟩ := common
  have full : ∃ a∈A, k≤G.degree a ∧ ∀ j∈S, G.Adj a j := by
    by_contra! no
    let C : Finset V := {i}
    have cs : C⊆S := singleton_subset_iff.mpr hi
    have size : (S \ C).card=2 := by
      have h := card_sdiff_add_card_eq_card cs
      simpa [C,three] using h
    have privatePorts (a : V) (aa : a∈A) (ah : k≤G.degree a) : (Graph189PortLabels.support G S a \ C).card≤1 := by
      let T := Graph189PortLabels.support G S a
      have mem : i∈T := mem_filter.mpr ⟨hi,all a aa ah⟩
      obtain ⟨j,js,miss⟩ := no a aa ah
      have sub : T ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset _ _,fun eq =>
        miss (mem_filter.mp (show j∈T from eq ▸ js)).2⟩
      have h := card_lt_card sub
      change (T \ C).card≤1
      have csub : C⊆T := singleton_subset_iff.mpr mem
      have r := card_sdiff_add_card_eq_card csub
      rw [show C.card=1 from card_singleton i] at r
      omega
    have residual := Graph189PrivateQuota.residual_singleton_quota hc cut C cs
      (card_pos.mp (by omega)) cp (fun j hj => contacts j (mem_sdiff.mp hj).1)
      (fun a ha high j hj => (mem_singleton.mp hj).symm ▸ all a ha high) privatePorts debit
    change ((X.card:ℤ)+Y.card)*((S \ C).card:ℤ) ≤ ((S.card:ℤ)*k-((S \ C).card:ℤ)*(((S \ C).card:ℤ)-1)+X.card+C.card+1)*((S \ C).card:ℤ)+X.card at residual
    rw [three,size] at residual
    have ccard : C.card=1 := card_singleton _
    rw [ccard] at residual
    have contradiction := notResidual i hi all
    omega
  obtain ⟨a,aa,ah,whole⟩ := full
  refine ⟨⟨i,hi,all⟩,⟨a,aa,ah,whole⟩,?_⟩
  intro v hv vh
  have wholeSet : Graph189PortLabels.support G S a=S := filter_eq_self.mpr whole
  have near (y : V) (hy : y∈Y) : G.dist v y≤4 := by
    have upper := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc) (u:=v) (v:=y)).trans (diameter_le_five hc cap)
    have far : G.dist v y≠5 := by
      intro eq
      exact (five_endpoints hc cp v y eq).elim (not_lt_of_ge vh) (not_lt_of_ge (mem_filter.mp hy).2)
    omega
  have h := Graph189PortDifference.one_new_label (Y:=Y) hc cut (filter_subset _ _) hv aa near
    (fun j hj => (cut.contacts_of_minimum sm hj).1) cp big
  rw [wholeSet] at h
  have sz := card_sdiff_add_card_eq_card (show Graph189PortLabels.support G S v⊆S from filter_subset _ _)
  change 2≤(Graph189PortLabels.support G S v).card
  omega

theorem covered_ports (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (minimum : S.card = G.vertexConnectivity) (three : S.card=3)
    (deletion : ∀ z : V, (G.induce {v : V | v≠z}).Connected)
    (cap : ∀ v, G.distEven v ≤ 1+G.secondSmallestDegree)
    (region : Covered G.secondSmallestDegree (Fintype.card V))
    (orient : (A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card ≤
      (B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card) :
    (∃ i∈S, ∀ a∈A, G.secondSmallestDegree≤G.degree a → G.Adj a i) ∧
    (∃ a∈A, G.secondSmallestDegree≤G.degree a ∧ ∀ i∈S, G.Adj a i) ∧
    ∀ a∈A, G.secondSmallestDegree≤G.degree a → 2≤(S.filter (G.Adj a)).card :=
  ports_of_quotas hc cut minimum three deletion cap (covered_room region)
    (covered_port_quotas hc cut minimum three cap region orient)

theorem supported_ports (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (minimum : S.card = G.vertexConnectivity) (three : S.card=3)
    (deletion : ∀ z : V, (G.induce {v : V | v≠z}).Connected)
    (cap : ∀ v, G.distEven v ≤ 1+G.secondSmallestDegree)
    (region : Supported G.secondSmallestDegree (Fintype.card V))
    (orient : (A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card ≤
      (B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card) :
    (∃ i∈S, ∀ a∈A, G.secondSmallestDegree≤G.degree a → G.Adj a i) ∧
    (∃ a∈A, G.secondSmallestDegree≤G.degree a ∧ ∀ i∈S, G.Adj a i) ∧
    ∀ a∈A, G.secondSmallestDegree≤G.degree a → 2≤(S.filter (G.Adj a)).card :=
  covered_ports hc cut minimum three deletion cap (Or.inl region) orient

theorem small_side_ports (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (minimum : S.card = G.vertexConnectivity) (three : S.card=3)
    (deletion : ∀ z : V, (G.induce {v : V | v≠z}).Connected)
    (cap : ∀ v, G.distEven v ≤ 1+G.secondSmallestDegree)
    (degree : 26 ≤ G.secondSmallestDegree) (region : HighOrder G.secondSmallestDegree (Fintype.card V))
    (orient : (A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card ≤
      (B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card) :
    (∃ i∈S, ∀ a∈A, G.secondSmallestDegree≤G.degree a → G.Adj a i) ∧
    (∃ a∈A, G.secondSmallestDegree≤G.degree a ∧ ∀ i∈S, G.Adj a i) ∧
    ∀ a∈A, G.secondSmallestDegree≤G.degree a → 2≤(S.filter (G.Adj a)).card :=
  supported_ports hc cut minimum three deletion cap (Or.inl ⟨degree,region⟩) orient

#print axioms small_side_ports
end Graph189ThreeCut

open SimpleGraph Finset
namespace Graph189ThreeCut
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The original even-distance cap forces an upper bound on the order
of every qualifying graph of vertex connectivity three. -/
theorem excludes_from_quotas (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (three : G.vertexConnectivity=3) (roomOrder : 4*G.secondSmallestDegree+4<Fintype.card V)
    (rows : ∀ {A B S : Finset V}, Graph189CutSides.CutSides G A B S → S.card=G.vertexConnectivity →
      (A.filter (fun a => G.secondSmallestDegree≤G.degree a)).card≤
        (B.filter (fun b => G.secondSmallestDegree≤G.degree b)).card → PortQuotas G A B S) : False := by
  classical
  let k := G.secondSmallestDegree
  let H (P : Finset V) := P.filter (fun v => k≤G.degree v)
  have room : G.vertexConnectivity<Fintype.card V-1 := by omega
  have point (v : V) : G.distEven v≤1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have deletion (z : V) : (G.induce {v : V | v≠z}).Connected := by
    have same : {v : V | v∉({z} : Finset V)} = {v : V | v≠z} := by ext v; simp
    rw [←same]
    apply Graph189CutSides.connected_after_smaller_deletion (G:=G) ({z} : Finset V)
    simp [three]
  have uniform (W F T : Finset V) (cut : Graph189CutSides.CutSides G W F T)
      (eq : T.card=G.vertexConnectivity) (orientation : (H W).card≤(H F).card) :=
    (ports_of_quotas hc cut eq (eq.trans three) deletion point roomOrder (rows cut eq orientation)).2.2
  obtain ⟨U,F,S,minimum,sides⟩ := Graph189GraphPopulation.minimum_sides (G:=G) room
  have select : ∃ A B : Finset V, Graph189CutSides.CutSides G A B S ∧ (H A).card≤(H B).card := by
    rcases le_total (H U).card (H F).card with h|h
    · exact ⟨U,F,sides,h⟩
    · exact ⟨F,U,sides.swap,h⟩
  obtain ⟨A,B,cut,orient⟩ := select
  have ss := minimum.trans three
  obtain ⟨common,full,_⟩ := ports_of_quotas hc cut minimum ss deletion point roomOrder (rows cut minimum orient)
  obtain ⟨i,hi,all⟩ := common
  obtain ⟨a,aa,ah,whole⟩ := full
  have giant := (rows cut minimum orient).1
  have many : S.card*G.secondSmallestDegree < (H B).card := by
    rw [ss]
    exact_mod_cast giant
  have point' (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by have h := point v; omega
  obtain ⟨j,_,b,hb,bh,support,enough⟩ := Graph189FullLabelExit.full_exit hc cut point'
    (by omega) many aa ah whole hi all
  exact Graph189FourCut.private_recut hc cut minimum point (by omega) hb bh support enough uniform

theorem excludes_covered (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (three : G.vertexConnectivity=3) (region : Covered G.secondSmallestDegree (Fintype.card V)) : False :=
  excludes_from_quotas hc cap three (covered_room region) (fun cut minimum orient =>
    covered_port_quotas hc cut minimum (minimum.trans three)
      (fun v => (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap) region orient)

theorem excludes_supported (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (three : G.vertexConnectivity=3) (region : Supported G.secondSmallestDegree (Fintype.card V)) : False :=
  excludes_covered hc cap three (Or.inl region)

theorem excludes_high (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (three : G.vertexConnectivity=3) (degree : 26≤G.secondSmallestDegree)
    (region : HighOrder G.secondSmallestDegree (Fintype.card V)) : False :=
  excludes_supported hc cap three (Or.inl ⟨degree,region⟩)

#print axioms excludes_supported
#print axioms excludes_high
end Graph189ThreeCut
