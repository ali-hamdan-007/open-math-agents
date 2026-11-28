import Graph189PositiveEvenCut
import Graph189ResidualWindows
import Graph189BoundaryDebit

namespace Graph189ThreePrivateDensity
open Graph189PrivateQuota Graph189PositiveEvenCut
open Finset SimpleGraph
open scoped BigOperators
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

variable {V : Type*} {G : SimpleGraph V} {A B S : Finset V}

private theorem private_distance (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    {x y i : V} (hx : x ∈ A) (hy : y ∈ B) (hmax : G.dist x y ≤ 4)
    (one : ∀ j ∈ S, G.Adj x j → j = i)
    (nonport : ∀ j ∈ S, ¬G.Adj y j) (notTwo : G.dist i y ≠ 2) : Even (G.dist x y) := by
  classical
  by_contra hodd
  have noOne : G.dist x y ≠ 1 := fun h => sides.no_cross x hx y hy (dist_eq_one_iff_adj.mp h)
  have d3 : G.dist x y = 3 := by rw [Nat.even_iff] at hodd; omega
  obtain ⟨p,hp⟩ := (hc x y).exists_walk_length_eq_dist
  obtain ⟨j,hj,hmem⟩ := sides.meets hx hy p
  have lengths := congrArg SimpleGraph.Walk.length (Walk.take_spec p hmem)
  rw [Walk.length_append] at lengths
  have left := G.dist_le (p.takeUntil j hmem)
  have right := G.dist_le (p.dropUntil j hmem)
  have tri := hc.dist_triangle (u:=x) (v:=j) (w:=y)
  have xj0 : G.dist x j ≠ 0 := by
    intro h
    exact Finset.disjoint_left.mp sides.left_cut hx ((hc.dist_eq_zero_iff.mp h).symm ▸ hj)
  have jy0 : G.dist j y ≠ 0 := by
    intro h
    exact Finset.disjoint_left.mp sides.right_cut hy ((hc.dist_eq_zero_iff.mp h) ▸ hj)
  have jy1 : G.dist j y ≠ 1 := fun h => nonport j hj (dist_eq_one_iff_adj.mp h).symm
  have xj1 : G.dist x j = 1 := by omega
  have ji := one j hj (dist_eq_one_iff_adj.mp xj1)
  apply notTwo
  rw [←ji]
  omega

variable [Fintype V] [DecidableEq V] [Nontrivial V] [DecidableRel G.Adj]

theorem quota (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (contacts : ∀ i ∈ S, ∃ a ∈ A, G.secondSmallestDegree ≤ G.degree a ∧ G.Adj a i)
    (privatePorts : ∀ a ∈ A, G.secondSmallestDegree ≤ G.degree a →
      (Graph189PortLabels.support G S a).card ≤ 1)
    (debit : ∀ a ∈ A,
      ((B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).filter
        (fun v => Even (G.dist a v))).card + S.card ≤
        G.secondSmallestDegree + (Graph189PortLabels.support G S a).card)
    (three : S.card=3)
    (depth : ∀ {a u : V}, a∈A → G.secondSmallestDegree≤G.degree a → u∈A →
      G.secondSmallestDegree≤G.degree u → a≠u → ¬G.Adj a u → G.dist a u=2) :
    2*(A.filter (fun v => G.secondSmallestDegree≤G.degree v)).card+
      3*(B.filter (fun v => G.secondSmallestDegree≤G.degree v)).card+12 ≤ 12*G.secondSmallestDegree := by
  classical
  let k := G.secondSmallestDegree
  let X := A.filter (fun v => k ≤ G.degree v)
  let Y := B.filter (fun v => k ≤ G.degree v)
  let P := Y.filter (fun v => ∃ i ∈ S, G.Adj v i)
  let N := Y \ P
  let QA (i : V) := X.filter (G.Adj i)
  let QB (i : V) := Y.filter (G.Adj i)
  let Z (i : V) := N.filter (fun v => G.dist i v = 2)
  let EA (i : V) := X.filter (fun v => G.dist i v = 2)
  let T (a : V) := X.filter (fun u => u=a ∨ G.Adj a u)
  let r := k+1-S.card
  have xs : X ⊆ A := filter_subset _ _
  have ys : Y ⊆ B := filter_subset _ _
  have ps : P ⊆ Y := filter_subset _ _
  have ns : N ⊆ Y := sdiff_subset
  have Sne : S.Nonempty := by
    obtain ⟨a,ha⟩ := sides.left_nonempty
    obtain ⟨b,hb⟩ := sides.right_nonempty
    obtain ⟨p⟩ := hc a b
    obtain ⟨i,hi,_⟩ := sides.meets ha hb p
    exact ⟨i,hi⟩
  have nonport (y : V) (hy : y ∈ N) (i : V) (hi : i ∈ S) : ¬G.Adj y i := by
    intro h
    exact (mem_sdiff.mp hy).2 (mem_filter.mpr ⟨ns hy,i,hi,h⟩)
  have labels_unique (a : V) (ha : a ∈ X) {i j : V} (hi : i ∈ S) (hj : j ∈ S)
      (ai : G.Adj a i) (aj : G.Adj a j) : i = j :=
    card_le_one_iff.mp (privatePorts a (xs ha) (mem_filter.mp ha).2)
      (mem_filter.mpr ⟨hi,ai⟩) (mem_filter.mpr ⟨hj,aj⟩)
  have degree_pair_bound (a : V) (ha : a ∈ X) (b : V) (hb : b ∈ Y) : G.dist a b ≤ 4 := by
    have c' (v : V) : G.distEven v ≤ 1+k := by simpa only [k,Nat.add_comm 1] using cap v
    have top := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc) (u:=a) (v:=b)).trans
      (diameter_le_five hc c')
    have n5 : G.dist a b ≠ 5 := by
      intro eq
      rcases five_endpoints hc cap a b eq with h | h
      · exact (not_lt_of_ge (mem_filter.mp ha).2) h
      · exact (not_lt_of_ge (mem_filter.mp hb).2) h
    omega
  have representative (i : V) (hi : i ∈ S) : ∃ a ∈ X, G.Adj a i := by
    obtain ⟨a,ha,hk,edge⟩ := contacts i hi
    exact ⟨a,mem_filter.mpr ⟨ha,hk⟩,edge⟩
  have s_le : S.card ≤ k+1 := by
    obtain ⟨i,hi⟩ := Sne
    obtain ⟨a,ha,_⟩ := representative i hi
    have hd := debit a (xs ha)
    have hp := privatePorts a (xs ha) (mem_filter.mp ha).2
    change _ + S.card ≤ k + _ at hd
    omega
  have rEq : r + S.card = k+1 := Nat.sub_add_cancel s_le
  have qBport (i : V) (hi : i ∈ S) : QB i ⊆ P := by
    intro y hy
    obtain ⟨hY,edge⟩ := mem_filter.mp hy
    exact mem_filter.mpr ⟨hY,i,hi,edge.symm⟩
  have opposite_row (i : V) (hi : i ∈ S) : (QB i).card ≤ r ∧
      (QB i).card + N.card + X.card ≤ 2*k+(QA i).card := by
    obtain ⟨a,ha,ai⟩ := representative i hi
    let E := Y.filter (fun v => Even (G.dist a v))
    have hquota := debit a (xs ha)
    have hprivate := privatePorts a (xs ha) (mem_filter.mp ha).2
    change E.card + S.card ≤ k + _ at hquota
    have Ecap : E.card ≤ r := by omega
    have port_even : QB i ⊆ E := by
      intro y hy
      obtain ⟨hY,edge⟩ := mem_filter.mp hy
      have ay : a ≠ y := by
        rintro rfl
        exact Finset.disjoint_left.mp sides.apart (xs ha) (ys hY)
      exact mem_filter.mpr ⟨hY,by simp [exact_two hc ai edge ay (sides.no_cross a (xs ha) y (ys hY))]⟩
    have nonport_even : N \ Z i ⊆ E := by
      intro y hy
      obtain ⟨hn,notZ⟩ := mem_sdiff.mp hy
      have hY := ns hn
      exact mem_filter.mpr ⟨hY,private_distance hc sides (xs ha) (ys hY)
        (degree_pair_bound a ha y hY) (fun j hj aj => labels_unique a ha hj hi aj ai)
        (nonport y hn) (fun d => notZ (mem_filter.mpr ⟨hn,d⟩))⟩
    have dis : Disjoint (QB i) (N \ Z i) := by
      rw [Finset.disjoint_left]
      intro y hy hn
      exact (mem_sdiff.mp (mem_sdiff.mp hn).1).2 (qBport i hi hy)
    have cross := card_le_card (union_subset port_even nonport_even)
    rw [card_union_of_disjoint dis] at cross
    have eq := card_sdiff_add_card_eq_card (filter_subset (fun v => G.dist i v = 2) N)
    change (N \ Z i).card+(Z i).card=N.card at eq
    have tsplit := card_sdiff_add_card_eq_card (show T a⊆X from filter_subset _ _)
    have nonnear : X \ T a ⊆ evenOthers G a := by
      intro u hu
      obtain ⟨ux,absent⟩ := mem_sdiff.mp hu
      have outside : ¬(u=a ∨ G.Adj a u) := fun h => absent (mem_filter.mpr ⟨ux,h⟩)
      have ne : u≠a := fun h => outside (Or.inl h)
      have no : ¬G.Adj a u := fun h => outside (Or.inr h)
      have hd := depth (xs ha) (mem_filter.mp ha).2 (xs ux) (mem_filter.mp ux).2 ne.symm no
      exact mem_even_others ne (by simp [hd])
    have evrow : E⊆evenOthers G a := by
      intro v hv
      have ne : v≠a := fun e => Finset.disjoint_left.mp sides.apart (xs ha) (e ▸ ys (mem_filter.mp hv).1)
      exact mem_even_others ne (mem_filter.mp hv).2
    have disA : Disjoint (X \ T a) E :=
      sides.apart.mono (sdiff_subset.trans xs) ((filter_subset _ _).trans ys)
    have allEven := (card_le_card (union_subset nonnear evrow)).trans (even_others_card (cap a))
    rw [card_union_of_disjoint disA] at allEven
    have tnear : T a⊆QA i ∪ EA i := by
      intro u hu
      obtain ⟨huX,close⟩ := mem_filter.mp hu
      by_cases edge : G.Adj i u
      · exact mem_union_left _ (mem_filter.mpr ⟨huX,edge⟩)
      rcases close with eq | au
      · exact (edge (eq ▸ ai.symm)).elim
      have ne : i≠u := fun eq => disjoint_left.mp sides.left_cut (xs huX) (eq ▸ hi)
      exact mem_union_right _ (mem_filter.mpr ⟨huX,exact_two hc ai.symm au ne edge⟩)
    have counts := (card_le_card tnear).trans (card_union_le _ _)
    have ez : Disjoint (EA i) (Z i) := sides.apart.mono
      ((filter_subset _ _).trans xs) ((filter_subset _ _).trans (ns.trans ys))
    have quota := two_layer_budget G (cap i) (EA i) (Z i) ez
      (fun _ hv => (mem_filter.mp hv).2) (fun _ hz => (mem_filter.mp hz).2)
    exact ⟨(card_le_card port_even).trans Ecap,by omega⟩
  have A_sum : ∑ i ∈ S, (QA i).card ≤ X.card := by
    have hdis : (S : Set V).PairwiseDisjoint QA := by
      intro i hi j hj hne
      change Disjoint (QA i) (QA j)
      rw [Finset.disjoint_left]
      intro a hai haj
      obtain ⟨ha,ia⟩ := mem_filter.mp hai
      exact hne (labels_unique a ha hi hj ia.symm (mem_filter.mp haj).2.symm)
    have hsub : S.biUnion QA ⊆ X := by
      intro a ha
      obtain ⟨i,_,hai⟩ := mem_biUnion.mp ha
      exact (mem_filter.mp hai).1
    rw [← card_biUnion hdis]
    exact card_le_card hsub
  have ports : P.card ≤ ∑ i ∈ S, (QB i).card := by
    have hsub : P ⊆ S.biUnion QB := by
      intro y hy
      obtain ⟨hY,i,hi,edge⟩ := mem_filter.mp hy
      exact mem_biUnion.mpr ⟨i,hi,mem_filter.mpr ⟨hY,edge.symm⟩⟩
    exact (card_le_card hsub).trans card_biUnion_le
  have portsCap : P.card ≤ S.card*r := ports.trans (by
    calc
      ∑ i ∈ S, (QB i).card ≤ ∑ _i ∈ S, r := Finset.sum_le_sum fun i hi => (opposite_row i hi).1
      _ = _ := by rw [Finset.sum_const,Nat.nsmul_eq_mul])
  have rows : (∑ i∈S,(QB i).card)+S.card*(N.card+X.card)≤S.card*(2*k)+∑ i∈S,(QA i).card := by
    calc
      _ = ∑ i∈S,((QB i).card+(N.card+X.card)) := by simp [Finset.sum_add_distrib]
      _ ≤ ∑ i∈S,(2*k+(QA i).card) := Finset.sum_le_sum fun i hi => by
        have h := (opposite_row i hi).2
        omega
      _ = _ := by simp [Finset.sum_add_distrib]
  have part := card_sdiff_add_card_eq_card ps
  change N.card+P.card=Y.card at part
  rw [three] at rows portsCap rEq
  change 2*X.card+3*Y.card+12≤12*k
  omega

#print axioms quota

private theorem dense_depth (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (small : A.card<2*G.secondSmallestDegree)
    (privatePorts : ∀ a∈A, G.secondSmallestDegree≤G.degree a →
      (Graph189PortLabels.support G S a).card≤1) {a v : V}
    (aa : a∈A) (ah : G.secondSmallestDegree≤G.degree a)
    (va : v∈A) (vh : G.secondSmallestDegree≤G.degree v)
    (ne : a≠v) (no : ¬G.Adj a v) : G.dist a v=2 := by
  classical
  let U (w : V) := A ∩ G.neighborFinset w
  have internal (w : V) (m : w∈A) (h : G.secondSmallestDegree≤G.degree w) :
      G.secondSmallestDegree≤(U w).card+1 := by
    have sub : G.neighborFinset w⊆U w ∪ Graph189PortLabels.support G S w := by
      intro u hu
      have wu := (G.mem_neighborFinset w u).mp hu
      rcases cut.cover u with ua | ub | us
      · exact mem_union_left _ (mem_inter.mpr ⟨ua,hu⟩)
      · exact (cut.no_cross w m u ub wu).elim
      · exact mem_union_right _ (mem_filter.mpr ⟨us,wu⟩)
    have size := (card_le_card sub).trans (card_union_le _ _)
    rw [G.card_neighborFinset_eq_degree] at size
    have labels := privatePorts w m h
    omega
  have manyA := internal a aa ah
  have manyV := internal v va vh
  by_cases overlap : (U a ∩ U v).Nonempty
  · obtain ⟨w,hw⟩ := overlap
    exact Graph189PrivateQuota.exact_two hc
      ((G.mem_neighborFinset a w).mp (mem_inter.mp (mem_inter.mp hw).1).2)
      ((G.mem_neighborFinset v w).mp (mem_inter.mp (mem_inter.mp hw).2).2).symm ne no
  have both : Disjoint (U a) (U v) :=
    disjoint_left.mpr fun _ ha hv => overlap ⟨_,mem_inter.mpr ⟨ha,hv⟩⟩
  have card := card_union_of_disjoint both
  have av : a∉U a ∪ U v := by
    intro ha
    rcases mem_union.mp ha with ha | ha
    · exact G.loopless.irrefl a ((G.mem_neighborFinset a a).mp (mem_inter.mp ha).2)
    · exact no ((G.mem_neighborFinset v a).mp (mem_inter.mp ha).2).symm
  have vv : v∉U a ∪ U v := by
    intro hv
    rcases mem_union.mp hv with hv | hv
    · exact no ((G.mem_neighborFinset a v).mp (mem_inter.mp hv).2)
    · exact G.loopless.irrefl v ((G.mem_neighborFinset v v).mp (mem_inter.mp hv).2)
  have incl : insert a (insert v (U a∪U v))⊆A :=
    insert_subset aa (insert_subset va (union_subset inter_subset_left inter_subset_left))
  have count := card_le_card incl
  rw [card_insert_of_notMem (fun h => (mem_insert.mp h).elim ne av),card_insert_of_notMem vv,card] at count
  omega

/-- Graph-facing form when the small side has at most 2k−1 vertices. -/
theorem dense_private_quota (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (smaller : ∀ T : Finset V, T.card<S.card → (G.induce {v : V | v∉T}).Connected)
    (three : S.card=3) (small : A.card<2*G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    (contacts : ∀ i∈S, ∃ a∈A, G.secondSmallestDegree≤G.degree a ∧ G.Adj a i)
    (privatePorts : ∀ a∈A, G.secondSmallestDegree≤G.degree a →
      (Graph189PortLabels.support G S a).card≤1) :
    2*(A.filter (fun v => G.secondSmallestDegree≤G.degree v)).card+
      3*(B.filter (fun v => G.secondSmallestDegree≤G.degree v)).card+12 ≤ 12*G.secondSmallestDegree :=
  quota hc cut cap contacts privatePorts
    (fun a aa => Graph189BoundaryDebit.even_quota hc cut smaller cap (filter_subset _ _) aa)
    three (dense_depth hc cut small privatePorts)

#print axioms dense_private_quota
end Graph189ThreePrivateDensity
