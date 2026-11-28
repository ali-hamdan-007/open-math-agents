import Graph189R1Metric
import Graph189CutSides
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Connectivity

namespace Graph189IndependentExpansion

open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The union of the open neighborhoods of the members of an independent set. -/
def neighbors (G : SimpleGraph V) [DecidableRel G.Adj] (I : Finset V) : Finset V :=
  I.biUnion (fun v => G.neighborFinset v)

omit [Nontrivial V] in
private theorem mem_neighbors {I : Finset V} {y : V} :
    y ∈ neighbors G I ↔ ∃ x ∈ I, G.Adj x y := by
  simp [neighbors, mem_biUnion, SimpleGraph.mem_neighborFinset]

omit [Nontrivial V] in
private theorem neighbor_subset {I : Finset V} {x : V} (hx : x ∈ I) :
    G.neighborFinset x ⊆ neighbors G I := by
  intro y hy
  exact mem_neighbors.mpr ⟨x,hx,(G.mem_neighborFinset _ _).mp hy⟩

omit [Fintype V] [DecidableEq V] [Nontrivial V] [DecidableRel G.Adj] in
private theorem two_step_metric {a b q : V} (different : a ≠ b) (missing : ¬G.Adj a b)
    (aq : G.Adj a q) (bq : G.Adj b q) : G.dist a b = 2 := by
  have h := SimpleGraph.edist_eq_two_iff.mpr ⟨different,missing,⟨q,aq,bq⟩⟩
  simp [SimpleGraph.dist,h]

-- These are the connectivity and degree facts used in Graph189MinimumCutOrder
-- and Graph189ConnectivityDegree, kept here with their minimal imports.
omit [DecidableRel G.Adj] in
private theorem connected_after_smaller_deletion (T : Finset V) (ht : T.card < G.vertexConnectivity) :
    (G.induce {u : V | u ∉ T}).Connected := by
  classical
  by_contra bad
  have hn := Fintype.one_lt_card (α := V)
  have bound : G.vertexConnectivity ≤ T.card := by
    unfold vertexConnectivity
    rw [if_neg (by omega : ¬ Fintype.card V ≤ 1)]
    exact Nat.sInf_le ⟨T,rfl,Or.inl bad⟩
  omega

private theorem connectivity_le_degree (z : V) : G.vertexConnectivity ≤ G.degree z := by
  classical
  let S := G.neighborFinset z
  have sz : S.card = G.degree z := G.card_neighborFinset_eq_degree z
  have convention : G.vertexConnectivity ≤ Fintype.card V-1 := by
    unfold vertexConnectivity
    rw [if_neg (not_le.mpr (Fintype.one_lt_card (α:=V)))]
    exact Nat.sInf_le ⟨univ.erase z,by simp,Or.inr (by simp)⟩
  by_contra! fail
  have conn := connected_after_smaller_deletion (G:=G) S (sz ▸ fail)
  let W := {v : V | v ∉ S}
  let z' : W := ⟨z, show z ∉ G.neighborFinset z by simp⟩
  have card : 1 < Fintype.card W := by
    have same : W = ((Sᶜ : Finset V) : Set V) := by ext v; simp [W]
    rw [Fintype.card_congr (Equiv.setCongr same)]
    change 1 < Fintype.card (Sᶜ : Finset V)
    rw [Fintype.card_coe,Finset.card_compl]
    omega
  let _ : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp card
  obtain ⟨w,edge⟩ := conn.preconnected.exists_adj_of_nontrivial z'
  exact w.property ((G.mem_neighborFinset z w.val).mpr edge)

omit [Nontrivial V] [DecidableRel G.Adj] in
private theorem even_bound {X : Finset V} {x : V} {k : ℕ} (nx : x ∉ X)
    (even : ∀ v ∈ X, Even (G.dist x v)) (cap : G.distEven x ≤ k+1) :
    X.card ≤ k := by
  classical
  have sub : insert x X ⊆ univ.filter (fun y => Even (G.dist x y)) := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · exact mem_filter.mpr ⟨mem_univ _,by simp⟩
    · exact mem_filter.mpr ⟨mem_univ _,even _ hy⟩
  have size := (card_le_card sub).trans cap
  rw [card_insert_of_notMem nx] at size
  omega

private theorem high_pairs_in_minimal_set (hc : G.Connected)
    (cap : ∀ x, G.distEven x ≤ G.secondSmallestDegree+1) {J : Finset V} {g : ℕ}
    (ind : ∀ x ∈ J, ∀ y ∈ J, ¬G.Adj x y) (small : (neighbors G J).card ≤ J.card+g)
    (minimal : ∀ F : Finset V, F.Nonempty → F ⊆ J → F.card < J.card →
      F.card+g < (neighbors G F).card)
    {x y : V} (hx : x ∈ J) (hy : y ∈ J) (xy : x ≠ y)
    (highx : G.secondSmallestDegree ≤ G.degree x)
    (highy : G.secondSmallestDegree ≤ G.degree y) : G.dist x y = 2 := by
  classical
  let Q := G.neighborFinset x
  let S := neighbors G J
  let F := J.filter (fun v => Disjoint Q (G.neighborFinset v))
  by_cases fy : y ∈ F
  · obtain ⟨u,xu⟩ := hc.preconnected.exists_adj_of_nontrivial x
    have notx : x ∉ F := by
      intro h
      have hd : Disjoint Q Q := (mem_filter.mp h).2
      have uq : u ∈ Q := (G.mem_neighborFinset _ _).mpr xu
      exact disjoint_left.mp hd uq uq
    have fsub : F ⊆ J := filter_subset _ _
    have fsmall : F.card < J.card :=
      card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨fsub,fun e => notx (e ▸ hx)⟩)
    have nb : neighbors G F ⊆ S \ Q := by
      intro a ha
      obtain ⟨v,hv,va⟩ := mem_neighbors.mp ha
      exact mem_sdiff.mpr ⟨mem_neighbors.mpr ⟨v,fsub hv,va⟩,fun aq =>
        disjoint_left.mp (mem_filter.mp hv).2 aq ((G.mem_neighborFinset _ _).mpr va)⟩
    let X := (J \ F).erase x
    have nc := minimal F ⟨y,fy⟩ fsub fsmall
    have bc := card_le_card nb
    have sq := card_sdiff_add_card_eq_card (neighbor_subset (G:=G) hx)
    have jf := card_sdiff_add_card_eq_card fsub
    have xc := card_erase_add_one (mem_sdiff.mpr ⟨hx,notx⟩)
    have deg : Q.card = G.degree x := G.card_neighborFinset_eq_degree x
    have few : G.secondSmallestDegree ≤ X.card := by
      change (neighbors G F).card ≤ (S \ Q).card at bc
      change (S \ Q).card + Q.card = S.card at sq
      change X.card+1 = (J \ F).card at xc
      change S.card ≤ J.card+g at small
      omega
    have two (v : V) (hv : v ∈ X) : G.dist x v = 2 := by
      obtain ⟨ne,mem⟩ := mem_erase.mp hv
      obtain ⟨vj,nf⟩ := mem_sdiff.mp mem
      have meet : ¬Disjoint Q (G.neighborFinset v) := fun h => nf (mem_filter.mpr ⟨vj,h⟩)
      obtain ⟨q,aq,bq⟩ := not_disjoint_iff.mp meet
      exact two_step_metric ne.symm (ind x hx v vj)
        ((G.mem_neighborFinset _ _).mp aq) ((G.mem_neighborFinset _ _).mp bq)
    let E := univ.filter (fun v => Even (G.dist x v))
    have sub : insert x X ⊆ E := by
      intro v hv
      rcases mem_insert.mp hv with rfl | hv
      · exact mem_filter.mpr ⟨mem_univ _,by simp⟩
      · exact mem_filter.mpr ⟨mem_univ _,by rw [two v hv]; decide⟩
    have nmem : x ∉ X := notMem_erase x _
    have eq : insert x X = E := eq_of_subset_of_card_le sub (by
      rw [card_insert_of_notMem nmem]
      exact (cap x).trans (by omega))
    have within (v : V) (hv : Even (G.dist x v)) : v ∈ insert x X := by
      rw [eq]
      exact mem_filter.mpr ⟨mem_univ _,hv⟩
    have le5 := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc) (u:=x) (v:=y)).trans
      (diameter_le_five hc (fun v => by simpa [Nat.add_comm] using cap v))
    have not5 : G.dist x y ≠ 5 := by
      intro e
      rcases five_endpoints hc cap x y e with e' | e' <;> omega
    have ge2 := hc.one_lt_dist_of_ne_of_not_adj xy (ind x hx y hy)
    have not4 : G.dist x y ≠ 4 := by
      intro e
      have m := within y (by rw [e]; decide)
      rcases mem_insert.mp m with h | h
      · exact xy h.symm
      · have hh := two y h
        omega
    have not3 : G.dist x y ≠ 3 := by
      intro e
      obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x y
      have htwo := geodesic hc p hp 0 2 (by decide) (by omega)
      rw [Walk.getVert_zero] at htwo
      have ins := within (p.getVert 2) (by rw [htwo]; decide)
      have jt : p.getVert 2 ∈ J := by
        rcases mem_insert.mp ins with h | h
        · exact h.symm ▸ hx
        · exact (mem_sdiff.mp (mem_erase.mp h).2).1
      have edge := p.adj_getVert_succ (show 2 < p.length by omega)
      rw [p.getVert_of_length_le (show p.length ≤ 2+1 by omega)] at edge
      exact ind _ jt _ hy edge
    omega
  · have meet : ¬Disjoint Q (G.neighborFinset y) := fun h => fy (mem_filter.mpr ⟨hy,h⟩)
    obtain ⟨q,aq,bq⟩ := not_disjoint_iff.mp meet
    exact two_step_metric xy (ind x hx y hy)
      ((G.mem_neighborFinset _ _).mp aq) ((G.mem_neighborFinset _ _).mp bq)

/-- If the vertex connectivity and graph order exceed the two stated bounds,
an independent set has at least the claimed number of extra neighbors. -/
theorem expansion (hc : G.Connected)
    (cap : ∀ x, G.distEven x ≤ G.secondSmallestDegree+1) {g : ℕ}
    (connected : g+2 ≤ G.vertexConnectivity)
    (order : 2*G.secondSmallestDegree+g+3 ≤ Fintype.card V)
    (I : Finset V) (nonempty : I.Nonempty)
    (independent : ∀ x ∈ I, ∀ y ∈ I, ¬G.Adj x y) :
    I.card+g+1 ≤ (neighbors G I).card := by
  classical
  let k := G.secondSmallestDegree
  by_contra! bad
  let P (n : ℕ) := ∃ J : Finset V, J ⊆ I ∧ J.Nonempty ∧ J.card = n ∧
    (neighbors G J).card ≤ J.card+g
  have ex : ∃ n, P n := ⟨I.card,I,Subset.rfl,nonempty,rfl,by omega⟩
  obtain ⟨J, jsub, jne, jsz, small⟩ := Nat.find_spec ex
  have min (F : Finset V) (fn : F.Nonempty) (fj : F ⊆ J) (lt : F.card < J.card) :
      F.card+g < (neighbors G F).card := by
    by_contra! h
    have h' := Nat.find_min' ex (show P F.card from ⟨F,fj.trans jsub,fn,rfl,h⟩)
    omega
  have ind (x : V) (hx : x ∈ J) (y : V) (hy : y ∈ J) :=
    independent x (jsub hx) y (jsub hy)
  let S := neighbors G J
  have js : Disjoint J S := disjoint_left.mpr fun v vj vs => by
    obtain ⟨u,uj,uv⟩ := mem_neighbors.mp vs
    exact ind u uj v vj uv
  have minDeg (v : V) : g+2 ≤ G.degree v :=
    connected.trans (connectivity_le_degree v)
  have jpos := card_pos.mpr jne
  obtain ⟨u,uj⟩ := jne
  obtain ⟨v,vj,vu⟩ : ∃ v ∈ J, v ≠ u := by
    by_contra! h
    have eq : J = {u} := Subset.antisymm
      (fun a aj => mem_singleton.mpr (h a aj)) (singleton_subset_iff.mpr uj)
    rw [eq,card_singleton] at small
    simp [neighbors,G.card_neighborFinset_eq_degree] at small
    have d := minDeg u
    omega
  obtain ⟨x,xj,xhigh⟩ : ∃ x ∈ J, k ≤ G.degree x :=
    ((degree_pair (G:=G) u v vu.symm).elim (fun h => ⟨u,uj,h⟩) (fun h => ⟨v,vj,h⟩))
  let H := J.filter (fun a => k ≤ G.degree a)
  have hj : H ⊆ J := filter_subset _ _
  have xh : x ∈ H := mem_filter.mpr ⟨xj,xhigh⟩
  have twoHigh (a : V) (ah : a ∈ H) (b : V) (bh : b ∈ H) (ab : a ≠ b) :
      G.dist a b = 2 := high_pairs_in_minimal_set hc cap ind small min
        (hj ah) (hj bh) ab (mem_filter.mp ah).2 (mem_filter.mp bh).2
  have highSize : H.card ≤ k+1 := by
    have c := even_bound (G:=G) (X:=H.erase x) (notMem_erase x _) (by
      intro b hb
      obtain ⟨bx,bh⟩ := mem_erase.mp hb
      rw [twoHigh x xh b bh bx.symm]
      decide) (cap x)
    rw [card_erase_of_mem xh] at c
    omega
  have lowSize : (J \ H).card ≤ 1 := card_le_one.mpr (by
    intro a al b bl
    by_contra neq
    rcases degree_pair (G:=G) a b neq with h | h
    · exact (mem_sdiff.mp al).2 (mem_filter.mpr ⟨(mem_sdiff.mp al).1,h⟩)
    · exact (mem_sdiff.mp bl).2 (mem_filter.mpr ⟨(mem_sdiff.mp bl).1,h⟩))
  have szH := card_sdiff_add_card_eq_card hj
  have allTwo (b : V) (bj : b ∈ J) (bx : b ≠ x) : G.dist x b = 2 := by
    by_cases bh : b ∈ H
    · exact twoHigh x xh b bh bx.symm
    by_contra no
    let D := G.neighborFinset b
    have bd : D ⊆ S := neighbor_subset (G:=G) bj
    have dis : Disjoint (G.neighborFinset x) D := disjoint_left.mpr fun a ax ab =>
      no (two_step_metric bx.symm (ind x xj b bj)
        ((G.mem_neighborFinset _ _).mp ax) ((G.mem_neighborFinset _ _).mp ab))
    have larger := card_le_card (union_subset (neighbor_subset (G:=G) xj) bd)
    rw [card_union_of_disjoint dis,G.card_neighborFinset_eq_degree] at larger
    change G.degree x + D.card ≤ S.card at larger
    have dmin : g+2 ≤ D.card := by
      simpa only [D,G.card_neighborFinset_eq_degree] using minDeg b
    change S.card ≤ J.card+g at small
    have full : H.card = k+1 := by
      omega
    have exactly : D.card = g+2 ∧ S.card = k+g+2 := by omega
    have noExtra (a : V) (ah : a ∈ H) (c : V) (ch : c ∉ H) (two : G.dist a c = 2) : False := by
      have m : c ∉ H.erase a := fun h => ch (mem_of_mem_erase h)
      have key := even_bound (G:=G) (X:=insert c (H.erase a)) (by
        simp only [mem_insert,not_or]
        exact ⟨fun e => ch (e ▸ ah),notMem_erase _ _⟩) (by
          intro y hy
          rcases mem_insert.mp hy with rfl | hy
          · rw [two]
            decide
          · obtain ⟨ne,m⟩ := mem_erase.mp hy
            rw [twoHigh a ah y m ne.symm]
            decide) (cap a)
      rw [card_insert_of_notMem m,card_erase_of_mem ah,full] at key
      omega
    have support (a : V) (ah : a ∈ H) : G.neighborFinset a = S \ D := by
      have sub := neighbor_subset (G:=G) (hj ah)
      have larger : G.neighborFinset a ⊆ S \ D := fun p pN => mem_sdiff.mpr ⟨sub pN,fun pD =>
        noExtra a ah b bh (two_step_metric (fun e => bh (e ▸ ah))
          (ind a (hj ah) b bj) ((G.mem_neighborFinset _ _).mp pN)
          ((G.mem_neighborFinset _ _).mp pD))⟩
      apply eq_of_subset_of_card_le larger
      rw [card_sdiff_of_subset bd,exactly.1,exactly.2,G.card_neighborFinset_eq_degree]
      have d := (mem_filter.mp ah).2
      omega
    let C := H ∪ (S \ D)
    have bx' : b ∉ C := by
      intro h
      rcases mem_union.mp h with h | h
      · exact bh h
      · exact disjoint_left.mp js bj (mem_sdiff.mp h).1
    obtain ⟨p⟩ := hc x b
    obtain ⟨a,c,ac,cc,e,_⟩ := Graph189CutSides.walk_exits (· ∈ C) p (mem_union_left _ xh) bx'
    rcases mem_union.mp ac with ah | aq
    · apply cc
      apply mem_union_right
      rw [← support a ah]
      exact (G.mem_neighborFinset _ _).mpr e
    · have aq' : a ∈ G.neighborFinset x := support x xh ▸ aq
      have cq : c ∉ G.neighborFinset x := fun h => cc (mem_union_right _ (support x xh ▸ h))
      have ch : c ∉ H := fun h => cc (mem_union_left _ h)
      exact noExtra x xh c ch (two_step_metric (fun h => ch (h ▸ xh))
        (fun edge => cq ((G.mem_neighborFinset _ _).mpr edge))
        ((G.mem_neighborFinset _ _).mp aq') e.symm)
  let Q := G.neighborFinset x
  have qs : Q ⊆ S := neighbor_subset (G:=G) xj
  let R := univ \ (J ∪ S)
  let B := R ∩ neighbors G Q
  have br : B ⊆ R := inter_subset_left
  have rj {a : V} (ar : a ∈ R) : a ∉ J := fun aj =>
    (mem_sdiff.mp ar).2 (mem_union_left _ aj)
  have rs {a : V} (ar : a ∈ R) : a ∉ S := fun as' =>
    (mem_sdiff.mp ar).2 (mem_union_right _ as')
  have bTwo (a : V) (ab : a ∈ B) : G.dist x a = 2 := by
    obtain ⟨ar,h⟩ := mem_inter.mp ab
    obtain ⟨q,qq,qa⟩ := mem_neighbors.mp h
    exact two_step_metric (fun e => rj ar (e ▸ xj))
      (fun e => rs ar (mem_neighbors.mpr ⟨x,xj,e⟩))
      ((G.mem_neighborFinset _ _).mp qq) qa.symm
  have both : Disjoint (J.erase x) B := disjoint_left.mpr fun _ aj ab =>
    rj (br ab) (mem_of_mem_erase aj)
  have total := even_bound (G:=G) (X:=J.erase x ∪ B)
    (by simp only [mem_union,not_or]; exact ⟨notMem_erase _ _,fun h => rj (br h) xj⟩) (by
      intro a ha
      rcases mem_union.mp ha with h | h
      · obtain ⟨ne,aj⟩ := mem_erase.mp h
        rw [allTwo a aj ne]
        decide
      · rw [bTwo a h]
        decide) (cap x)
  rw [card_union_of_disjoint both,card_erase_of_mem xj] at total
  let T := (S \ Q) ∪ B
  have tcard : T.card < G.vertexConnectivity := by
    have t := card_union_le (S \ Q) B
    have sq := card_sdiff_add_card_eq_card qs
    have qsz : Q.card = G.degree x := G.card_neighborFinset_eq_degree _
    change S.card ≤ J.card+g at small
    change (S \ Q ∪ B).card < G.vertexConnectivity
    change J.card-1+B.card ≤ k at total
    omega
  have rsub : R ⊆ B := by
    intro a ar
    by_contra na
    let U : Set V := {v | v ∉ T}
    have aliveX : x ∈ U := fun h => (mem_union.mp h).elim
      (fun h => disjoint_left.mp js xj (mem_sdiff.mp h).1)
      (fun h => rj (br h) xj)
    have aliveA : a ∈ U := fun h => (mem_union.mp h).elim
      (fun h => rs ar (mem_sdiff.mp h).1) na
    have notA : a ∉ J ∪ Q := fun h => (mem_union.mp h).elim (rj ar) (fun q => rs ar (qs q))
    have conn : (G.induce U).Connected := connected_after_smaller_deletion T tcard
    obtain ⟨p⟩ := conn ⟨x,aliveX⟩ ⟨a,aliveA⟩
    obtain ⟨u,v,uu,vnot,e,_⟩ := Graph189CutSides.walk_exits
      (fun v : U => v.val ∈ J ∪ Q) p (mem_union_left _ xj) notA
    have vj : v.val ∉ J := fun h => vnot (mem_union_left _ h)
    have vs : v.val ∉ S := fun h =>
      v.property (mem_union_left _ (mem_sdiff.mpr ⟨h,fun vq => vnot (mem_union_right _ vq)⟩))
    have vr : v.val ∈ R := mem_sdiff.mpr ⟨mem_univ _,fun h => (mem_union.mp h).elim vj vs⟩
    rcases mem_union.mp uu with j | q
    · exact vs (mem_neighbors.mpr ⟨u.val,j,e⟩)
    · exact v.property (mem_union_right _ (mem_inter.mpr ⟨vr,mem_neighbors.mpr ⟨u.val,q,e⟩⟩))
  have same : R.card = B.card := congrArg Finset.card (Subset.antisymm rsub br)
  have sumN := card_sdiff_add_card_eq_card (subset_univ (J ∪ S))
  rw [card_univ,card_union_of_disjoint js] at sumN
  change R.card+_ = _ at sumN
  change 2*k+g+3 ≤ Fintype.card V at order
  change S.card ≤ J.card+g at small
  omega

/-- Quantitative expansion implies Hall's inequality for all remaining
subsets after any deletion of at most the proved surplus. -/
theorem hall_after_deletion (hc : G.Connected)
    (cap : ∀ x, G.distEven x ≤ G.secondSmallestDegree+1) {g : ℕ}
    (connected : g+2 ≤ G.vertexConnectivity)
    (order : 2*G.secondSmallestDegree+g+3 ≤ Fintype.card V)
    (I D : Finset V) (survives : Disjoint I D) (deleted : D.card ≤ g+1) :
    I.card ≤ (neighbors G I \ D).card := by
  classical
  let S := neighbors G I
  let F := I \ S
  let T := S \ D
  have independent (x : V) (hx : x ∈ F) (y : V) (hy : y ∈ F) : ¬G.Adj x y := by
    intro edge
    exact (mem_sdiff.mp hy).2 (mem_neighbors.mpr ⟨x,(mem_sdiff.mp hx).1,edge⟩)
  have nsub : neighbors G F \ D ⊆ T \ I := by
    intro y hy
    obtain ⟨yn,yd⟩ := mem_sdiff.mp hy
    obtain ⟨x,xf,xy⟩ := mem_neighbors.mp yn
    refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨mem_neighbors.mpr ⟨x,(mem_sdiff.mp xf).1,xy⟩,yd⟩,?_⟩
    intro yi
    exact (mem_sdiff.mp xf).2 (mem_neighbors.mpr ⟨y,yi,xy.symm⟩)
  have fbound : F.card ≤ (T \ I).card := by
    by_cases fn : F.Nonempty
    · have expand := expansion hc cap connected order F fn independent
      have loss := card_le_card_sdiff_add_card (s:=neighbors G F) (t:=D)
      have upper := card_le_card nsub
      omega
    · rw [not_nonempty_iff_eq_empty.mp fn,card_empty]
      exact Nat.zero_le _
  have inter : T ∩ I = I ∩ S := by
    ext x
    simp only [T,mem_inter,mem_sdiff]
    exact ⟨fun h => ⟨h.2,h.1.1⟩,fun h => ⟨⟨h.2,fun xd =>
      disjoint_left.mp survives h.1 xd⟩,h.1⟩⟩
  have first := card_sdiff_add_card_inter I S
  have second := card_sdiff_add_card_inter T I
  rw [inter] at second
  change F.card+(I ∩ S).card = I.card at first
  change I.card ≤ T.card
  omega

#print axioms expansion
#print axioms hall_after_deletion

end Graph189IndependentExpansion
