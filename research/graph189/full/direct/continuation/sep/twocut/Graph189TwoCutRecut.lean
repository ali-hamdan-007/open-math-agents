import Graph189PositiveEvenCut

namespace Graph189TwoCutRecut
open Finset SimpleGraph Graph189PositiveEvenCut
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [Nontrivial V] [DecidableRel G.Adj] in
private theorem two (hc : G.Connected) {x a y : V} (ne : x≠y)
    (no : ¬G.Adj x y) (xa : G.Adj x a) (ay : G.Adj a y) : G.dist x y=2 := by
  have lo := (hc x y).one_lt_dist_of_ne_of_not_adj ne no
  have hi := G.dist_le (Walk.cons xa (.cons ay .nil))
  change G.dist x y≤2 at hi
  omega

omit [Nontrivial V] [DecidableRel G.Adj] in
private theorem two_mem (hc : G.Connected) {x a y : V} (ne : x≠y)
    (no : ¬G.Adj x y) (xa : G.Adj x a) (ay : G.Adj a y) : y∈evenOthers G x :=
  mem_even_others ne.symm (by rw [two hc ne no xa ay]; exact ⟨1,rfl⟩)

variable {A B U W : Finset V} {p q g : V}

omit [Fintype V] [Nontrivial V] [DecidableRel G.Adj] in
/-- The actual distance between the two arms is at least three, except at
neighbors of the unique gate. A length-three route must start via the gate. -/
theorem opposite_arm_distances (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B {p,q})
    (split : B=insert g (U∪W)) (ud : Disjoint U W) (gU : g∉U)
    (noCross : ∀ u∈U, ∀ w∈W, ¬G.Adj u w)
    (uq : ∀ u∈U, ¬G.Adj u q) (wp : ∀ w∈W, ¬G.Adj w p) (pq : ¬G.Adj p q)
    {f x : V} (fw : f∈W) (xu : x∈U) (gx : ¬G.Adj g x) :
    3≤G.dist f x ∧ (G.dist f x=3 → G.dist g x=2) := by
  classical
  have Ub : U⊆B := by intro u hu; rw [split]; exact mem_insert_of_mem (mem_union_left W hu)
  have Wb : W⊆B := by intro w hw; rw [split]; exact mem_insert_of_mem (mem_union_right U hw)
  have xd : ∀ {t}, G.Adj t x → t∈U ∨ t=p := by
    intro t edge
    rcases sides.cover t with ta|tb|ts
    · exact (sides.no_cross t ta x (Ub xu) edge).elim
    · rw [split] at tb
      rcases mem_insert.mp tb with rfl|tm
      · exact (gx edge).elim
      rcases mem_union.mp tm with tu|tw
      · exact Or.inl tu
      · exact (noCross x xu t tw edge.symm).elim
    · rcases (show t=p ∨ t=q by simpa using ts) with rfl|rfl
      · exact Or.inr rfl
      · exact (uq x xu edge.symm).elim
  have fd : ∀ {t}, G.Adj f t → t=g ∨ t∈W ∨ t=q := by
    intro t edge
    rcases sides.cover t with ta|tb|ts
    · exact (sides.no_cross t ta f (Wb fw) edge.symm).elim
    · rw [split] at tb
      rcases mem_insert.mp tb with rfl|tm
      · exact Or.inl rfl
      rcases mem_union.mp tm with tu|tw
      · exact (noCross t tu f fw edge.symm).elim
      · exact Or.inr (Or.inl tw)
    · rcases (show t=p ∨ t=q by simpa using ts) with rfl|rfl
      · exact (wp f fw edge).elim
      · exact Or.inr (Or.inr rfl)
  have ne : f≠x := fun eq => disjoint_left.mp ud xu (eq ▸ fw)
  have non : ¬G.Adj f x := fun e => noCross x xu f fw e.symm
  have twoLower := (hc f x).one_lt_dist_of_ne_of_not_adj ne non
  have wlen : ∃ P : G.Walk f x, P.length=G.dist f x := (hc f x).exists_walk_length_eq_dist
  constructor
  · by_contra! short
    obtain ⟨P,lp⟩ := wlen
    have len : P.length=2 := by omega
    have first : G.Adj f (P.getVert 1) := by
      simpa using P.adj_getVert_succ (show 0<P.length by omega)
    have tail : G.Adj (P.getVert 1) x := by
      have eq : P.getVert 2=x := by rw [←len,P.getVert_length]
      simpa only [eq] using P.adj_getVert_succ (show 1<P.length by omega)
    rcases xd tail with hu|hp
    · exact noCross _ hu f fw first.symm
    · exact wp f fw (hp ▸ first)
  · intro exactThree
    obtain ⟨P,lp⟩ := wlen
    have len : P.length=3 := lp.trans exactThree
    have first : G.Adj f (P.getVert 1) := by
      simpa using P.adj_getVert_succ (show 0<P.length by omega)
    have mid : G.Adj (P.getVert 1) (P.getVert 2) := by
      exact P.adj_getVert_succ (show 1<P.length by omega)
    have tail : G.Adj (P.getVert 2) x := by
      have eq : P.getVert 3=x := by rw [←len,P.getVert_length]
      simpa only [eq] using P.adj_getVert_succ (show 2<P.length by omega)
    have hit : P.getVert 1=g := by
      rcases fd first with ha|hw|hq
      · exact ha
      · rcases xd tail with hu|hp
        · exact (noCross _ hu _ hw mid.symm).elim
        · exact (wp _ hw (hp ▸ mid)).elim
      · rcases xd tail with hu|hp
        · exact (uq _ hu (hq ▸ mid.symm)).elim
        · exact (pq (by simpa only [hq,hp] using mid.symm)).elim
    exact two hc (fun eq => gU (eq.symm ▸ xu)) gx (hit ▸ mid) tail

/-- The two arm counts, including the extra anchor witness on whichever
row receives it, bound the order of the original graph by 3k+2. -/
theorem final_bound (hc : G.Connected) (cap : ∀ v, G.distEven v≤1+G.secondSmallestDegree)
    (sides : Graph189CutSides.CutSides G A B {p,q}) (split : B=insert g (U∪W))
    (ud : Disjoint U W) (gU : g∉U)
    (noCross : ∀ u∈U, ∀ w∈W, ¬G.Adj u w)
    (uq : ∀ u∈U, ¬G.Adj u q) (wp : ∀ w∈W, ¬G.Adj w p) (pq : ¬G.Adj p q)
    (aCommon : ∀ a∈A, G.secondSmallestDegree≤G.degree a → G.Adj a q)
    {f : V} (fw : f∈W) (fq : G.Adj f q) (fg : G.Adj f g)
    (highf : G.secondSmallestDegree≤G.degree f)
    (wbound : (W.filter (fun x => G.secondSmallestDegree≤G.degree x)).card +
      (if G.Adj g q then 1 else 0) + 1≤G.secondSmallestDegree) :
    Fintype.card V≤3*G.secondSmallestDegree+2 := by
  classical
  let k := G.secondSmallestDegree
  let Ah := A.filter (fun x => k≤G.degree x)
  let Uh := U.filter (fun x => k≤G.degree x)
  let Wh := W.filter (fun x => k≤G.degree x)
  let L := univ.filter (fun x => G.degree x<k)
  let T := Uh.filter (fun x => G.Adj g x ∨ G.dist f x=4)
  let R := Uh \ T
  have Ub : U⊆B := by intro u hu; rw [split]; exact mem_insert_of_mem (mem_union_left W hu)
  have Wb : W⊆B := by intro w hw; rw [split]; exact mem_insert_of_mem (mem_union_right U hw)
  have gb : g∈B := by rw [split]; exact mem_insert_self _ _
  have qs : q∈({p,q}:Finset V) := by simp
  have qB : q∉B := fun h => disjoint_left.mp sides.right_cut h qs
  have fA : Ah⊆evenOthers G f := by
    intro a ha
    obtain ⟨aa,ah⟩ := mem_filter.mp ha
    exact two_mem hc (fun eq => disjoint_left.mp sides.apart (eq.symm ▸ aa) (Wb fw))
      (fun e => sides.no_cross a aa f (Wb fw) e.symm) fq (aCommon a aa ah).symm
  have fT : T⊆evenOthers G f := by
    intro x hx
    obtain ⟨hu,edge|far⟩ := mem_filter.mp hx
    · have xu := (mem_filter.mp hu).1
      exact two_mem hc (fun eq => disjoint_left.mp ud (eq.symm ▸ xu) fw)
        (fun e => noCross x xu f fw e.symm) fg edge
    · exact mem_even_others (by rintro rfl; simp at far) (by rw [far]; exact ⟨2,rfl⟩)
  have dis : Disjoint Ah T := by
    apply Finset.disjoint_left.mpr
    intro x ha ht
    exact disjoint_left.mp sides.apart (mem_filter.mp ha).1
      (Ub (mem_filter.mp (mem_filter.mp ht).1).1)
  have fbound := (card_le_card (union_subset fA fT)).trans
    (even_others_card (by simpa only [Nat.add_comm 1] using cap f))
  rw [card_union_of_disjoint dis] at fbound
  have gR : R⊆evenOthers G g := by
    intro x hx
    obtain ⟨hu,nt⟩ := mem_sdiff.mp hx
    obtain ⟨xu,xh⟩ := mem_filter.mp hu
    have gx : ¬G.Adj g x := fun e => nt (mem_filter.mpr ⟨hu,Or.inl e⟩)
    have noFour : G.dist f x≠4 := fun e => nt (mem_filter.mpr ⟨hu,Or.inr e⟩)
    obtain ⟨lo,lift⟩ := opposite_arm_distances hc sides split ud gU noCross uq wp pq fw xu gx
    have hi := high_distance_four hc cap highf xh
    have eq := lift (by omega)
    exact mem_even_others (by rintro rfl; simp at eq) (by rw [eq]; exact ⟨1,rfl⟩)
  have gRow : (evenOthers G g).card≤k :=
    even_others_card (by simpa only [Nat.add_comm 1] using cap g)
  have gbound : R.card + (if G.Adj g q then 0 else 1)≤k := by
    split
    · exact (by simpa using (card_le_card gR).trans gRow)
    · rename_i non
      have gqne : g≠q := fun eq => qB (eq ▸ gb)
      have qEven := two_mem hc gqne non fg.symm fq
      have outside : q∉R := fun h => qB (Ub (mem_filter.mp (mem_sdiff.mp h).1).1)
      have sub : insert q R⊆evenOthers G g := by
        intro v hv
        rcases mem_insert.mp hv with rfl|hr
        · exact qEven
        · exact gR hr
      have le := (card_le_card sub).trans gRow
      rw [card_insert_of_notMem outside] at le
      exact le
  have part : R.card+T.card=Uh.card := by
    have sub : T⊆Uh := filter_subset _ _
    simpa only [inter_eq_right.mpr sub] using card_sdiff_add_card_inter Uh T
  have sum : Ah.card+Uh.card+Wh.card≤3*k-2 := by
    change Ah.card+T.card≤k at fbound
    change Wh.card+(if G.Adj g q then 1 else 0)+1≤k at wbound
    by_cases edge : G.Adj g q <;> simp only [edge,if_true,if_false] at gbound wbound <;> omega
  have low : L.card≤1 := by
    apply card_le_one.mpr
    intro x hx y hy
    by_contra ne
    obtain high|high := degree_pair (G:=G) x y ne
    · exact (not_lt_of_ge high) (mem_filter.mp hx).2
    · exact (not_lt_of_ge high) (mem_filter.mp hy).2
  have cover : (univ : Finset V)⊆((((Ah∪Uh)∪Wh)∪{p,q})∪{g})∪L := by
    intro v _
    by_cases ht : k≤G.degree v
    · apply mem_union_left
      rcases sides.cover v with va|vb|vs
      · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨va,ht⟩))))
      · rw [split] at vb
        rcases mem_insert.mp vb with rfl|vm
        · exact mem_union_right _ (mem_singleton_self _)
        rcases mem_union.mp vm with vu|vw
        · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨vu,ht⟩))))
        · exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨vw,ht⟩)))
      · exact mem_union_left _ (mem_union_right _ vs)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,Nat.lt_of_not_ge ht⟩)
  have bound := card_le_card cover
  rw [card_univ] at bound
  have pA := card_union_le Ah Uh
  have pB := card_union_le (Ah∪Uh) Wh
  have pS := card_union_le ((Ah∪Uh)∪Wh) ({p,q}:Finset V)
  have pG := card_union_le (((Ah∪Uh)∪Wh)∪({p,q}:Finset V)) ({g}:Finset V)
  have pL := card_union_le ((((Ah∪Uh)∪Wh)∪({p,q}:Finset V))∪({g}:Finset V)) L
  have ps : ({p,q}:Finset V).card≤2 := (card_insert_le p {q}).trans (by simp)
  have gs : ({g}:Finset V).card=1 := by simp
  change Fintype.card V≤3*k+2
  omega

omit [Nontrivial V] in
/-- A neighbor of the gate in the first arm sees the second arm and its own
label, with an extra charge whenever the gate contacts the other label. -/
theorem gate_arm_row (hc : G.Connected) (cap : ∀ v, G.distEven v≤1+G.secondSmallestDegree)
    (sides : Graph189CutSides.CutSides G A B {p,q}) (split : B=insert g (U∪W))
    (different : p≠q) (ud : Disjoint U W) (noCross : ∀ u∈U, ∀ w∈W, ¬G.Adj u w)
    (uq : ∀ u∈U, ¬G.Adj u q)
    (contacts : (A.filter (G.Adj p)).card+1=G.secondSmallestDegree)
    (many : 2≤(W.filter (G.Adj g)).card)
    {y u : V} (yu : G.Adj y u) (uc : u∈U) (yp : G.Adj y p) (ug : G.Adj u g) :
    (W.filter (G.Adj g)).card+(if G.Adj g q then 1 else 0)+1≤G.secondSmallestDegree := by
  classical
  let k := G.secondSmallestDegree
  let D := W.filter (G.Adj g)
  let P := A.filter (G.Adj p)
  have Ub : U⊆B := by intro u hu; rw [split]; exact mem_insert_of_mem (mem_union_left W hu)
  have Wb : W⊆B := by intro w hw; rw [split]; exact mem_insert_of_mem (mem_union_right U hw)
  have ps : p∈({p,q}:Finset V) := by simp
  have qs : q∈({p,q}:Finset V) := by simp
  have pB : p∉B := fun hp => disjoint_left.mp sides.right_cut hp ps
  have qB : q∉B := fun hq => disjoint_left.mp sides.right_cut hq qs
  have cap' : (evenOthers G u).card≤k :=
    even_others_card (by simpa only [Nat.add_comm 1] using cap u)
  have row : D⊆evenOthers G u := by
    intro w dw
    obtain ⟨ww,gw⟩ := mem_filter.mp dw
    exact two_mem hc (fun eq => disjoint_left.mp ud uc (eq.symm ▸ ww))
      (noCross u uc w ww) ug gw
  have up : ¬G.Adj u p := by
    intro edge
    have other : P⊆evenOthers G u := by
      intro a ap
      obtain ⟨aa,ha⟩ := mem_filter.mp ap
      exact two_mem hc (fun eq => disjoint_left.mp sides.apart aa (eq ▸ Ub uc))
        (fun e => sides.no_cross a aa u (Ub uc) e.symm) edge ha
    have separate : Disjoint P D := by
      apply Finset.disjoint_left.mpr
      intro v hv hd
      exact disjoint_left.mp sides.apart (mem_filter.mp hv).1 (Wb (mem_filter.mp hd).1)
    have count := (card_le_card (union_subset other row)).trans cap'
    rw [card_union_of_disjoint separate] at count
    change P.card+1=k at contacts
    change 2≤D.card at many
    omega
  have pe : p∈evenOthers G u :=
    two_mem hc (fun eq => pB (eq ▸ Ub uc)) up yu.symm yp
  have addP : insert p D⊆evenOthers G u := by
    intro v hv
    rcases mem_insert.mp hv with rfl|hd
    · exact pe
    · exact row hd
  have np : p∉D := fun h => pB (Wb (mem_filter.mp h).1)
  change D.card+(if G.Adj g q then 1 else 0)+1≤k
  by_cases gq : G.Adj g q
  · have qe : q∈evenOthers G u :=
      two_mem hc (fun eq => qB (eq ▸ Ub uc)) (uq u uc) ug gq
    have more : insert q (insert p D)⊆evenOthers G u := by
      intro v hv
      rcases mem_insert.mp hv with rfl|hp
      · exact qe
      · exact addP hp
    have nq : q∉insert p D := by
      intro h
      rcases mem_insert.mp h with eq|hd
      · exact different eq.symm
      · exact qB (Wb (mem_filter.mp hd).1)
    have count := (card_le_card more).trans cap'
    rw [card_insert_of_notMem nq,card_insert_of_notMem np] at count
    simpa only [if_pos gq] using count
  · have count := (card_le_card addP).trans cap'
    rw [card_insert_of_notMem np] at count
    simpa only [if_neg gq,add_zero] using count

/-- The far arm's q-contacts cannot consist of just the low vertex. Its
contact triangle would have to use the gate, exceeding the reserved row. -/
theorem exists_high_q_contact (sides : Graph189CutSides.CutSides G A B {p,q})
    (split : B=insert g (U∪W))
    (noCross : ∀ u∈U, ∀ w∈W, ¬G.Adj u w) (wp : ∀ w∈W, ¬G.Adj w p)
    (hasTriangle : ∀ u v, G.Adj u v → ∃ t, G.Adj u t ∧ G.Adj v t)
    (highGate : ∀ w∈W, G.secondSmallestDegree≤G.degree w → G.Adj g w)
    (many : G.secondSmallestDegree≤(W.filter (fun w => G.secondSmallestDegree≤G.degree w)).card+2)
    (wbound : (W.filter (G.Adj g)).card+(if G.Adj g q then 1 else 0)+1≤G.secondSmallestDegree)
    (contact : ∃ w∈W, G.Adj w q) :
    ∃ f∈W, G.Adj f q ∧ G.secondSmallestDegree≤G.degree f := by
  classical
  let k := G.secondSmallestDegree
  let H := W.filter (fun w => k≤G.degree w)
  let D := W.filter (G.Adj g)
  have Wb : W⊆B := by intro w hw; rw [split]; exact mem_insert_of_mem (mem_union_right U hw)
  obtain ⟨z,zw,zq⟩ := contact
  by_cases high : k≤G.degree z
  · exact ⟨z,zw,zq,high⟩
  obtain ⟨t,qt,zt⟩ := hasTriangle q z zq.symm
  have gateImpossible (gq : G.Adj g q) (gz : G.Adj g z) : False := by
    have absent : z∉H := fun h => high (mem_filter.mp h).2
    have sub : insert z H⊆D := by
      intro v hv
      rcases mem_insert.mp hv with rfl|hh
      · exact mem_filter.mpr ⟨zw,gz⟩
      · obtain ⟨vw,vh⟩ := mem_filter.mp hh
        exact mem_filter.mpr ⟨vw,highGate v vw vh⟩
    have count := card_le_card sub
    rw [card_insert_of_notMem absent] at count
    change D.card + (if G.Adj g q then 1 else 0) + 1≤k at wbound
    rw [if_pos gq] at wbound
    change k≤H.card+2 at many
    omega
  rcases sides.cover t with ta|tb|ts
  · exact (sides.no_cross t ta z (Wb zw) zt.symm).elim
  · rw [split] at tb
    rcases mem_insert.mp tb with rfl|tm
    · exact (gateImpossible qt.symm zt.symm).elim
    rcases mem_union.mp tm with tu|tw
    · exact (noCross t tu z zw zt.symm).elim
    · exact ⟨t,tw,qt.symm,(degree_pair (G:=G) z t zt.ne).resolve_left high⟩
  · rcases (show t=p ∨ t=q by simpa using ts) with rfl|rfl
    · exact (wp z zw zt).elim
    · exact (G.loopless.irrefl _ qt).elim

#print axioms exists_high_q_contact
#print axioms gate_arm_row
#print axioms opposite_arm_distances
#print axioms final_bound
end Graph189TwoCutRecut
