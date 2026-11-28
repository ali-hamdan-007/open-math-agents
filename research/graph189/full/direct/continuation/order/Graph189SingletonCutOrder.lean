import Graph189ThreeLargeComponents

open SimpleGraph Finset Graph189CutSides
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189SingletonCutOrder
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Any nonempty region whose exterior boundary separates it from a surviving
vertex has at least as many boundary vertices as the vertex connectivity. -/
private theorem boundary (D T : Finset V) (d : D.Nonempty) (dt : Disjoint D T)
    (z : V) (zd : z∉D) (zt : z∉T) (closed : ∀ x∈D, ∀ y, G.Adj x y → y∉D → y∈T) :
    G.vertexConnectivity ≤ T.card := by
  by_contra! short
  obtain ⟨x,hx⟩ := d
  let U : Set V := {v | v∉T}
  have hxU : x∈U := fun h => disjoint_left.mp dt hx h
  have con := connected_after_smaller_deletion (G:=G) T short
  obtain ⟨p⟩ := con (⟨x,hxU⟩ : U) (⟨z,zt⟩ : U)
  obtain ⟨a,b,ad,bd,e,_⟩ := walk_exits (G:=G.induce U) (fun t : U => t.val∈D) p hx zd
  exact b.property (closed a.val ad b.val e bd)

private theorem positive_budget (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (x : V) (T : Finset V) (out : x∉T) (ev : ∀ y∈T, Even (G.dist x y)) :
    T.card ≤ G.secondSmallestDegree := by
  classical
  have sub : insert x T ⊆ univ.filter (fun v => Even (G.dist x v)) := by
    intro y hy
    rcases mem_insert.mp hy with rfl | h
    · simp
    · exact mem_filter.mpr ⟨mem_univ _,ev y h⟩
  have cnt := (card_le_card sub).trans (cap x)
  rwa [card_insert_of_notMem out,Nat.add_le_add_iff_right] at cnt

private theorem switch (A B : Finset V) :
    (∑ a ∈ A, (B.filter (G.Adj a)).card) = ∑ b ∈ B, (A.filter (fun a => G.Adj a b)).card := by
  simp only [card_eq_sum_ones,sum_filter]
  exact sum_comm

private theorem deficits (S : Finset V) (L R : Finset V) (lr : Disjoint L R)
    (spos : 0<S.card) (l : L.card=S.card) (r : R.card=S.card)
    {k a b : ℕ} (aCap : a≤k) (bCap : b≤k)
    (row : ∀ u∈S, S.card ≤ ((L∪R).filter (G.Adj u)).card)
    (left : ∀ v∈L, (S.filter (fun u => G.Adj u v)).card ≤ k-b)
    (right : ∀ v∈R, (S.filter (fun u => G.Adj u v)).card ≤ k-a) :
    S.card+a+b ≤ 2*k := by
  have rS := sum_le_sum row
  have cL := sum_le_sum left
  have cR := sum_le_sum right
  rw [switch,Finset.sum_union lr] at rS
  simp only [sum_const,smul_eq_mul,l,r] at rS cL cR
  have cmp : S.card*S.card ≤ S.card*((k-b)+(k-a)) := by
    rw [Nat.mul_add]
    omega
  have := Nat.le_of_mul_le_mul_left cmp spos
  omega

/-- The two nonempty sides outside a singleton component and its neighbors. -/
structure Split (G : SimpleGraph V) [DecidableRel G.Adj] (z : V) (S : Finset V)
    (W : Bool → Finset V) : Prop where
  neighbors : G.neighborFinset z=S
  connectivity : S.card≤G.vertexConnectivity
  nonempty : ∀ i, (W i).Nonempty
  apart : ∀ i, Disjoint (W i) (W (!i))
  wcut : ∀ i, Disjoint (W i) S
  notz : ∀ i, z∉W i
  closed : ∀ i, ∀ u∈W i, ∀ v, G.Adj u v → v∉W i → v∈S
  cover : ∀ u, u=z ∨ u∈S ∨ u∈W false ∨ u∈W true

noncomputable def ports (G : SimpleGraph V) (S W : Finset V) : Finset V := by
  classical
  exact W.filter (fun v => ∃ u∈S, G.Adj v u)

/-- If deleting a minimum separator leaves the singleton z and two other
components, their ports and remote vertices give n≤3k+1. The two sides
may themselves be unions of components. -/
theorem population (hc : G.Connected) (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (z : V) (S : Finset V) (W : Bool → Finset V) (split : Split G z S W)
    (two : 2≤S.card) (wide : 2*S.card ≤ G.secondSmallestDegree+1)
    : Fintype.card V ≤ 3*G.secondSmallestDegree+1 ∧
      (∀ i, S.card≤(ports G S (W i)).card) ∧
      (ports G S (W false)).card + (ports G S (W true)).card ≤ G.secondSmallestDegree ∧
      (∀ i, ((W i)\ports G S (W i)).card<G.secondSmallestDegree) := by
  classical
  obtain ⟨ns,sc,nonempty,apart,wcut,notz,closed,cover⟩ := split
  let k := G.secondSmallestDegree
  let P (i : Bool) := (W i).filter (fun v => ∃ u∈S, G.Adj v u)
  let D (i : Bool) := W i \ P i
  let F (i : Bool) := (P i).filter (fun v => ∃ x∈D i, G.Adj x v)
  let B := P false∪P true
  have ports_eq (i : Bool) : ports G S (W i)=P i := by ext v; simp [P,ports]
  have pos : 0<S.card := by omega
  have dz : G.degree z = S.card := by rw [←ns,G.card_neighborFinset_eq_degree]
  have zS : z∉S := by simp [←ns]
  have az (u : V) : G.Adj z u ↔ u∈S := by rw [←ns,G.mem_neighborFinset]
  have pW (i : Bool) : P i ⊆ W i := filter_subset _ _
  have dW (i : Bool) : D i ⊆ W i := sdiff_subset
  have fP (i : Bool) : F i ⊆ P i := filter_subset _ _
  have piB (i : Bool) : P i ⊆ B := by cases i <;> simp [B]
  have high {u : V} (ne : u≠z) : k≤G.degree u := by
    rcases degree_pair (G:=G) u z ne with h|h
    · exact h
    · change k≤G.degree z at h
      change 2*S.card≤k+1 at wide
      omega
  have noPort (i : Bool) {x : V} (hx : x∈D i) {u : V} (hu : u∈S) : ¬G.Adj x u := by
    exact fun e => (mem_sdiff.mp hx).2 (mem_filter.mpr ⟨dW i hx,u,hu,e⟩)
  have allB : B.card≤k := by
    apply positive_budget cap z
    · intro hz
      rcases mem_union.mp hz with h|h
      · exact notz false (pW false h)
      · exact notz true (pW true h)
    · intro y hy
      have single (i : Bool) (h : y∈P i) : Even (G.dist z y) := by
        obtain ⟨yw,u,uS,e⟩ := mem_filter.mp h
        have ne : z≠y := fun h => notz i (h ▸ yw)
        have no : ¬G.Adj z y := fun h => disjoint_left.mp (wcut i) yw ((az y).mp h)
        rw [Graph189LowDegreeTwo.two_edges ((az u).mpr uS) e.symm ne no]
        decide
      exact (mem_union.mp hy).elim (single false) (single true)
  have sizeW (i : Bool) : k+1 ≤ S.card+(W i).card := by
    obtain ⟨x,hx⟩ := nonempty i
    have deg := high (fun eq => notz i (eq ▸ hx))
    have sub : insert x (G.neighborFinset x) ⊆ S∪W i := by
      intro y hy
      rcases mem_insert.mp hy with rfl|e
      · exact mem_union_right _ hx
      by_cases yw : y∈W i
      · exact mem_union_right _ yw
      · exact mem_union_left _ (closed i x hx y ((G.mem_neighborFinset _ _).mp e) yw)
    have h := (card_le_card sub).trans (card_union_le S (W i))
    rw [card_insert_of_notMem (by simp),G.card_neighborFinset_eq_degree] at h
    omega
  have enoughP (i : Bool) : S.card ≤ (P i).card := by
    obtain ⟨T,sub,sz,f,edges⟩ := Graph189ExteriorGap.matching_at_component_boundary S (W i)
      (wcut i).symm (fun x hx y hy e => closed i x hx y e hy) le_rfl
      (show S.card≤(W i).card by have h:=sizeW i; change 2*S.card≤k+1 at wide; omega)
      (fun C short => connected_after_smaller_deletion C (short.trans_le sc))
    let g : T ↪ P i := ⟨fun u => ⟨(f u).val,mem_filter.mpr
      ⟨(f u).property,u.val,sub u.property,(edges u).symm⟩⟩,fun _ _ e =>
        f.injective (Subtype.ext (congrArg (fun v : P i => v.val) e))⟩
    exact sz.trans (by simpa using Fintype.card_le_of_injective g g.injective)
  have pb (i : Bool) : (P i).card+(P (!i)).card = B.card := by
    have dj := (apart i).mono (pW i) (pW (!i))
    rw [←card_union_of_disjoint dj]
    cases i <;> simp [B,Finset.union_comm]
  have dPos (i : Bool) : (D i).Nonempty := by
    apply card_pos.mp
    have h := sizeW i
    have j := enoughP (!i)
    have total := pb i
    change 0<(W i\P i).card
    rw [card_sdiff_of_subset (pW i)]
    omega
  have fSize (i : Bool) : S.card≤(F i).card := by
    apply sc.trans
    apply boundary (D i) (F i) (dPos i) (z:=z)
    · exact disjoint_left.mpr fun _ hd hf => (mem_sdiff.mp hd).2 (fP i hf)
    · exact fun h => notz i (dW i h)
    · exact fun h => notz i (pW i (fP i h))
    · intro x hx y e notD
      have yw : y∈W i := by by_contra out; exact noPort i hx (closed i x (dW i hx) y e out) e
      have yp : y∈P i := by by_contra no; exact notD (mem_sdiff.mpr ⟨yw,no⟩)
      exact mem_filter.mpr ⟨yp,x,hx,e⟩
  have four (i : Bool) {x y : V} (hx : x∈D i) (hy : y∈D (!i)) : G.dist x y=4 := by
    obtain ⟨p,len⟩ := (hc x y).exists_walk_length_eq_dist
    have other : y∉W i := fun h => disjoint_left.mp (apart i) h (dW (!i) hy)
    obtain ⟨a,u,aw,uw,e,mem⟩ := walk_exits (·∈W i) p (dW i hx) other
    have us := closed i a aw u e uw
    have leg (j : Bool) {v : V} (vh : v∈D j) : 2≤G.dist v u := by
      have nz : G.dist v u≠0 := fun h => disjoint_left.mp (wcut j) (dW j vh) ((hc.dist_eq_zero_iff.mp h).symm ▸ us)
      have no : G.dist v u≠1 := fun h => noPort j vh us (dist_eq_one_iff_adj.mp h)
      omega
    have e₁ := leg i hx
    have e₂ := leg (!i) hy
    rw [G.dist_comm (u:=y) (v:=u)] at e₂
    have h₁ := G.dist_le (p.takeUntil u mem)
    have h₂ := G.dist_le (p.dropUntil u mem)
    have sum := congrArg SimpleGraph.Walk.length (Walk.take_spec p mem)
    rw [Walk.length_append] at sum
    have hi := high (fun eq => notz i (eq ▸ dW i hx))
    have hj := high (fun eq => notz (!i) (eq ▸ dW (!i) hy))
    have upper := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc) (u:=x) (v:=y)).trans
      (diameter_le_five hc (fun v => (cap v).trans_eq (Nat.add_comm _ _)))
    have notFive : G.dist x y≠5 := fun h => by
      rcases five_endpoints hc cap x y h with h|h
      · exact (not_lt_of_ge hi) h
      · exact (not_lt_of_ge hj) h
    omega
  have debit (i : Bool) {v : V} (hv : v∈F i) :
      (S.filter (fun u => G.Adj u v)).card + (D (!i)).card ≤ k := by
    obtain ⟨_,x,hx,e⟩ := mem_filter.mp hv
    let A := S.filter (fun u => G.Adj u v)
    have separate : Disjoint A (D (!i)) := (wcut (!i)).symm.mono (filter_subset _ _) (dW (!i))
    rw [←card_union_of_disjoint separate]
    apply positive_budget cap x
    · intro bad
      rcases mem_union.mp bad with h|h
      · exact disjoint_left.mp (wcut i) (dW i hx) (mem_filter.mp h).1
      · exact disjoint_left.mp (apart i) (dW i hx) (dW (!i) h)
    · intro y hy
      rcases mem_union.mp hy with ha|hd
      · obtain ⟨ys,edge⟩ := mem_filter.mp ha
        have ne : x≠y := fun eq => disjoint_left.mp (wcut i) (eq ▸ dW i hx) ys
        rw [Graph189LowDegreeTwo.two_edges e edge.symm ne (noPort i hx ys)]
        decide
      · rw [four i hx hd]
        decide
  choose T tf eqT using fun i => exists_subset_card_eq (fSize i)
  let M := T false ∪ T true
  have tm (i : Bool) : T i ⊆ B := (tf i).trans ((fP i).trans (piB i))
  have mi : M⊆B := Finset.union_subset (tm false) (tm true)
  have disT : Disjoint (T false) (T true) := (apart false).mono
    ((tf false).trans ((fP false).trans (pW false))) ((tf true).trans ((fP true).trans (pW true)))
  have szM : M.card = 2*S.card := by rw [show M=T false∪T true from rfl,card_union_of_disjoint disT,eqT,eqT]; omega
  have row (u : V) (hu : u∈S) : S.card≤(M.filter (G.Adj u)).card := by
    have h := high (fun e => zS (e ▸ hu))
    have sub : G.neighborFinset u ⊆ insert z (S.erase u) ∪ ((B\M)∪M.filter (G.Adj u)) := by
      intro v hv
      have e := (G.mem_neighborFinset _ _).mp hv
      rcases cover v with rfl|vs|vw|vw
      · exact mem_union_left _ (mem_insert_self _ _)
      · exact mem_union_left _ (mem_insert_of_mem (mem_erase.mpr ⟨e.ne.symm,vs⟩))
      all_goals
        have vb : v∈B := piB _ (mem_filter.mpr ⟨vw,u,hu,e.symm⟩)
        by_cases yes : v∈M
        · exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨yes,e⟩))
        · exact mem_union_right _ (mem_union_left _ (mem_sdiff.mpr ⟨vb,yes⟩))
    have cnt := (card_le_card sub).trans (card_union_le _ _)
    rw [G.card_neighborFinset_eq_degree] at cnt
    have inner := card_union_le (B\M) (M.filter (G.Adj u))
    have ext := card_insert_le z (S.erase u)
    rw [card_erase_of_mem hu] at ext
    rw [card_sdiff_of_subset mi] at inner
    have sB := card_le_card mi
    omega
  have dCap (i : Bool) : (D (!i)).card≤k := by
    obtain ⟨v,hv⟩ := card_pos.mp (pos.trans_le (fSize i))
    have h := debit i hv
    omega
  have total := deficits S (T false) (T true) disT pos (eqT false) (eqT true)
    (k:=k) (a:=(D false).card) (b:=(D true).card) (dCap true) (dCap false) row
    (fun v hv => by have h:=debit false (tf false hv); change _+(D true).card≤k at h; omega)
    (fun v hv => by have h:=debit true (tf true hv); change _+(D false).card≤k at h; omega)
  have all : univ⊆insert z (((S∪B)∪D false)∪D true) := by
    intro v _
    rcases cover v with rfl|hs|hw|hw
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_union_left _ (mem_union_left _ (mem_union_left _ hs)))
    · by_cases h : v∈P false
      · exact mem_insert_of_mem (mem_union_left _ (mem_union_left _ (mem_union_right _ (piB false h))))
      · exact mem_insert_of_mem (mem_union_left _ (mem_union_right _ (mem_sdiff.mpr ⟨hw,h⟩)))
    · by_cases h : v∈P true
      · exact mem_insert_of_mem (mem_union_left _ (mem_union_left _ (mem_union_right _ (piB true h))))
      · exact mem_insert_of_mem (mem_union_right _ (mem_sdiff.mpr ⟨hw,h⟩))
  have cnt := (card_le_card all).trans (card_insert_le _ _)
  rw [card_univ] at cnt
  have l₁ := card_union_le S B
  have l₂ := card_union_le (S∪B) (D false)
  have l₃ := card_union_le ((S∪B)∪D false) (D true)
  simp only [ports_eq]
  refine ⟨by change Fintype.card V≤3*k+1; omega,enoughP,by exact (pb false).le.trans allB,?_⟩
  have strict (i : Bool) : (D (!i)).card<k := by
    obtain ⟨v,hv⟩ := card_pos.mp (pos.trans_le (fSize i))
    obtain ⟨_,u,us,e⟩ := mem_filter.mp (fP i hv)
    have h := debit i hv
    have p : 0<(S.filter (fun t => G.Adj t v)).card := card_pos.mpr ⟨u,mem_filter.mpr ⟨us,e.symm⟩⟩
    omega
  intro i
  change (D i).card<k
  simpa using strict (!i)

#print axioms population
end Graph189SingletonCutOrder
