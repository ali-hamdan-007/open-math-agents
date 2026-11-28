import Graph189MaximumDegree
import Graph189HighThirdLayer
import Graph189ContactColumns

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189ThirdLayerDegreeCeiling
variable {V : Type*} {G : SimpleGraph V}

private theorem predecessor {x z : V} {j : ℕ} (hz : G.dist x z=j+1) :
    ∃ a, G.dist x a=j ∧ G.Adj a z := by
  have hr : G.dist z x=j+1 := by rwa [dist_comm]
  obtain ⟨walk,len⟩ := (Reachable.of_dist_ne_zero (by omega : G.dist z x≠0)).exists_walk_length_eq_dist
  cases walk with
  | nil => simp at hz
  | cons e tail =>
    rename_i a
    have ht : tail.length=j := by rw [Walk.length_cons,hr] at len; omega
    have le : G.dist x a≤j := by rw [dist_comm]; exact ht ▸ G.dist_le tail
    have := e.diff_dist_adj (u:=x)
    exact ⟨a,by omega,e.symm⟩

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- If the third layer outnumbers the second-layer budget, two distance-three
vertices share a predecessor. These two vertices and the root consume three
slots outside the root's neighborhood in its three-layer cover. -/
theorem degree_at_root (x : V) {k : ℕ}
    (quota : ∀ v, (univ.filter (fun w => G.dist v w=2)).card ≤ k)
    (C : Finset V) (layer : ∀ t∈C, G.dist x t=3) (many : k<C.card) :
    G.degree x+3≤3*k := by
  classical
  let D (v : V) := univ.filter (fun w => G.dist v w=2)
  have pick (t : C) : ∃ j : (D x), G.Adj j.val t.val := by
    obtain ⟨j,dist,edge⟩ := predecessor (j:=2) (layer t.val t.property)
    exact ⟨⟨j,mem_filter.mpr ⟨mem_univ _,dist⟩⟩,edge⟩
  choose f edge using pick
  have dup : ∃ t s : C, t≠s ∧ f t=f s := by
    by_contra! distinct
    have inj : Function.Injective f := fun a b eq => by
      by_contra ne
      exact distinct a b ne eq
    have card := card_le_card_of_injective inj
    have := quota x
    change _ ≤ (D x).card at card
    change (D x).card ≤ k at this
    omega
  obtain ⟨t,s,ne,eq⟩ := dup
  let j := (f t).val
  have dj : G.dist x j=2 := (mem_filter.mp (f t).property).2
  obtain ⟨i,di,ij⟩ := predecessor (j:=1) dj
  have xi := dist_eq_one_iff_adj.mp di
  have jt : G.Adj j t.val := edge t
  have js : G.Adj j s.val := by change G.Adj (f t).val s.val; rw [eq]; exact edge s
  have dt := layer t.val t.property
  have ds := layer s.val s.property
  let N := G.neighborFinset x
  let U := (D i ∪ D j) ∪ D t.val
  have front (a : C) (ja : G.Adj j a.val) : a.val∈D i := by
    have da := layer _ a.property
    apply mem_filter.mpr
    refine ⟨mem_univ _,two_step_metric (fun eq => by rw [←eq] at da; omega) (fun e => ?_) ij ja.symm⟩
    have := e.diff_dist_adj (u:=x)
    omega
  have near : N⊆U := by
    intro w hw
    have xw := (G.mem_neighborFinset _ _).mp hw
    have dw := dist_eq_one_iff_adj.mpr xw
    by_cases jw : G.Adj j w
    · apply mem_union_right
      apply mem_filter.mpr
      refine ⟨mem_univ _,two_step_metric (fun eq => by rw [eq] at dt; omega) (fun e => ?_) jt.symm jw.symm⟩
      have := e.diff_dist_adj (u:=x)
      omega
    by_cases iw : G.Adj i w
    · apply mem_union_left
      apply mem_union_right
      exact mem_filter.mpr ⟨mem_univ _,two_step_metric (fun eq => by rw [eq] at dj; omega) jw ij.symm iw.symm⟩
    apply mem_union_left
    apply mem_union_left
    exact mem_filter.mpr ⟨mem_univ _,two_step_metric (fun eq => by rw [eq] at ij; exact jw ij.symm) iw xi.symm xw.symm⟩
  have root : x∈D j := mem_filter.mpr ⟨mem_univ _,by rwa [SimpleGraph.dist_comm]⟩
  have all : insert x (insert t.val (insert s.val N)) ⊆ U := by
    intro w hw
    rcases mem_insert.mp hw with rfl|hw
    · exact mem_union_left _ (mem_union_right _ root)
    rcases mem_insert.mp hw with rfl|hw
    · exact mem_union_left _ (mem_union_left _ (front t jt))
    rcases mem_insert.mp hw with rfl|hw
    · exact mem_union_left _ (mem_union_left _ (front s js))
    exact near hw
  have nroot : x∉N := fun h => G.irrefl ((G.mem_neighborFinset _ _).mp h)
  have nt : t.val∉N := fun h => by have := dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset _ _).mp h); omega
  have ns : s.val∉N := fun h => by have := dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset _ _).mp h); omega
  have xt : x≠t.val := fun e => by rw [←e,SimpleGraph.dist_self] at dt; contradiction
  have xs : x≠s.val := fun e => by rw [←e,SimpleGraph.dist_self] at ds; contradiction
  have ts : t.val≠s.val := fun h => ne (Subtype.ext h)
  have pop := card_le_card all
  rw [card_insert_of_notMem (by simp [xt,xs,nroot]),card_insert_of_notMem (by simp [ts,nt]),card_insert_of_notMem ns] at pop
  have first := card_union_le (D i) (D j)
  have second := card_union_le (D i∪D j) (D t.val)
  have qi : (D i).card≤k := quota i
  have qj : (D j).card≤k := quota j
  have qt : (D t.val).card≤k := quota t.val
  change N.card+1+1+1 ≤ ((D i∪D j)∪D t.val).card at pop
  change N.card+3≤3*k
  omega

/-- The sharpened degree ceiling at orders exceeding 5k+2 under the exact
metric assumptions of the original conjecture. -/
theorem max_degree [Nontrivial V] (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (large : 5*G.secondSmallestDegree+2<Fintype.card V) :
    G.maxDegree+3≤3*G.secondSmallestDegree := by
  classical
  let k:=G.secondSmallestDegree
  obtain ⟨x,hx⟩ := G.exists_maximal_degree_vertex
  have point (v : V) : G.distEven v ≤ 1+k := (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have upper := Graph189DegreeCeiling.maxDegree_le_three_mul_secondSmallestDegree hc point
  let C := Graph189HighThirdLayer.highThird G x
  have count := Graph189HighThirdLayer.card_highThird_at_max hc cap x hx.symm
  change Fintype.card V-G.maxDegree-k-2≤C.card at count
  change G.maxDegree≤3*k at upper
  change 5*k+2<Fintype.card V at large
  rw [hx]
  apply degree_at_root x (C:=C) _ (fun t ht => (mem_filter.mp ht).2.1) (by omega : k<C.card)
  intro v
  let D := univ.filter (fun w => G.dist v w=2)
  have out : v∉D := by simp [D]
  have incl : insert v D ⊆ univ.filter (fun w => Even (G.dist v w)) := by
    intro w hw
    rcases mem_insert.mp hw with rfl|h
    · simp
    · exact mem_filter.mpr ⟨mem_univ _,by rw [(mem_filter.mp h).2]; decide⟩
  have cmp := card_le_card incl
  rw [card_insert_of_notMem out] at cmp
  change D.card+1≤G.distEven v at cmp
  have := point v
  change D.card≤k
  omega

end Graph189ThirdLayerDegreeCeiling
#print axioms Graph189ThirdLayerDegreeCeiling.max_degree
