import Graph189FiveCycleComponent
import Graph189FiveCycleTails
import Graph189FiveExteriorData

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189FiveCycleLarge
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Seven or more omissions cannot include a five-cycle in a qualifying
two-connected graph of second-smallest degree six and minimum degree three. -/
theorem excluded (hcG : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (degree : G.secondSmallestDegree=6) (conn : 2≤G.vertexConnectivity) (minimum : ∀ v, 3≤G.degree v)
    {a b r : V} (p : G.Walk a b) (hp : p.IsPath) (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (C : G.Walk r r) (hc : C.IsCycle) (five : C.length=5) (off : ∀ v∈C.support,v∉p.support)
    (size : 7≤p.support.toFinsetᶜ.card) : False := by
  classical
  let W := C.support.toFinset
  let E := p.support.toFinsetᶜ
  let F := E\W
  have wc : W.card=5 := (Graph189SixCycleExtra.cycle_card C hc).trans five
  have inc : W⊆E := fun v hv => mem_compl.mpr fun h => off v (List.mem_toFinset.mp hv) (List.mem_toFinset.mp h)
  have fsize := card_sdiff_add_card_eq_card inc
  change F.card+W.card=E.card at fsize
  change 7≤E.card at size
  have pop := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at pop
  change p.support.length+E.card=Fintype.card V at pop
  have path := Graph189TwoExteriorLinks.path_of_cycle p hp mx conn C hc off
  have point (v : V) : G.distEven v≤7 := by
    have bound := (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
    omega
  obtain ⟨z,sz⟩ := Graph189QuadraticOrder.second_attained (G:=G)
  have quad := Graph189QuadraticOrder.rooted hcG z 6 point
  rw [sz,degree] at quad
  have order : Fintype.card V≤25 := by omega
  have outside {v : V} (vf : v∈F) : v∉p.support ∧ v∉C.support :=
    ⟨fun h => (mem_compl.mp (mem_sdiff.mp vf).1) (List.mem_toFinset.mpr h),
      fun h => (mem_sdiff.mp vf).2 (List.mem_toFinset.mpr h)⟩
  have parts (v : V) : (G.neighborFinset v∩W).card+(G.neighborFinset v∩F).card=
      (G.neighborFinset v\p.support.toFinset).card := by
    rw [←card_union_of_disjoint (show Disjoint (G.neighborFinset v∩W) (G.neighborFinset v∩F) from
      disjoint_left.mpr (fun w hw hf => (mem_sdiff.mp (mem_inter.mp hf).2).2 (mem_inter.mp hw).2))]
    congr 1
    ext w
    simp only [mem_union,mem_inter,mem_sdiff]
    constructor
    · rintro (⟨ng,hW⟩|⟨ng,hE,hW⟩)
      · exact ⟨ng,mem_compl.mp (inc hW)⟩
      · exact ⟨ng,mem_compl.mp hE⟩
    · rintro ⟨ng,np⟩
      by_cases hW : w∈W
      · exact Or.inl ⟨ng,hW⟩
      · exact Or.inr ⟨ng,mem_compl.mpr np,hW⟩
  have quota (v : V) : (univ.filter (fun u => G.dist v u=2)).card≤6 := by
    let D := univ.filter (fun u => G.dist v u=2)
    have inc : insert v D⊆univ.filter (fun u => Even (G.dist v u)) := by
      intro u hu
      rcases mem_insert.mp hu with rfl|hu
      · simp
      · exact mem_filter.mpr ⟨mem_univ _,by simp [(mem_filter.mp hu).2]⟩
    have n := card_le_card inc
    rw [card_insert_of_notMem (by simp [D])] at n
    change D.card+1≤G.distEven v at n
    exact Nat.le_of_succ_le_succ (n.trans (point v))
  have unique {u v : V} (lu : G.degree u<6) (lv : G.degree v<6) : u=v := by
    by_contra ne
    have pair := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) u v ne
    omega
  have half {v u : V} (out : v∉p.support) (offU : u∉p.support) (edge : G.Adj v u) :
      G.degree v≤2*(G.neighborFinset v\p.support.toFinset).card := by
    by_cases hi : 6≤G.degree v
    · exact (high_exterior_half p hp mx out (quota v) hi minimum (fun _ _ => unique)).2
    have high : 6≤G.degree u := by by_contra! lo; exact edge.ne (unique (Nat.lt_of_not_ge hi) lo)
    exact half_degree_outside_longest p hp mx out offU edge (quota v) high
  have two (v : V) (vf : v∈F) : (G.neighborFinset v∩W).card≤2 :=
    (Graph189FiveCycleRing.outside_neighbors hcG cap degree conn p hp mx C hc five off (outside vf).1 (outside vf).2).1
  have minF (v : V) (vf : v∈F) (u : V) (uf : u∈F) (vu : G.Adj v u) :
      2≤(G.neighborFinset v∩W).card+(G.neighborFinset v∩F).card := by
    rw [parts]
    have h := half (outside vf).1 (outside uf).1 vu
    have := minimum v
    omega
  have anchors (x y : F) (ne : x≠y) (reach : (G.induce (F : Set V)).Reachable x y)
      (u : V) (uw : u∈W) (v : V) (vw : v∈W) (ux : G.Adj u x.val) (yv : G.Adj y.val v) : u=v :=
    Graph189FiveCycleLinks.same_anchor p C hc five off (fun T hT away =>
      Graph189SixCycleExtra.five_bound hcG cap degree conn p hp mx T hT away) F (fun _ h => outside h)
      ne reach (List.mem_toFinset.mp uw) (List.mem_toFinset.mp vw) ux yv
  obtain ⟨u,uf,v,vf,uv⟩ := one_lt_card.mp (show 1<F.card by omega)
  obtain ⟨w,wf,high⟩ : ∃w∈F, 6≤G.degree w := by
    have pair := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) u v uv
    rcases pair with h|h
    · exact ⟨u,uf,by omega⟩
    · exact ⟨v,vf,by omega⟩
  have three := Graph189FiveCycleLinks.component_three W F two minF anchors ⟨w,wf⟩ (by
    rw [parts]
    have h := (high_exterior_half p hp mx (outside wf).1 (quota _) high minimum (fun _ _ => unique)).2
    omega)
  have nF : 3≤F.card := three.trans (card_le_card (filter_subset _ _))
  have min5 (v : V) : 5≤G.degree v := by have q := Graph189QuadraticOrder.rooted hcG v 6 point; omega
  have strong (v : V) (vf : v∈F) (touch : ∃ u∈W,G.Adj u v) :
      3≤(G.neighborFinset v∩W).card+(G.neighborFinset v∩F).card := by
    obtain ⟨u,uw,uv⟩ := touch
    rw [parts]
    have h := half (outside vf).1 (off u (List.mem_toFinset.mp uw)) uv.symm
    have := min5 v
    omega
  let A := W.filter (fun c => ∃ v∈F,G.Adj c v)
  obtain ⟨few,tails⟩ := Graph189FiveCycleComponent.layout W F (by omega) two minF strong anchors
  change A.card≤2 at few
  change ∀ c∈A, ∃ x∈F, ∃ y∈F, G.Adj c x ∧ G.Adj x y at tails
  rcases A.eq_empty_or_nonempty with empty|⟨c,cA⟩
  · have close (u : V) (uw : u∈W) (v : V) (uv : G.Adj u v) (vw : v∉W) : v∈p.support := by
      by_contra missing
      have vf : v∈F := mem_sdiff.mpr ⟨mem_compl.mpr (fun h => missing (List.mem_toFinset.mp h)),vw⟩
      have hit : u∈A := mem_filter.mpr ⟨uw,v,vf,uv⟩
      rw [empty] at hit
      exact notMem_empty _ hit
    obtain ⟨_,_,_,_,_,small⟩ := Graph189FiveExteriorData.window p W close hcG degree point wc (by
      intro M n f edges
      have large := Graph189FiveCycleContacts.triple p hp mx C hc five off M n f edges
      omega)
    omega
  let D := (W\A).filter (fun v => 6≤G.degree v)
  have rich : 2≤D.card := by
    have h1 := card_sdiff_add_card_eq_card (show A⊆W from filter_subset _ _)
    have h2 := card_sdiff_add_card_eq_card (show D⊆W\A from filter_subset _ _)
    have one : ((W\A)\D).card≤1 := by
      apply card_le_one.mpr
      intro u hu v hv
      apply unique
      · by_contra! high
        exact (mem_sdiff.mp hu).2 (mem_filter.mpr ⟨(mem_sdiff.mp hu).1,high⟩)
      · by_contra! high
        exact (mem_sdiff.mp hv).2 (mem_filter.mpr ⟨(mem_sdiff.mp hv).1,high⟩)
    omega
  have row (v : V) (vd : v∈D) : 2≤(contactPositions p v).card := by
    obtain ⟨va,hi⟩ := mem_filter.mp vd
    obtain ⟨vw,vA⟩ := mem_sdiff.mp va
    have none : G.neighborFinset v∩F=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro u hu
      exact vA (mem_filter.mpr ⟨vw,u,(mem_inter.mp hu).2,(G.mem_neighborFinset _ _).mp (mem_inter.mp hu).1⟩)
    have h := parts v
    rw [none,card_empty,add_zero] at h
    have ub := card_le_card (show G.neighborFinset v∩W⊆W.erase v from fun u hu => mem_erase.mpr
      ⟨((G.mem_neighborFinset _ _).mp (mem_inter.mp hu).1).ne.symm,(mem_inter.mp hu).2⟩)
    rw [card_erase_of_mem vw,wc] at ub
    have eq := card_sdiff_add_card_inter (G.neighborFinset v) p.support.toFinset
    rw [G.card_neighborFinset_eq_degree,←contact_card_neighbors p hp] at eq
    omega
  obtain ⟨d,dD,e,eD,de⟩ := one_lt_card.mp rich
  obtain ⟨x,xf,y,yf,cx,xy⟩ := tails c cA
  have Dloc {v} (vd : v∈D) : v∈C.support ∧ v≠c := by
    obtain ⟨vw,va⟩ := mem_sdiff.mp (mem_filter.mp vd).1
    exact ⟨List.mem_toFinset.mp vw,fun zl => va (zl ▸ cA)⟩
  have long := Graph189FiveCycleTails.order p hp mx C hc five off (List.mem_toFinset.mp (mem_filter.mp cA).1)
    (Dloc dD).1 (Dloc eD).1 (Dloc dD).2 (Dloc eD).2 de cx xy
    (outside xf).1 (outside yf).1 (outside xf).2 (outside yf).2 (row d dD) (row e eD)
  omega

#print axioms excluded
end Graph189FiveCycleLarge
