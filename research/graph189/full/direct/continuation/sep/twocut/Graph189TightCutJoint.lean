import Graph189ExteriorPopulation
import Graph189HighMinimumGap
import Graph189MinimumCut
import Graph189RootedTrace

open SimpleGraph Finset Graph189CutSides
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189TightTwoCut
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B : Finset V} {z t a b : V}

/-- At a tight lower-degree cut vertex the two sides exhaust its even-distance
budget, for every choice of its two opposite contacts. -/
theorem pair (cut : CutSides G A B {z,t}) (zt : z≠t)
    (low : G.degree z+1=G.secondSmallestDegree) (cap : G.distEven z≤G.secondSmallestDegree+1)
    (aA : a∈A) (bB : b∈B) (za : G.Adj z a) (zb : G.Adj z b) :
    G.degree a=G.secondSmallestDegree ∧ G.degree b=G.secondSmallestDegree ∧
    G.neighborFinset a ∩ G.neighborFinset b = {z,t} ∧
    ∀ v, (G.Adj z v ∨ Even (G.dist z v)) →
      v=a ∨ v=b ∨ G.Adj a v ∨ G.Adj b v := by
  classical
  let U := G.neighborFinset a ∪ G.neighborFinset b
  let E := univ.filter (fun v => Even (G.dist z v))
  have apart : ¬G.Adj a b := cut.no_cross a aA b bB
  have ne : a≠b := fun eq => disjoint_left.mp cut.apart (eq ▸ aA) bB
  have highA := (degree_pair (G:=G) a z za.ne.symm).resolve_right (show ¬G.secondSmallestDegree≤G.degree z by omega)
  have highB := (degree_pair (G:=G) b z zb.ne.symm).resolve_right (show ¬G.secondSmallestDegree≤G.degree z by omega)
  have sub : G.neighborFinset a ∩ G.neighborFinset b ⊆ ({z,t}:Finset V) := by
    intro v hv
    obtain ⟨av,bv⟩ := mem_inter.mp hv
    rcases cut.cover v with va|vb|vs
    · exact (cut.no_cross v va b bB ((G.mem_neighborFinset _ _).mp bv).symm).elim
    · exact (cut.no_cross a aA v vb ((G.mem_neighborFinset _ _).mp av)).elim
    · exact vs
  have two : ({z,t}:Finset V).card=2 := by simp [zt]
  have bound := card_le_card sub
  have width := Graph189HighPredecessor.common_lower ne apart za zb cap
  have eq : G.neighborFinset a ∩ G.neighborFinset b = {z,t} :=
    eq_of_subset_of_card_le sub (by omega)
  refine ⟨by omega,by omega,eq,?_⟩
  have inc {u v : V} (zu : G.Adj z u) (uv : G.Adj u v) :
      v∈G.neighborFinset z ∪ E := by
    by_cases zv : G.Adj z v
    · exact mem_union_left _ ((G.mem_neighborFinset _ _).mpr zv)
    apply mem_union_right
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    by_cases same : z=v
    · subst v; simp
    let p : G.Walk z v := .cons zu (.cons uv .nil)
    have d := p.reachable.one_lt_dist_of_ne_of_not_adj same zv
    have hi := G.dist_le p
    change G.dist z v≤2 at hi
    simp [show G.dist z v=2 by omega]
  have covers : insert a (insert b U) ⊆ G.neighborFinset z ∪ E := by
    intro v h
    rcases mem_insert.mp h with rfl|h
    · exact mem_union_left _ ((G.mem_neighborFinset _ _).mpr za)
    rcases mem_insert.mp h with rfl|h
    · exact mem_union_left _ ((G.mem_neighborFinset _ _).mpr zb)
    rcases mem_union.mp h with ha|hb
    · exact inc za ((G.mem_neighborFinset _ _).mp ha)
    · exact inc zb ((G.mem_neighborFinset _ _).mp hb)
  have notA : a∉U := by
    intro ha
    rcases mem_union.mp ha with ha|ha
    · exact G.notMem_neighborFinset_self _ ha
    · exact apart ((G.mem_neighborFinset _ _).mp ha).symm
  have notB : b∉U := by simp [U,apart]
  have boundE : E.card≤G.secondSmallestDegree+1 := cap
  have sz := card_union_add_card_inter (G.neighborFinset a) (G.neighborFinset b)
  change U.card+_=_ at sz
  rw [eq,two,G.card_neighborFinset_eq_degree,G.card_neighborFinset_eq_degree] at sz
  have fullBound := card_union_le (G.neighborFinset z) E
  rw [G.card_neighborFinset_eq_degree] at fullBound
  have size : (insert a (insert b U)).card=U.card+2 := by
    rw [card_insert_of_notMem (by simp [ne,notA]),card_insert_of_notMem notB]
  have full := eq_of_subset_of_card_le covers (by omega)
  intro v h
  have m : v∈G.neighborFinset z ∪ E := h.elim
    (fun h => mem_union_left _ ((G.mem_neighborFinset _ _).mpr h))
    (fun h => mem_union_right _ (mem_filter.mpr ⟨mem_univ _,h⟩))
  rw [←full] at m
  simpa [U] using m

#print axioms pair
end Graph189TightTwoCut

open SimpleGraph Finset Graph189CutSides
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189TightTwoCut
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B : Finset V} {z t a b : V}

omit [Fintype V] [DecidableEq V] [Nontrivial V] [DecidableRel G.Adj] in
private theorem within_two {i j q : V} (first : G.Adj i q) (last : G.Adj q j) : G.dist i j≤2 :=
  G.dist_le (.cons first (.cons last .nil))

omit [Fintype V] [DecidableEq V] [Nontrivial V] [DecidableRel G.Adj] in
private theorem exact_two {i j q : V} (first : G.Adj i q) (last : G.Adj q j)
    (ne : i≠j) (no : ¬G.Adj i j) : G.dist i j=2 := by
  have lo := (first.reachable.trans last.reachable).one_lt_dist_of_ne_of_not_adj ne no
  have hi := within_two first last
  omega

/-- For either side of a tight separating pair, every vertex lies within
distance two of each of that side's z-contacts. The opposite contact and
both separator vertices give three additional vertices in the count. -/
theorem side_order (hc : G.Connected) (cut : CutSides G A B {z,t}) (zt : z≠t)
    (low : G.degree z+1=G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    (aA : a∈A) (bB : b∈B) (za : G.Adj z a) (zb : G.Adj z b) :
    B.card+2≤2*G.secondSmallestDegree := by
  classical
  obtain ⟨_,degB,common,cover⟩ := pair cut zt low (cap z) aA bB za zb
  have bt : G.Adj b t := by
    have mem : t∈G.neighborFinset a ∩ G.neighborFinset b := by rw [common]; simp
    exact (G.mem_neighborFinset _ _).mp (mem_inter.mp mem).2
  have evenClose (w : V) (h : Even (G.dist z w)) : G.dist z w≤2 := by
    rcases cover w (Or.inr h) with rfl|rfl|aW|bW
    · exact (dist_eq_one_iff_adj.mpr za).le.trans (by decide)
    · exact (dist_eq_one_iff_adj.mpr zb).le.trans (by decide)
    · exact within_two za aW
    · exact within_two zb bW
  have withinThree (w : V) : G.dist z w≤3 := by
    by_contra! far
    obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist z w
    have mid := geodesic hc p hp 0 4 (by decide) (by omega)
    rw [Walk.getVert_zero,Nat.sub_zero] at mid
    have h := evenClose (p.getVert 4) (by rw [mid]; decide)
    omega
  let E := univ.filter (fun y => Even (G.dist b y))
  let S := G.neighborFinset b ∪ E
  have into (w : V) (reach : G.Adj b w ∨ Even (G.dist b w)) : w∈S := by
    rcases reach with adj|even
    · exact mem_union_left _ ((G.mem_neighborFinset _ _).mpr adj)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,even⟩)
  have inside : B⊆S := by
    intro y hy
    apply into y
    by_cases beq : b=y
    · subst y; simp
    by_cases edge : G.Adj b y
    · exact Or.inl edge
    right
    have outside : ¬(G.Adj z y ∨ Even (G.dist z y)) := by
      intro h
      rcases cover y h with eq|eq|adj|adj
      · subst y; exact disjoint_left.mp cut.apart aA hy
      · exact beq eq.symm
      · exact cut.no_cross a aA y hy adj
      · exact edge adj
    have three : G.dist z y=3 := by
      have n1 : G.dist z y≠1 := fun h => outside (Or.inl (dist_eq_one_iff_adj.mp h))
      have n0 : G.dist z y≠0 := fun h => outside (Or.inr (by simp [h]))
      have n2 : G.dist z y≠2 := fun h => outside (Or.inr (by simp [h]))
      have bound := withinThree y
      omega
    obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist z y
    let q := p.getVert 2
    have dq : G.dist z q=2 := by
      simpa [q] using geodesic hc p hp 0 2 (by decide) (by omega)
    have qy : G.Adj q y := by
      have h := p.adj_getVert_succ (show 2<p.length by omega)
      simpa only [show 2+1=p.length by omega,Walk.getVert_length] using h
    have bq : G.Adj b q := by
      rcases cut.cover q with qa|qb|qs
      · exact (cut.no_cross q qa y hy qy).elim
      · rcases cover q (Or.inr (by simp [dq])) with eq|eq|adj|adj
        · exact (disjoint_left.mp cut.apart aA (eq ▸ qb)).elim
        · rw [eq,dist_eq_one_iff_adj.mpr zb] at dq
          omega
        · exact (cut.no_cross a aA q qb adj).elim
        · exact adj
      · have choice : q=z ∨ q=t := by simpa using qs
        rcases choice with eq|eq
        · rw [eq,SimpleGraph.dist_self] at dq
          omega
        · simpa [eq] using bt
    simp [exact_two bq qy beq edge]
  have az : a≠z := za.ne.symm
  have at' : a≠t := by
    intro eq
    exact disjoint_left.mp cut.left_cut aA (by simp [eq])
  have notB (v) (h : v∈({a,z,t} : Finset V)) : v∉B := by
    rcases mem_insert.mp h with rfl|h
    · exact fun hm => disjoint_left.mp cut.apart aA hm
    · exact fun hm => disjoint_left.mp cut.right_cut hm h
  have nA : a∉B := notB a (by simp)
  have nZ : z∉B := notB z (by simp)
  have nT : t∉B := notB t (by simp)
  have ba : b≠a := fun eq => nA (eq ▸ bB)
  have sep : ¬G.Adj b a := fun h => cut.no_cross a aA b bB h.symm
  have inc : insert a (insert z (insert t B)) ⊆ S := by
    intro w hw
    rcases mem_insert.mp hw with eq|hw
    · subst w; exact into a (Or.inr (by simp [exact_two zb.symm za ba sep]))
    rcases mem_insert.mp hw with eq|hw
    · subst w; exact into z (Or.inl zb.symm)
    rcases mem_insert.mp hw with eq|hw
    · subst w; exact into t (Or.inl bt)
    · exact inside hw
  have count := card_le_card inc
  have upper := card_union_le (G.neighborFinset b) E
  change S.card≤_ at upper
  rw [G.card_neighborFinset_eq_degree,degB] at upper
  have ec : E.card≤G.secondSmallestDegree+1 := cap b
  simp [az,at',zt,nA,nZ,nT] at count
  omega

#print axioms side_order
end Graph189TightTwoCut

open SimpleGraph Finset Graph189CutSides
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189TightTwoCut
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The bad wedge for a longest rooted path has distinct outer vertices. -/
private theorem rooted {H : SimpleGraph V} [DecidableRel H.Adj] (r b : V) (edge : H.Adj r b)
    (ore : ∀ x y : V, x≠r → y≠r → x≠y → ¬H.Adj x y →
      Fintype.card V≤H.degree x+H.degree y) : ∃ v, ∃ p : H.Walk r v, p.IsHamiltonian := by
  classical
  have reach (x y : V) (xr : x≠r) (yr : y≠r) : H.Reachable x y := by
    by_contra no
    have xy : x≠y := fun eq => no (eq ▸ Reachable.refl _)
    have missing : ¬H.Adj x y := fun e => no e.reachable
    have dis : Disjoint (H.neighborFinset x) (H.neighborFinset y) := by
      apply Finset.disjoint_left.mpr
      intro v xv yv
      exact no (((H.mem_neighborFinset _ _).mp xv).reachable.trans
        ((H.mem_neighborFinset _ _).mp yv).symm.reachable)
    have absent : x∉H.neighborFinset x ∪ H.neighborFinset y := by
      simp only [mem_union,H.mem_neighborFinset]
      exact fun e => e.elim (H.loopless.irrefl x) (fun a => missing a.symm)
    have size := card_le_univ (insert x (H.neighborFinset x ∪ H.neighborFinset y))
    rw [card_insert_of_notMem absent,card_union_of_disjoint dis,H.card_neighborFinset_eq_degree,
      H.card_neighborFinset_eq_degree] at size
    have lower := ore x y xr yr xy missing
    omega
  have hc : H.Connected := (H.connected_iff_exists_forall_reachable).mpr ⟨r,fun v => by
    by_cases eq : v=r
    · exact eq ▸ Reachable.refl _
    exact edge.reachable.trans (reach b v edge.ne.symm eq)⟩
  obtain ⟨v,P,hp,longest⟩ := Graph189RootedPath.exists_rooted_longest H r
  refine ⟨v,P,hp.isHamiltonian_iff.mpr ?_⟩
  intro x
  by_contra hx
  obtain ⟨u,hu,contact⟩ := Graph189RootedPath.exists_exterior_contact P hc ⟨x,hx⟩
  obtain ⟨W,succ,hn,hi,ht,hm,ha,hc',hs,hur⟩ :=
    Graph189RootedPath.successors_of_rooted_longest P hp longest hu contact
  obtain ⟨w,hw,bad⟩ := Graph189RootedOreCount.bad_wedge_of_successors u W succ hn hi ht hm ha hc'
  have deg := ore u (succ w) hur (hs _ hw).2 (hm _ hw).1.symm (hm _ hw).2
  exact (not_lt_of_ge ((card_le_univ _).trans deg)) bad

variable [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj] {A B : Finset V} {z t a b : V}

private theorem side_path (hc : G.Connected) (cut : CutSides G A B {z,t}) (zt : z≠t)
    (low : G.degree z+1=G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    (aA : a∈A) (bB : b∈B) (za : G.Adj z a) (zb : G.Adj z b) :
    ∃ v, ∃ p : G.Walk t v, p.IsPath ∧ p.support.length=B.card+1 ∧
      ∀ u∈p.support, u=t ∨ u∈B := by
  classical
  have size := side_order hc cut zt low cap aA bB za zb
  let S := insert t B
  let H := G.induce (S : Set V)
  let r : S := ⟨t,mem_insert_self ..⟩
  let c : S := ⟨b,mem_insert_of_mem bB⟩
  have tB : t∉B := fun h => disjoint_left.mp cut.right_cut h (by simp)
  have zB : z∉B := fun h => disjoint_left.mp cut.right_cut h (by simp)
  have card : Fintype.card ((S : Set V))=B.card+1 := by
    change Fintype.card S=B.card+1
    rw [Fintype.card_coe,card_insert_of_notMem tB]
  obtain ⟨_,_,common,_⟩ := pair cut zt low (cap z) aA bB za zb
  have edge : H.Adj r c := by
    have mem : t∈G.neighborFinset a ∩ G.neighborFinset b := by rw [common]; simp
    exact ((G.mem_neighborFinset _ _).mp (mem_inter.mp mem).2).symm
  have bounds (x : S) (xr : x≠r) : G.secondSmallestDegree≤H.degree x+1 ∧
      (¬G.Adj z x.val → G.secondSmallestDegree≤H.degree x) := by
    have xB : x.val∈B := (mem_insert.mp x.property).resolve_left (fun e => xr (Subtype.ext e))
    have high := (degree_pair (G:=G) x.val z (fun e => zB (e ▸ xB))).resolve_right
      (show ¬G.secondSmallestDegree≤G.degree z by omega)
    let F := (G.neighborFinset x.val).filter (fun v => v∈(S:Set V))
    have deg : H.degree x=F.card := Graph189ExteriorDegreeCycle.degree_induce_filter _ _
    have inc : G.neighborFinset x.val ⊆ insert z F := by
      intro v hv
      rcases cut.cover v with av|bv|vs
      · exact (cut.no_cross v av x.val xB ((G.mem_neighborFinset _ _).mp hv).symm).elim
      · exact mem_insert_of_mem (mem_filter.mpr ⟨hv,mem_insert_of_mem bv⟩)
      · rcases (show v=z ∨ v=t by simpa using vs) with rfl|rfl
        · exact mem_insert_self ..
        · exact mem_insert_of_mem (mem_filter.mpr ⟨hv,mem_insert_self ..⟩)
    have n := card_le_card inc
    rw [G.card_neighborFinset_eq_degree] at n
    have one := card_insert_le z F
    refine ⟨by omega,?_⟩
    intro no
    have inc' : G.neighborFinset x.val⊆F := by
      intro v hv
      rcases mem_insert.mp (inc hv) with rfl|h
      · exact (no ((G.mem_neighborFinset _ _).mp hv).symm).elim
      · exact h
    have n' := card_le_card inc'
    rw [G.card_neighborFinset_eq_degree] at n'
    omega
  obtain ⟨v,P,hP⟩ := rooted (H:=H) r c edge (by
    intro x y xr yr xy no
    have bx := bounds x xr
    have by' := bounds y yr
    by_cases zx : G.Adj z x.val
    · have xB := (mem_insert.mp x.property).resolve_left (fun e => xr (Subtype.ext e))
      have yB := (mem_insert.mp y.property).resolve_left (fun e => yr (Subtype.ext e))
      have ny : ¬G.Adj z y.val := by
        intro zy
        have covers := (pair cut zt low (cap z) aA xB za zx).2.2.2
        rcases covers y.val (Or.inl zy) with e|e|ay|adj
        · exact disjoint_left.mp cut.apart aA (e ▸ yB)
        · exact xy (Subtype.ext e.symm)
        · exact cut.no_cross a aA y.val yB ay
        · exact no adj
      have := by'.2 ny
      omega
    · have := bx.2 zx
      omega)
  let f := (Embedding.induce (G:=G) (S : Set V)).toHom
  have length : (P.map f).support.length=B.card+1 := by
    rw [Walk.support_map,List.length_map,hP.length_support,card]
  have inside (u : V) (hu : u∈(P.map f).support) : u=t ∨ u∈B := by
    rw [Walk.support_map] at hu
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hu
    exact mem_insert.mp j.property
  exact ⟨v.val,P.map f,hP.isPath.map Subtype.val_injective,length,inside⟩

/-- Every tight separating pair through the unique lower vertex gives an
actual Hamiltonian path in the original graph. -/
theorem traceable (hc : G.Connected) (cut : CutSides G A B {z,t}) (zt : z≠t)
    (low : G.degree z+1=G.secondSmallestDegree) (five : 5≤G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    (aA : a∈A) (bB : b∈B) (za : G.Adj z a) (zb : G.Adj z b) :
    ∃ x y : V, ∃ p : G.Walk x y, p.IsHamiltonian := by
  classical
  by_contra fail
  obtain ⟨x,P,hp,lenP,allP⟩ := side_path hc cut.swap zt low cap bB aA zb za
  obtain ⟨y,Q,hq,lenQ,allQ⟩ := side_path hc cut zt low cap aA bB za zb
  let W := P.reverse.append Q
  have toll : t∉Q.support.tail := by
    have l := hq.support_nodup
    rw [← Q.cons_tail_support] at l
    exact (List.nodup_cons.mp l).1
  have real : W.IsPath := by
    apply Walk.IsPath.mk'
    rw [show W=P.reverse.append Q from rfl,Walk.support_append,Walk.support_reverse]
    apply List.nodup_append.mpr
    refine ⟨List.nodup_reverse.mpr hp.support_nodup,hq.support_nodup.tail,?_⟩
    rintro v hv w hw rfl
    have a := allP v (List.mem_reverse.mp hv)
    have b := allQ v (List.mem_of_mem_tail hw)
    rcases a with rfl|a
    · exact toll hw
    rcases b with rfl|b
    · exact toll hw
    exact disjoint_left.mp cut.apart a b
  have counts : A.card+B.card+2=Fintype.card V := by
    have all : A∪B∪{z,t}=univ := by
      apply eq_univ_iff_forall.mpr
      intro v
      rcases cut.cover v with av|bv|s
      · exact mem_union_left _ (mem_union_left _ av)
      · exact mem_union_left _ (mem_union_right _ bv)
      · exact mem_union_right _ s
    have q := congrArg Finset.card all
    rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨cut.left_cut,cut.right_cut⟩),
      card_union_of_disjoint cut.apart,card_univ] at q
    simpa [zt] using q
  have gap := Graph189ExteriorDegreeCycle.high_min_all_paths_gap fail five cap
    (fun v => by
      by_cases eq : v=z
      · rw [eq]; omega
      have := (degree_pair (G:=G) v z eq).resolve_right (show ¬G.secondSmallestDegree≤G.degree z by omega)
      omega) x y W real
  rw [show W=P.reverse.append Q from rfl,Walk.support_append,Walk.support_reverse,List.length_append,
    List.length_reverse,List.length_tail,lenP,lenQ] at gap
  omega

#print axioms traceable
end Graph189TightTwoCut
