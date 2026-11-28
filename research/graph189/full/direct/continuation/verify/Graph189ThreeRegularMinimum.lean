import Graph189OrderBound
import Graph189SingleExteriorShift
import Graph189ExteriorDegree
import Graph189MatchedOrder
import Graph189RootedPath

open SimpleGraph Finset Graph189ExteriorGap

namespace Graph189ThreeRegularMinimum

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem longest_path (z : V) :
    ∃ x y : V, ∃ p : G.Walk x y, p.IsPath ∧
      ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length := by
  classical
  let Good (n : ℕ) := ∃ x y : V, ∃ p : G.Walk x y, p.IsPath ∧ p.length = n
  have base : Good 0 := ⟨z,z,.nil,by simp,rfl⟩
  obtain ⟨x,y,p,hp,hlen⟩ := Nat.findGreatest_spec (Nat.zero_le (Fintype.card V)) base
  refine ⟨x,y,p,hp,?_⟩
  intro u v r hr
  rw [hlen]
  have card := hr.support_nodup.length_le_card
  have size := r.length_support
  exact Nat.le_findGreatest (by omega) (show Good r.length from ⟨u,v,r,hr,rfl⟩)

/-- If all degrees are at least three and every second layer has at most three
vertices, each vertex omitted by a longest path has two omitted neighbors. -/
theorem exterior_neighbors {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (degree : ∀ v : V, 3 ≤ G.degree v)
    (quota : ∀ v : V, (univ.filter (fun z => G.dist v z=2)).card ≤ 3)
    {a : V} (out : a ∉ p.support) :
    2 ≤ (G.neighborFinset a \ p.support.toFinset).card := by
  classical
  let D := G.neighborFinset a \ p.support.toFinset
  have sum := Finset.card_sdiff_add_card_inter (G.neighborFinset a) p.support.toFinset
  change D.card + _ = G.degree a at sum
  have ha := degree a
  by_cases nonempty : D.Nonempty
  · obtain ⟨b,hm⟩ := nonempty
    obtain ⟨nb,off⟩ := mem_sdiff.mp hm
    have bOut : b∉p.support := fun h => off (List.mem_toFinset.mpr h)
    have bound := half_degree_outside_longest p hp longest out bOut
      ((G.mem_neighborFinset _ _).mp nb) (quota a) (degree b)
    omega
  · have empty : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp nonempty
    rw [empty,Finset.card_empty,Nat.zero_add] at sum
    have size := contact_card_neighbors p hp a
    have touch : (contactPositions p a).Nonempty := card_pos.mp (by omega)
    have shift := single_positions_lt_path_shell p hp longest out touch
    have sub : p.support.toFinset.filter (fun v => G.dist a v=2) ⊆
        univ.filter (fun v => G.dist a v=2) :=
      fun v h => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2⟩
    have count := (card_le_card sub).trans (quota a)
    omega

/-- Two-connected graphs with minimum degree three, order at most eleven and
at most three vertices in every second layer have a Hamiltonian path. -/
theorem traceable_eleven (hc : G.Connected)
    (uncut : ∀ z : V, (G.induce {v | v ≠ z}).Connected)
    (degree : ∀ v : V, 3 ≤ G.degree v)
    (quota : ∀ v : V, (univ.filter (fun z => G.dist v z=2)).card ≤ 3)
    (small : Fintype.card V ≤ 11) :
    ∃ x y : V, ∃ p : G.Walk x y, p.IsHamiltonian := by
  classical
  obtain ⟨z⟩ := hc.nonempty
  obtain ⟨x,y,p,hp,longest⟩ := longest_path (G:=G) z
  refine ⟨x,y,p,hp.isHamiltonian_iff.mpr ?_⟩
  intro a
  by_contra missing
  let E := univ \ p.support.toFinset
  let D (b : V) := G.neighborFinset b \ p.support.toFinset
  have exdeg (b : V) (out : b∉p.support) : 2 ≤ (D b).card :=
    exterior_neighbors p hp longest degree quota out
  have dmem {b c : V} (h : c ∈ D b) : G.Adj b c ∧ c∉p.support :=
    ⟨(G.mem_neighborFinset _ _).mp (mem_sdiff.mp h).1,
      fun hc' => (mem_sdiff.mp h).2 (List.mem_toFinset.mpr hc')⟩
  have emem {b : V} : b∈E ↔ b∉p.support := by simp [E]
  have add (b : V) (out : b∉p.support) : insert b (D b) ⊆ E := by
    intro c h
    rcases mem_insert.mp h with rfl | h
    · exact emem.mpr out
    · exact emem.mpr (dmem h).2
  have self (b : V) : b∉D b := fun h => (dmem h).1.ne rfl
  have cardE : 3 ≤ E.card := by
    have h := card_le_card (add a missing)
    rw [card_insert_of_notMem (self a)] at h
    have := exdeg a missing
    omega
  have total := card_outside_add_path p hp E (fun _ h => emem.mp h)
  have nextNeighbor (b c : V) (out : c∉p.support) : ∃ d ∈ D c, d ≠ b := by
    by_contra! all
    have sub : D c ⊆ {b} := fun d hd => mem_singleton.mpr (all d hd)
    have bd := card_le_card sub
    rw [card_singleton] at bd
    have := exdeg c out
    omega
  have tails (i : Fin p.support.length) (b : V) (out : b∉p.support)
      (attach : G.Adj p.support[i.val] b) : 3 ≤ i.val ∧ i.val+4 ≤ p.support.length := by
    have degB := exdeg b out
    obtain ⟨c,hc'⟩ := card_pos.mp (show 0 < (D b).card by omega)
    obtain ⟨bc,cout⟩ := dmem hc'
    obtain ⟨d,hd,db⟩ := nextNeighbor b c cout
    obtain ⟨cd,dout⟩ := dmem hd
    let q : G.Walk b d := Walk.cons bc (Walk.cons cd Walk.nil)
    have hq : q.IsPath := Walk.IsPath.mk' (by simp [q,bc.ne,cd.ne,Ne.symm db])
    have hdj : List.Disjoint q.support p.support := by
      simpa [q,List.disjoint_left] using (show
        ∀ v, v=b ∨ v=c ∨ v=d → v∉p.support from by
          rintro _ (rfl|rfl|rfl) <;> assumption)
    have revdisj : List.Disjoint q.reverse.support p.support := by
      simpa only [Walk.support_reverse,List.disjoint_reverse_left] using hdj
    have front := prefix_of_detour p hp longest i q.reverse hq.reverse revdisj attach.symm
    have back := suffix_of_detour p hp longest i q hq hdj attach
    have pathLength := p.length_support
    simp [q] at front back
    omega
  obtain ⟨b,boff,w,won,bw⟩ := Graph189RootedPath.exists_exterior_contact p hc ⟨a,missing⟩
  obtain ⟨i,hi,wi⟩ := List.mem_iff_getElem.mp won
  let I : Fin p.support.length := ⟨i,hi⟩
  have first : G.Adj p.support[I.val] b := by simpa only [I,wi] using bw.symm
  have ti := tails I b boff first
  have xw : x ≠ w := by
    intro eq
    have hix : p.getVert i = p.getVert 0 := by
      rw [← get_at p hi,wi,Walk.getVert_zero,eq]
    have ls := p.length_support
    have iz := hp.getVert_injOn (show i ≤ p.length by omega) (show 0 ≤ p.length by omega) hix
    change 3 ≤ i ∧ _ at ti
    omega
  have aw : a ≠ w := by rintro rfl; exact missing won
  let X := {v : V // v ≠ w}
  let st : X := ⟨x,xw⟩
  let en : X := ⟨a,aw⟩
  obtain ⟨r⟩ := uncut w st en
  obtain ⟨edge,_,inside,outside⟩ := r.exists_boundary_dart
    {v : X | v.val∈p.support} p.start_mem_support missing
  let c := edge.snd.val
  have cout : c∉p.support := outside
  have onpath : edge.fst.val∈p.support := inside
  obtain ⟨j,hj,wj⟩ := List.mem_iff_getElem.mp onpath
  let J : Fin p.support.length := ⟨j,hj⟩
  have second : G.Adj p.support[J.val] c := by
    simpa only [J,wj] using (show G.Adj edge.fst.val c from edge.adj)
  have diff : i ≠ j := by
    intro h
    subst j
    exact edge.fst.property (wj.symm.trans wi)
  have tj := tails J c cout second
  change 3 ≤ i ∧ i+4 ≤ p.support.length at ti
  change 3 ≤ j ∧ j+4 ≤ p.support.length at tj
  have Eeq : E.card=3 := by omega
  have adj : b = c ∨ G.Adj b c := by
    by_cases eq : b = c
    · exact Or.inl eq
    right
    have h := card_le_card (add b boff)
    rw [card_insert_of_notMem (self b)] at h
    have db := exdeg b boff
    have same : insert b (D b) = E :=
      Finset.eq_of_subset_of_card_le (add b boff) (by rw [card_insert_of_notMem (self b)]; omega)
    have hc' : c ∈ insert b (D b) := by rw [same]; exact emem.mpr cout
    exact (dmem ((mem_insert.mp hc').resolve_left (Ne.symm eq))).1
  rcases lt_or_gt_of_ne diff with lt | gt
  · have lt' : I < J := lt
    rcases adj with rfl | bc
    · have := omitted_contact_spacing p hp longest boff I J lt' first second
      change i+2 ≤ j at this
      omega
    · have := adjacent_omitted_contact_spacing p hp longest boff cout bc I J lt' first second
      change i+3 ≤ j at this
      omega
  · have gt' : J < I := gt
    rcases adj with rfl | bc
    · have := omitted_contact_spacing p hp longest boff J I gt' second first
      change j+2 ≤ i at this
      omega
    · have := adjacent_omitted_contact_spacing p hp longest cout boff bc.symm J I gt' second first
      change j+3 ≤ i at this
      omega

/-- The registered maximum-even hypothesis at degree three bounds every second layer. -/
theorem exact_two_quota [Nontrivial V]
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (hk : G.secondSmallestDegree = 3) :
    ∀ v, (univ.filter (fun w => G.dist v w=2)).card ≤ 3 := by
  classical
  intro v
  let D := univ.filter (fun w => G.dist v w = 2)
  have sub : insert v D ⊆ univ.filter (fun w => Even (G.dist v w)) := by
    intro w hw
    rcases mem_insert.mp hw with rfl | h
    · simp
    · exact mem_filter.mpr ⟨mem_univ _,by simp [(mem_filter.mp h).2]⟩
  have no : v∉D := by simp [D]
  have bound := card_le_card sub
  rw [card_insert_of_notMem no] at bound
  change D.card+1 ≤ G.distEven v at bound
  have localCap := (le_max' _ _ (mem_image_of_mem (distEven G) (mem_univ v))).trans cap
  change D.card ≤ 3
  omega

/-- The tied minimum and second degree three case of the two-connected parent. -/
theorem traceable_tied_three [Nontrivial V] (hc : G.Connected)
    (uncut : ∀ z : V, (G.induce {v | v ≠ z}).Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (hmin : G.minDegree = 3) (hk : G.secondSmallestDegree = 3) :
    ∃ x y : V, ∃ p : G.Walk x y, p.IsHamiltonian := by
  classical
  have n := Graph189OrderBound.order_le hc cap
  rw [hmin,hk] at n
  apply traceable_eleven hc uncut (fun v => hmin ▸ G.minDegree_le_degree v) _ (by norm_num at n; omega)
  exact exact_two_quota cap hk

#print axioms traceable_tied_three
end Graph189ThreeRegularMinimum
