import Graph189ExteriorDegree
import Graph189ExteriorPopulation
import Graph189PrescribedBatch

open Finset SimpleGraph
namespace Graph189RotationExterior
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem exists_longest (z : V) :
    ∃ x y, ∃ p : G.Walk x y, p.IsPath ∧
      ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length ≤ p.length := by
  classical
  let Good (n : ℕ) := ∃ a b, ∃ r : G.Walk a b, r.IsPath ∧ r.length=n
  have base : Good 0 := ⟨z,z,.nil,by simp,rfl⟩
  obtain ⟨x,y,p,hp,sz⟩ := Nat.findGreatest_spec (Nat.zero_le (Fintype.card V)) base
  refine ⟨x,y,p,hp,?_⟩
  intro a b r hr
  rw [sz]
  have := r.length_support
  have := hr.support_nodup.length_le_card
  exact Nat.le_findGreatest (by omega) (show Good r.length from ⟨_,_,r,hr,rfl⟩)

/-- With all cycles short, every neighbor of the first vertex of a longest
path occurs within its first L vertices. -/
private theorem neighbors_in_prefix {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (maximal : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length ≤ p.length)
    {L : ℕ} (two : 2 ≤ L) (short : ∀ v (q : G.Walk v v), q.IsCycle → q.length ≤ L) :
    G.neighborFinset x ⊆ (p.support.take L).toFinset := by
  intro v hv
  have edge := (G.mem_neighborFinset _ _).mp hv
  have mem : v ∈ p.support := by
    by_contra miss
    have bound := maximal (p.cons edge.symm) (Walk.IsPath.mk' (by simp [miss,hp.support_nodup]))
    simp at bound
  apply List.mem_toFinset.mpr
  apply (List.mem_take_iff_idxOf_lt mem).mpr
  by_contra! far
  let T := p.takeUntil v mem
  have len : L ≤ T.length := by rwa [p.length_takeUntil mem]
  have cycle : (T.cons edge.symm).IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨?_,by simp only [Walk.length_cons]; omega⟩
    rw [Walk.tail_cons]
    exact (Walk.isPath_copy _ _ _).mpr (hp.takeUntil mem)
  have bound := short v _ cycle
  simp only [Walk.length_cons] at bound
  omega

omit [Fintype V] [DecidableRel G.Adj] in
/-- Reverse the path strictly before the pivot and join the old initial
vertex to the pivot. If the pivot was in the first L positions the new
path has the same set of first L vertices. -/
private theorem rotate {x y : V} (p : G.Walk x y) (hp : p.IsPath) {i L : ℕ}
    (inside : i+1 < p.support.length) (near : i+1 ≤ L)
    (pivot : G.Adj x (p.getVert (i+1))) :
    ∃ b, ∃ r : G.Walk (p.getVert i) b, r.IsPath ∧ r.length=p.length ∧
      (r.support.take L).toFinset=(p.support.take L).toFinset := by
  let A := p.support.take (i+1)
  let B := p.support.drop (i+1)
  have split : p.support=A++B := (List.take_append_drop _ _).symm
  have size : A.length=i+1 := by
    change (p.support.take (i+1)).length=i+1
    exact List.length_take_of_le (by omega)
  have last : A.getLast?=some (p.getVert i) := by
    have nearI : i < p.support.length := by omega
    rw [←Graph189ExteriorGap.get_at p nearI]
    exact (congrArg List.getLast? (List.take_succ_eq_append_getElem (l:=p.support) (i:=i) nearI)).trans
      List.getLast?_concat
  have first : A.head?=some x := by
    simp only [A,List.head?_take,show i+1≠0 by omega,if_false]
    rw [List.head?_eq_some_head p.support_ne_nil,p.head_support]
  have startB : B.head?=some (p.getVert (i+1)) := by
    simp only [B,List.head?_drop,List.getElem?_eq_getElem inside,Graph189ExteriorGap.get_at]
  let S := A.reverse++B
  have chain := p.isChain_adj_support
  have nd := hp.support_nodup
  rw [split] at chain nd
  have chainR : A.reverse.IsChain G.Adj := List.isChain_reverse.mpr
    (chain.left_of_append.imp (fun _ _ edge => edge.symm))
  have chainS : S.IsChain G.Adj := by
    apply chainR.append chain.right_of_append
    intro v hv w hw
    rw [List.getLast?_reverse, first] at hv
    rw [startB] at hw
    exact (Option.mem_some_iff.mp hv) ▸ (Option.mem_some_iff.mp hw) ▸ pivot
  have ndS : S.Nodup := List.Nodup.append (by simpa using nd.of_append_left) nd.of_append_right
    (by simpa using nd.disjoint)
  have headS : S.head?=some (p.getVert i) := by simp [S,List.head?_append,last]
  have sNe : S≠[] := by intro empty; simp [empty] at headS
  let r := Walk.ofSupport S sNe chainS
  have supp : r.support=S := Walk.support_ofSupport sNe chainS
  have start : S.head sNe=p.getVert i := by rw [List.head?_eq_some_head sNe] at headS; simpa using headS
  have path : r.IsPath := Walk.IsPath.mk' (by rwa [supp])
  have len : r.length=p.length := by
    have lhs := r.length_support
    have rhs := p.length_support
    rw [supp] at lhs
    rw [split] at rhs
    simp only [S,List.length_append,List.length_reverse] at lhs rhs
    omega
  have sets : (S.take L).toFinset=(p.support.take L).toFinset := by
    have le : A.length ≤ L := size.trans_le near
    have rev : A.reverse.length ≤ L := by simpa using le
    rw [split]
    simp only [S,List.take_append,List.take_of_length_le le,List.take_of_length_le rev,List.length_reverse]
    simp
  exact ⟨_,r.copy start rfl,(Walk.isPath_copy _ _ _).mpr path,by simpa using len,by simpa [supp] using sets⟩

/-- If all cycles are short, one initial segment of a longest path contains
at least d distinct reachable endpoints and their entire neighborhoods. -/
theorem degree_window (z : V) {d L : ℕ} (two : 2 ≤ L)
    (minimum : ∀ v, d ≤ G.degree v)
    (short : ∀ v (q : G.Walk v v), q.IsCycle → q.length ≤ L) :
    ∃ B E : Finset V, d ≤ E.card ∧ E ⊆ B ∧ B.card ≤ L ∧
      ∀ v ∈ E, G.neighborFinset v ⊆ B := by
  classical
  obtain ⟨x,y,p,hp,mx⟩ := exists_longest (G:=G) z
  let B := (p.support.take L).toFinset
  let N := G.neighborFinset x
  let idx (v : V) := p.support.idxOf v
  let prev (v : V) := p.getVert (idx v-1)
  let E := N.image prev
  have initial : N ⊆ B := neighbors_in_prefix p hp mx two short
  have mem {v : V} (hv : v ∈ N) : v ∈ p.support := List.mem_of_mem_take (List.mem_toFinset.mp (initial hv))
  have range {v : V} (hv : v ∈ N) : idx v < p.support.length := List.idxOf_lt_length_iff.mpr (mem hv)
  have value {v : V} (hv : v ∈ N) : p.getVert (idx v)=v :=
    (Graph189ExteriorGap.get_at p (range hv)).symm.trans (List.getElem_idxOf (range hv))
  have pos {v : V} (hv : v ∈ N) : 0 < idx v := by
    by_contra! zero
    have eq := value hv
    rw [show idx v=0 by omega,Walk.getVert_zero] at eq
    exact ((G.mem_neighborFinset _ _).mp hv).ne eq
  have near {v : V} (hv : v ∈ N) : idx v < L :=
    (List.mem_take_iff_idxOf_lt (mem hv)).mp (List.mem_toFinset.mp (initial hv))
  have inj : Set.InjOn prev (N : Set V) := by
    intro a ha b hb eq
    have pa := pos ha
    have pb := pos hb
    have ra := range ha
    have rb := range hb
    have := p.length_support
    have same : idx a-1=idx b-1 := hp.getVert_injOn
      (by change idx a-1 ≤ p.length; omega) (by change idx b-1 ≤ p.length; omega) eq
    have index : idx a=idx b := by omega
    exact (value ha).symm.trans ((congrArg p.getVert index).trans (value hb))
  have enough : d ≤ E.card := by
    change d ≤ (N.image prev).card
    rw [card_image_of_injOn inj]
    exact (minimum x).trans_eq (G.card_neighborFinset_eq_degree x).symm
  have sub : E ⊆ B := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
    let j := idx w-1
    have jw : j < p.support.length := by have := range hw; dsimp [j]; omega
    have jl : j < L := by have := near hw; dsimp [j]; omega
    apply List.mem_toFinset.mpr
    apply List.mem_take_iff_getElem.mpr
    exact ⟨j,lt_min jl jw, Graph189ExteriorGap.get_at p jw⟩
  have constrained (v : V) (hv : v ∈ E) : G.neighborFinset v ⊆ B := by
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
    have pp := pos hw
    have len := range hw
    have small := near hw
    have step : idx w-1+1=idx w := by omega
    obtain ⟨b,r,hr,eq,same⟩ := rotate p hp (i:=idx w-1) (L:=L) (by omega) (by omega)
      (by rw [step,value hw]; exact (G.mem_neighborFinset _ _).mp hw)
    have mx' {a b} (s : G.Walk a b) (hs : s.IsPath) : s.length ≤ r.length := (mx s hs).trans_eq eq.symm
    have bound := neighbors_in_prefix r hr mx' two short
    rw [same] at bound
    exact bound
  have lengthB : B.card ≤ L := (List.toFinset_card_le _).trans (List.length_take_le _ _)
  exact ⟨B,E,enough,sub,lengthB,constrained⟩

/-- A graph with a sufficiently large minimum degree either has a long cycle
or contains a Hamilton-connected induced subgraph of at least that degree. -/
theorem cycle_or_hamilton_connected (z : V) {d L : ℕ} (two : 2 ≤ L)
    (density : 2*L+1 ≤ 3*d) (minimum : ∀ v, d ≤ G.degree v) :
    (∃ x, ∃ q : G.Walk x x, q.IsCycle ∧ L+1 ≤ q.length) ∨
      ∃ E : Finset V, d ≤ E.card ∧ ∀ x y : E, x≠y →
        ∃ r : (G.induce (E : Set V)).Walk x y, r.IsHamiltonian := by
  classical
  by_cases long : ∃ x, ∃ q : G.Walk x x, q.IsCycle ∧ L+1 ≤ q.length
  · exact Or.inl long
  right
  have short (x : V) (q : G.Walk x x) (cycle : q.IsCycle) : q.length ≤ L := by
    by_contra! big
    exact long ⟨x,q,cycle,big⟩
  obtain ⟨B,E,enough,sub,lengthB,constrained⟩ := degree_window z two minimum short
  let H := G.induce (E : Set V)
  have degree (v : E) : d+E.card ≤ H.degree v+B.card := by
    let A := G.neighborFinset v.val
    have bound : (A \ E).card ≤ (B \ E).card := card_le_card (sdiff_subset_sdiff_left E (constrained _ v.property))
    have left := card_sdiff_add_card_inter A E
    have right := card_sdiff_add_card_eq_card sub
    change d+E.card ≤ (G.induce (E : Set V)).degree v + B.card
    rw [Graph189ExteriorDegreeCycle.degree_induce_filter]
    have same : (A.filter (fun w => w ∈ (E : Set V)))=A∩E := by ext w; simp
    rw [show ((G.neighborFinset v.val).filter (fun w => w ∈ (E : Set V)))=A∩E from same]
    have ambient := minimum v.val
    change d ≤ A.card at ambient
    omega
  refine ⟨E,enough,?_⟩
  intro a b ne
  apply Graph189TerminalLeafClosure.prescribed_of_supergraph (G:=H) le_top _
    (Graph189TerminalLeafClosure.complete_prescribed a b ne)
  intro v w _ _
  have := degree v
  have := degree w
  change Fintype.card E+1 ≤ H.degree v + H.degree w
  rw [Fintype.card_coe]
  omega

end Graph189RotationExterior
#print axioms Graph189RotationExterior.cycle_or_hamilton_connected
