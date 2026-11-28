import Graph189FiveLowMarks
import Graph189GapExchange
import Graph189HighMinimumGap

open SimpleGraph Finset Graph189ExteriorGap
namespace Graph189FiveLowInsertion
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}

/-- An isolated omission whose degree exceeds half the quota can replace
an intermediate vertex between two marks. -/
theorem isolated (p : G.Walk a b) (hp : p.IsPath)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {z : V} (off : z∉p.support) (all : G.neighborFinset z ⊆ p.support.toFinset)
    (quota : (univ.filter (fun w => G.dist z w=2)).card < 2*G.degree z) :
    ∃ c d, ∃ q : G.Walk c d, q.IsPath ∧ q.length=p.length ∧ z∈q.support := by
  classical
  by_contra no
  have wide (i : ℕ) (hi : i∈contactPositions p z) (j : ℕ) (hj : j∈contactPositions p z) (ij : i<j) : i+3 ≤ j := by
    obtain ⟨ir,ic⟩ := (mem_contactPositions p z i).mp hi
    obtain ⟨jr,jc⟩ := (mem_contactPositions p z j).mp hj
    have spaced := omitted_contact_spacing p hp maximal off ⟨i,ir⟩ ⟨j,jr⟩ ij
      (by simpa [get_at] using ic) (by simpa [get_at] using jc)
    by_contra! small
    have eq : j=i+2 := by change i+2 ≤ j at spaced; omega
    obtain ⟨c,d,q,hq,same,supp⟩ := swap_contact_midpoint p hp off i (eq ▸ jr) ic (eq ▸ jc)
    apply no ⟨c,d,q,hq,same,?_⟩
    apply List.mem_toFinset.mp
    rw [supp]
    exact mem_insert_self _ _
  have costs := double_positions_le_path_shell p hp maximal off wide
  rw [contact_card_neighbors p hp,inter_eq_left.mpr all,G.card_neighborFinset_eq_degree] at costs
  have sub : p.support.toFinset.filter (fun v => G.dist z v=2) ⊆ univ.filter (fun v => G.dist z v=2) :=
    fun w hw => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hw).2⟩
  have := card_le_card sub
  omega

/-- When the unique low vertex is in the four-vertex exterior, a tight
tail brings it onto another longest path. -/
theorem tetrahedron (p : G.Walk a b) (hp : p.IsPath)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {z : V} (old : z∉p.support) (high : ∀ w, w≠z → 5 ≤ G.degree w)
    (retain : ∀ w, w≠z → w∉p.support → 3 ≤ (G.neighborFinset w \ p.support.toFinset).card)
    (order : Fintype.card V ≤ 19) (size : (p.support.toFinsetᶜ : Finset V).card=4) :
    ∃ c d, ∃ q : G.Walk c d, q.IsPath ∧ q.length=p.length ∧ z∈q.support := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  change E.card=4 at size
  obtain ⟨routes,M,card,links⟩ := Graph189FiveLowMarks.data p hp maximal z high retain order size
  obtain ⟨u,v,une,pair⟩ := card_eq_two.mp card
  obtain ⟨i,j,ij,pair⟩ : ∃ i j : Fin p.support.length, i<j ∧ M={i,j} := by
    rcases lt_or_gt_of_ne une with h|h
    · exact ⟨u,v,h,pair⟩
    · exact ⟨v,u,h,by simpa [Finset.pair_comm] using pair⟩
  have first : i∈M := by simp [pair]
  have last : j∈M := by simp [pair]
  have zE : z∈E := by simpa [E] using old
  have many := card_erase_add_one zE
  obtain ⟨x,hx,y,hy,xy⟩ := one_lt_card.mp (show 1 < (E.erase z).card by omega)
  obtain ⟨xz,xE⟩ := mem_erase.mp hx
  obtain ⟨yz,yE⟩ := mem_erase.mp hy
  have get {x y : V} (hx : x∈E) (hy : y∈E) (ne : x≠y) :
      ∃ q : G.Walk x y, q.IsPath ∧ List.Disjoint q.support p.support ∧ q.support.length=4 := by
    let X : E := ⟨x,hx⟩
    let Y : E := ⟨y,hy⟩
    obtain ⟨r,hr⟩ := routes X Y (fun eq => ne (congrArg Subtype.val eq))
    obtain ⟨q,hq,dis,lower⟩ := route_of_induced_hamilton p E (fun _ hw => by simpa [E] using hw) hr
    have sub : q.support.toFinset ⊆ E := by
      intro t ht
      apply mem_compl.mpr
      exact fun on => (List.disjoint_left.mp dis (List.mem_toFinset.mp ht)) (List.mem_toFinset.mp on)
    have ub := card_le_card sub
    rw [List.toFinset_card_of_nodup hq.support_nodup] at ub
    exact ⟨q,hq,dis,by omega⟩
  obtain ⟨q,hq,dis,qlen⟩ := get xE yE xy
  have xi := (links x xE xz i).mpr first
  have yi := (links y yE yz i).mpr first
  have xj := (links x xE xz j).mpr last
  have yj := (links y yE yz j).mpr last
  have front := prefix_of_detour p hp maximal i q hq dis yi.symm
  have middle := interval_of_detour p hp maximal i j ij q hq dis xi yj.symm
  have back := suffix_of_detour p hp maximal j q hq dis xj
  rw [qlen] at front middle back
  have total := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at total
  change p.support.length+E.card=Fintype.card V at total
  have tight : i.val=4 ∨ p.support.length=j.val+1+4 := by omega
  rcases tight with L|R
  · obtain ⟨s,hs,sd,sl⟩ := get zE xE xz.symm
    obtain ⟨c,d,r,hr,supp⟩ := splice_support p hp [] (p.support.take i.val) (p.support.drop i.val)
      (by simp) s hs sd (by simp) (by
        intro v hv
        have head : (p.support.drop i.val).head?=some p.support[i.val] := by simp [List.head?_drop]
        have value : p.support[i.val]=v := by simpa only [head,Option.mem_def,Option.some.injEq] using hv
        exact value ▸ xi.symm)
    have len := congrArg List.length supp
    simp only [List.length_append,List.length_nil,List.length_drop,sl] at len
    refine ⟨c,d,r,hr,by have := p.length_support; have := r.length_support; omega,?_⟩
    rw [supp,List.nil_append,List.mem_append]
    exact Or.inl s.start_mem_support
  · obtain ⟨s,hs,sd,sl⟩ := get xE zE xz
    obtain ⟨c,d,r,hr,supp⟩ := splice_support p hp (p.support.take (j.val+1)) (p.support.drop (j.val+1)) []
      (by simp) s hs sd (by
        intro v hv
        have last' : (p.support.take (j.val+1)).getLast?=some p.support[j.val] :=
          (congrArg List.getLast? (List.take_succ_eq_append_getElem j.isLt)).trans List.getLast?_concat
        have value : p.support[j.val]=v := by simpa only [last',Option.mem_def,Option.some.injEq] using hv
        exact value ▸ xj) (by simp)
    have len := congrArg List.length supp
    simp only [List.length_append,List.length_nil,List.length_take,sl] at len
    refine ⟨c,d,r,hr,by have := p.length_support; have := r.length_support; omega,?_⟩
    rw [supp,List.append_nil,List.mem_append]
    exact Or.inr s.end_mem_support

#print axioms isolated
#print axioms tetrahedron
end Graph189FiveLowInsertion
