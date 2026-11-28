import Graph189UniqueOmissionExchange
import Graph189TwoMarkShift
import Graph189MatchedOrder

open SimpleGraph Finset Graph189ExteriorGap
namespace Graph189ThreeSmallExterior
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {x y : V}

theorem isolated_low (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a : V} (out : a∉p.support) (isolated : ∀ b, G.Adj a b → b∈p.support)
    (quota : (univ.filter (fun z => G.dist a z=2)).card ≤ 3) : G.degree a ≤ 2 := by
  classical
  by_contra! high
  have sub : G.neighborFinset a ⊆ p.support.toFinset :=
    fun b h => List.mem_toFinset.mpr (isolated b ((G.mem_neighborFinset _ _).mp h))
  have card := contact_card_neighbors p hp a
  rw [inter_eq_left.mpr sub,G.card_neighborFinset_eq_degree] at card
  have shift := single_positions_lt_path_shell p hp longest out (card_pos.mp (by omega))
  have incl : p.support.toFinset.filter (fun z => G.dist a z=2) ⊆
      univ.filter (fun z => G.dist a z=2) := fun z h => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2⟩
  have count := (card_le_card incl).trans quota
  omega

/-- A two-vertex component of the complement of a longest path cannot have
ambient degrees at least three and two in a graph of order at most eleven. -/
theorem no_pair (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a b : V} (ao : a∉p.support) (bo : b∉p.support) (ab : G.Adj a b)
    (onlyA : ∀ v, G.Adj a v → v∉p.support → v=b)
    (onlyB : ∀ v, G.Adj b v → v∉p.support → v=a)
    (da : 3 ≤ G.degree a) (db : 2 ≤ G.degree b)
    (quota : (univ.filter (fun z => G.dist a z=2)).card ≤ 3)
    (small : Fintype.card V ≤ 11) : False := by
  classical
  have num (u v : V) (only : ∀ w, G.Adj u w → w∉p.support → w=v) :
      G.degree u ≤ (contactPositions p u).card + 1 := by
    have ss : G.neighborFinset u \ p.support.toFinset ⊆ {v} := by
      intro w h
      exact mem_singleton.mpr (only w ((G.mem_neighborFinset _ _).mp (mem_sdiff.mp h).1)
        (fun h' => (mem_sdiff.mp h).2 (List.mem_toFinset.mpr h')))
    have bound := card_le_card ss
    rw [card_singleton] at bound
    have sum := Finset.card_sdiff_add_card_inter (G.neighborFinset u) p.support.toFinset
    have contact := contact_card_neighbors p hp u
    change _ + _ = G.degree u at sum
    omega
  obtain ⟨i,hi,j,hj,ne⟩ := one_lt_card.mp (show 1 < (contactPositions p a).card by have := num a b onlyA; omega)
  obtain ⟨l,hl⟩ := card_pos.mp (show 0 < (contactPositions p b).card by have := num b a onlyB; omega)
  have positions (u v : V) (uo : u∉p.support) (vo : v∉p.support) (uv : G.Adj u v)
      (t : ℕ) (h : t∈contactPositions p u) : 2 ≤ t ∧ t+3 ≤ p.support.length := by
    obtain ⟨tr,te⟩ := (mem_contactPositions p u t).mp h
    have attach : G.Adj p.support[t] u := by rwa [get_at p tr]
    let q : G.Walk u v := Walk.cons uv Walk.nil
    have hq : q.IsPath := Walk.IsPath.mk' (by simp [q,uv.ne])
    have hd : List.Disjoint q.support p.support := by simp [q,List.disjoint_left,uo,vo]
    have hd' : List.Disjoint q.reverse.support p.support := by
      simpa only [Walk.support_reverse,List.disjoint_reverse_left] using hd
    have front := prefix_of_detour p hp longest ⟨t,tr⟩ q.reverse hq.reverse hd' attach.symm
    have back := suffix_of_detour p hp longest ⟨t,tr⟩ q hq hd attach
    simpa [q] using And.intro front back
  have sep (t : ℕ) (h : t∈contactPositions p a) : t=l ∨ t+3 ≤ l ∨ l+3 ≤ t := by
    obtain ⟨tr,te⟩ := (mem_contactPositions p a t).mp h
    obtain ⟨lr,le⟩ := (mem_contactPositions p b l).mp hl
    have A : G.Adj p.support[t] a := by rwa [get_at p tr]
    have B : G.Adj p.support[l] b := by rwa [get_at p lr]
    rcases lt_trichotomy t l with less | eq | more
    · exact Or.inr (Or.inl (adjacent_omitted_contact_spacing p hp longest ao bo ab
        ⟨t,tr⟩ ⟨l,lr⟩ less A B))
    · exact Or.inl eq
    · exact Or.inr (Or.inr (adjacent_omitted_contact_spacing p hp longest bo ao ab.symm
        ⟨l,lr⟩ ⟨t,tr⟩ more B A))
  have total := card_outside_add_path p hp ({a,b} : Finset V) (by
    intro v hv
    simp only [mem_insert,mem_singleton] at hv
    rcases hv with rfl|rfl <;> assumption)
  simp [ab.ne] at total
  have plen := p.length_support
  have pi := positions a b ao bo ab i hi
  have pj := positions a b ao bo ab j hj
  have pl := positions b a bo ao ab.symm l hl
  have si := sep i hi
  have sj := sep j hj
  rcases lt_or_gt_of_ne ne with h|h
  · have := two_marks_exact p hp longest ao quota hi hj h
    omega
  · have := two_marks_exact p hp longest ao quota hj hi h
    omega

/-- A midpoint exchange prevents a longest path from omitting just one vertex
when all degrees are at least two, at most one is below three, and every
second layer has at most three vertices. -/
theorem not_one_omission (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (degree : ∀ v, 2 ≤ G.degree v) (highPair : ∀ u v : V, u ≠ v → 3 ≤ G.degree u ∨ 3 ≤ G.degree v)
    (quota : ∀ v, (univ.filter (fun z => G.dist v z=2)).card ≤ 3)
    {a : V} (out : a∉p.support) (sole : ∀ v : V, v ≠ a → v∈p.support) : False := by
  classical
  have isolated : ∀ v, G.Adj a v → v∈p.support := fun v e => sole v e.ne.symm
  have low := isolated_low p hp longest out isolated (quota a)
  have sub : G.neighborFinset a ⊆ p.support.toFinset := fun v h =>
    List.mem_toFinset.mpr (isolated v ((G.mem_neighborFinset _ _).mp h))
  have num := contact_card_neighbors p hp a
  rw [inter_eq_left.mpr sub,G.card_neighborFinset_eq_degree] at num
  obtain ⟨l,hl,r,hr,hne⟩ := one_lt_card.mp (show 1 < (contactPositions p a).card by
    have := degree a
    omega)
  have marks : ∃ i : ℕ, i∈contactPositions p a ∧ i+2∈contactPositions p a := by
    rcases lt_or_gt_of_ne hne with h|h
    · have e := two_marks_exact p hp longest out (quota a) hl hr h
      exact ⟨l,hl,e.symm ▸ hr⟩
    · have e := two_marks_exact p hp longest out (quota a) hr hl h
      exact ⟨r,hr,e.symm ▸ hl⟩
  obtain ⟨i,hi,hj⟩ := marks
  obtain ⟨ir,ia⟩ := (mem_contactPositions p a i).mp hi
  obtain ⟨jr,ja⟩ := (mem_contactPositions p a (i+2)).mp hj
  let m := p.getVert (i+1)
  have am : a ≠ m := fun eq => out (eq ▸ p.getVert_mem_support (i+1))
  obtain ⟨u,v,q,hq,eqlen,mo,retain⟩ := Graph189MidpointExchange.exchange p hp out i jr ia ja
  have qmax : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ q.length := by
    intro s t r hr
    rw [eqlen]
    exact longest r hr
  have mIso (t : V) (e : G.Adj m t) : t∈q.support := by
    apply retain t e.ne.symm
    by_cases h : t=a
    · exact Or.inl h
    · exact Or.inr (sole t h)
  have mlow := isolated_low q hq qmax mo mIso (quota m)
  change G.degree m ≤ 2 at mlow
  have := highPair a m am
  omega

#print axioms no_pair
#print axioms not_one_omission
end Graph189ThreeSmallExterior
