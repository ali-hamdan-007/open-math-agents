import Graph189ThreeRegularMinimum
import Graph189ThreeSmallExterior

open SimpleGraph Finset Graph189ExteriorGap Graph189ThreeSmallExterior
namespace Graph189ThreeLowMinimum
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At order at most ten, no nontrivial longest-path exterior can occur when
only one degree can fall below three and every second layer fits three vertices. -/
theorem traceable_ten (hc : G.Connected)
    (uncut : ∀ z : V, (G.induce {v | v ≠ z}).Connected)
    (degree : ∀ v, 2 ≤ G.degree v) (highPair : ∀ u v : V, u ≠ v → 3 ≤ G.degree u ∨ 3 ≤ G.degree v)
    (quota : ∀ v, (univ.filter (fun z => G.dist v z=2)).card ≤ 3)
    (small : Fintype.card V ≤ 10) :
    ∃ x y : V, ∃ p : G.Walk x y, p.IsHamiltonian := by
  classical
  obtain ⟨z⟩ := hc.nonempty
  obtain ⟨x,y,p,hp,longest⟩ := Graph189ThreeRegularMinimum.longest_path (G:=G) z
  refine ⟨x,y,p,hp.isHamiltonian_iff.mpr ?_⟩
  intro a
  by_contra missing
  let E := univ \ p.support.toFinset
  let D (b : V) := G.neighborFinset b \ p.support.toFinset
  let S := E.filter (fun b => (D b).Nonempty)
  have emem {v : V} : v∈E ↔ v∉p.support := by simp [E]
  have dm {b c : V} : c∈D b ↔ G.Adj b c ∧ c∉p.support := by simp [D]
  have sm {b : V} : b∈S ↔ b∉p.support ∧ (D b).Nonempty := by simp [S,emem]
  have noPair {u v : V} (uo : u∉p.support) (vo : v∉p.support) (uv : G.Adj u v)
      (onlyU : ∀ w, G.Adj u w → w∉p.support → w=v)
      (onlyV : ∀ w, G.Adj v w → w∉p.support → w=u) : False := by
    rcases highPair u v uv.ne with h|h
    · exact no_pair p hp longest uo vo uv onlyU onlyV h (degree v) (quota u) (by omega)
    · exact no_pair p hp longest vo uo uv.symm onlyV onlyU h (degree u) (quota v) (by omega)
  have nonempty : S.Nonempty := by
    by_contra empty
    have isolated (u : V) (uo : u∉p.support) (v : V) (e : G.Adj u v) : v∈p.support := by
      by_contra vo
      exact empty ⟨u,sm.mpr ⟨uo,v,dm.mpr ⟨e,vo⟩⟩⟩
    have alow := isolated_low p hp longest missing (isolated a missing) (quota a)
    apply not_one_omission p hp longest degree highPair quota missing
    intro v va
    by_contra vo
    have vlow := isolated_low p hp longest vo (isolated v vo) (quota v)
    have := highPair v a va
    omega
  have boundary (u v : V) (us : u∈S) (vs : v∉S) (uv : G.Adj u v) : v∈p.support := by
    by_contra vo
    exact vs (sm.mpr ⟨vo,u,dm.mpr ⟨uv.symm,(sm.mp us).1⟩⟩)
  have route (u w : V) (us : u∈S) (wp : w∈p.support) (uw : G.Adj u w) :
      ∃ v∈D u, ∃ t∈D v, t ≠ u := by
    obtain ⟨uo,uNbr⟩ := sm.mp us
    by_contra! fail
    have only (v : V) (hv : v∈D u) (t : V) (adj : G.Adj v t) (out : t∉p.support) : t=u :=
      fail v hv t (dm.mpr ⟨adj,out⟩)
    obtain ⟨v,hv⟩ := uNbr
    obtain ⟨uv,vo⟩ := dm.mp hv
    by_cases unique : ∀ t, G.Adj u t → t∉p.support → t=v
    · exact noPair uo vo uv unique (only v hv)
    push Not at unique
    obtain ⟨t,ut,tOff,tv⟩ := unique
    have ht : t∈D u := dm.mpr ⟨ut,tOff⟩
    have highU : 3 ≤ G.degree u := by
      have sub : ({v,t,w} : Finset V) ⊆ G.neighborFinset u := by
        intro q h
        simp only [mem_insert,mem_singleton] at h
        rcases h with rfl|rfl|rfl <;> apply (G.mem_neighborFinset _ _).mpr <;> assumption
      have vw : v ≠ w := by rintro rfl; exact vo wp
      have tw : t ≠ w := by rintro rfl; exact tOff wp
      have size := card_le_card sub
      rw [card_triple_eq_three_iff.mpr ⟨tv.symm,vw,tw⟩] at size
      exact size
    have low (b : V) (hb : b∈D u) : G.degree b ≤ 2 := by
      obtain ⟨ub,bo⟩ := dm.mp hb
      have size : (D b).card ≤ 1 := by
        have sub : D b ⊆ {u} := fun t h => mem_singleton.mpr (fail b hb t h)
        simpa using card_le_card sub
      have bound := half_degree_outside_longest p hp longest bo uo ub.symm (quota b) highU
      change G.degree b ≤ 2*(D b).card at bound
      omega
    have vl := low v hv
    have tl := low t ht
    have := highPair t v tv
    omega
  have tails (u : V) (us : u∈S) (i : Fin p.support.length) (e : G.Adj p.support[i.val] u) :
      3 ≤ i.val ∧ i.val+4 ≤ p.support.length ∧ 3 ≤ E.card := by
    have uo := (sm.mp us).1
    obtain ⟨v,hv,t,ht,tu⟩ := route u _ us (List.getElem_mem _) e.symm
    obtain ⟨uv,vo⟩ := dm.mp hv
    obtain ⟨vt,tOff⟩ := dm.mp ht
    let q : G.Walk u t := Walk.cons uv (Walk.cons vt Walk.nil)
    have hq : q.IsPath := Walk.IsPath.mk' (by simp [q,uv.ne,vt.ne,tu.symm])
    have hd : List.Disjoint q.support p.support := by simp [q,List.disjoint_left,uo,vo,tOff]
    have hd' : List.Disjoint q.reverse.support p.support := by
      simpa only [Walk.support_reverse,List.disjoint_reverse_left] using hd
    have front := prefix_of_detour p hp longest i q.reverse hq.reverse hd' e.symm
    have back := suffix_of_detour p hp longest i q hq hd e
    have sub : ({u,v,t} : Finset V) ⊆ E := by
      intro b hb
      simp only [mem_insert,mem_singleton] at hb
      rcases hb with rfl|rfl|rfl <;> apply emem.mpr <;> assumption
    have count := card_le_card sub
    rw [card_triple_eq_three_iff.mpr ⟨uv.ne,tu.symm,vt.ne⟩] at count
    have pathLength := p.length_support
    simp [q] at front back
    omega
  obtain ⟨u,us⟩ := nonempty
  have xp : x∉S := fun h => (sm.mp h).1 p.start_mem_support
  obtain ⟨r⟩ := hc u x
  obtain ⟨d,_,din,dout⟩ := r.exists_boundary_dart (S : Set V) us xp
  have onP := boundary d.fst d.snd din dout d.adj
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp onP
  have attach : G.Adj p.support[i] d.fst := by simpa only [eq] using d.adj.symm
  have ti := tails d.fst din ⟨i,hi⟩ attach
  change 3 ≤ i ∧ i+4 ≤ p.support.length ∧ 3 ≤ E.card at ti
  have total := card_outside_add_path p hp E (fun _ h => emem.mp h)
  have xw : x ≠ d.snd := by
    intro same
    have e : p.getVert i = p.getVert 0 := by rw [←get_at p hi,eq,Walk.getVert_zero,same]
    have sz := p.length_support
    have iz := hp.getVert_injOn (show i ≤ p.length by omega) (show 0 ≤ p.length by omega) e
    omega
  have uw : u ≠ d.snd := by rintro eq'; exact dout (eq' ▸ us)
  let U := {v : V // v ≠ d.snd}
  let u' : U := ⟨u,uw⟩
  let x' : U := ⟨x,xw⟩
  obtain ⟨r'⟩ := uncut d.snd u' x'
  obtain ⟨f,_,fin,fout⟩ := r'.exists_boundary_dart {b : U | b.val∈S} us xp
  have onP' := boundary f.fst.val f.snd.val fin fout f.adj
  obtain ⟨j,hj,eq'⟩ := List.mem_iff_getElem.mp onP'
  have attach' : G.Adj p.support[j] f.fst.val := by simpa only [eq'] using (show G.Adj f.snd.val f.fst.val from f.adj.symm)
  have tj := tails f.fst.val fin ⟨j,hj⟩ attach'
  change 3 ≤ j ∧ j+4 ≤ p.support.length ∧ 3 ≤ E.card at tj
  have same : i=j := by omega
  subst j
  exact f.snd.property (eq'.symm.trans eq)

#print axioms traceable_ten
end Graph189ThreeLowMinimum
