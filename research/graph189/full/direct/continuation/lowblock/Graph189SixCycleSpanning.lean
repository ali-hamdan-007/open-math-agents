import Graph189CycleEdgeMarks
import Graph189ContactColumns
import Graph189OrdinaryRotationWindow

open SimpleGraph Finset Graph189ExteriorGap
namespace Graph189SixCycleSpanning
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
/-- If all non-root vertices carry a mark and successive vertices cannot
carry different marks, there is just one mark anywhere on the cycle. -/
theorem constant {z : V} (C : G.Walk z z) (hc : C.IsCycle) {I : Type*} (marks : V→I→Prop)
    (many : ∀ v∈C.support, v≠z → ∃ i, marks v i)
    (succ : ∀ a b, s(a,b)∈C.edges → ∀ i j, marks a i → marks b j → i=j) :
    ∃ t, ∀ v∈C.support, ∀ i, marks v i → i=t := by
  have three := hc.three_le_length
  have yes (i : ℕ) (nz : 0 < i) (hi : i<C.length) : ∃ t, marks (C.getVert i) t := by
    apply many _ (C.getVert_mem_support i)
    intro e
    rcases (hc.getVert_endpoint_iff (by omega)).mp e with h|h <;> omega
  have edge (i : ℕ) (hi : i<C.length) : s(C.getVert i,C.getVert (i+1))∈C.edges :=
    C.mk_mem_edges_iff_exists.mpr ⟨i,hi,rfl⟩
  obtain ⟨t,ht⟩ := yes 1 (by decide) (by omega)
  obtain ⟨s,hs⟩ := yes 2 (by decide) (by omega)
  have ts := succ _ _ (edge 1 (by omega)) t s ht hs
  have chain (j : ℕ) (inside : j+1<C.length) :
      marks (C.getVert (j+1)) t ∧ ∀ i, marks (C.getVert (j+1)) i → i=t := by
    induction j with
    | zero =>
      exact ⟨ht,fun i hi => (succ _ _ (edge 1 (by omega)) i s hi hs).trans ts.symm⟩
    | succ j ih =>
      obtain ⟨prev,_⟩ := ih (by omega)
      obtain ⟨w,hw⟩ := yes (j+1+1) (by omega) inside
      have tw := succ _ _ (edge (j+1) (by omega)) t w prev hw
      exact ⟨tw.symm ▸ hw,fun i hi => (succ _ _ (edge (j+1) (by omega)) t i prev hi).symm⟩
  have root (i : I) (hi : marks z i) : i=t := by
    have origin : marks (C.getVert 0) i := by simpa using hi
    exact succ _ _ (edge 0 (by omega)) i t origin ht
  refine ⟨t,?_⟩
  intro v hv i hi
  classical
  let n := C.support.idxOf v
  have idn : C.getVert n=v := C.getVert_support_idxOf hv
  have hn : n<C.support.length := List.idxOf_lt_length_iff.mpr hv
  have plen := C.length_support
  by_cases h0 : n=0
  · rw [h0,Walk.getVert_zero] at idn
    exact root i (idn.symm ▸ hi)
  by_cases hL : n=C.length
  · rw [hL,Walk.getVert_length] at idn
    exact root i (idn.symm ▸ hi)
  have add : n-1+1=n := by omega
  have atn := (chain (n-1) (by omega)).2
  rw [add,idn] at atn
  exact atn i hi

/-- When the entire exterior is a single spanning cycle of order q, each
high vertex with degree at least q has a path contact. At most one possible
lower degree suffices to obtain three full q-vertex intervals. -/
theorem path_lower [Fintype V] [Nontrivial V] [DecidableRel G.Adj]
    {x y z : V} (p : G.Walk x y) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (conn : 2≤G.vertexConnectivity) (C : G.Walk z z) (hc : C.IsCycle)
    (part : ∀ v, v∈C.support ↔ v∉p.support) (size : C.support.toFinset.card=C.length)
    (high : ∀ v∈C.support, v≠z → C.length≤G.degree v) :
    3*C.length+2≤p.support.length := by
  classical
  by_contra! short
  let W := C.support.toFinset
  let marks (v : V) (i : Fin p.support.length) := G.Adj p.support[i.val] v
  have off (v : V) (hv : v∈C.support) : v∉p.support := (part v).mp hv
  have apart (v : V) (hv : v∈W) : v∉p.support := off v (List.mem_toFinset.mp hv)
  have ys (v : V) (hv : v∈C.support) (nz : v≠z) : ∃ i, marks v i := by
    by_contra! none
    have inc : G.neighborFinset v⊆W.erase v := by
      intro u h
      have e := (G.mem_neighborFinset _ _).mp h
      apply mem_erase.mpr
      refine ⟨e.ne.symm,List.mem_toFinset.mpr ((part u).mpr ?_)⟩
      intro up
      obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp up
      exact none ⟨j,hj⟩ (by change G.Adj p.support[j] v; rw [eq]; exact e.symm)
    have q := card_le_card inc
    rw [G.card_neighborFinset_eq_degree,card_erase_of_mem (List.mem_toFinset.mpr hv),size] at q
    have dg := high v hv nz
    have pos := hc.three_le_length
    omega
  have same (u v : V) (e : s(u,v)∈C.edges) (i j : Fin p.support.length)
      (ui : marks u i) (vj : marks v j) : i=j := by
    rcases lt_trichotomy i j with ij|eq|ji
    · obtain ⟨l,m,r⟩ := Graph189CycleEdgeMarks.positions p hp mx C hc off e ij ui vj
      omega
    · exact eq
    · have rev : s(v,u)∈C.edges := Sym2.eq_swap ▸ e
      obtain ⟨l,m,r⟩ := Graph189CycleEdgeMarks.positions p hp mx C hc off rev ji vj ui
      omega
  obtain ⟨t,uniform⟩ := constant C hc marks ys same
  obtain ⟨width,paths,_⟩ := Graph189TwoExteriorLinks.cycle_routes C hc
  obtain ⟨_,q,hq,len,_⟩ := paths z (List.mem_toFinset.mpr C.start_mem_support)
  have n := mx q hq
  have l := q.length_support
  have l' := p.length_support
  have three := hc.three_le_length
  obtain ⟨A,inj,_⟩ := Graph189TwoExteriorLinks.arms p hp W apart 2 conn (by change 2≤C.support.toFinset.card; omega) (by omega)
  have endMark (i : Fin 2) : (A i).mark=t := by
    have ext := (A i).off _ (A i).route.end_mem_support
    exact uniform _ ((part _).mpr ext) _ (A i).contact.symm
  exact (show (0 : Fin 2)≠1 by decide) (inj ((endMark 0).trans (endMark 1).symm))

/-- A six-cycle cannot span six omissions at the original second degree
six and order at most twenty-five. -/
theorem excluded [Fintype V] [Nontrivial V] [DecidableRel G.Adj]
    {x y r : V} (p : G.Walk x y) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (conn : 2≤G.vertexConnectivity) (C : G.Walk r r) (hc : C.IsCycle) (six : C.length=6)
    (off : ∀ v∈C.support,v∉p.support) (small : p.support.toFinsetᶜ.card≤6)
    (degree : G.secondSmallestDegree=6) (order : Fintype.card V≤25) : False := by
  classical
  let E := p.support.toFinsetᶜ
  let W := C.support.toFinset
  have inside : W⊆E := fun v hv => mem_compl.mpr (fun h => off v (List.mem_toFinset.mp hv) (List.mem_toFinset.mp h))
  have lower := (Graph189TwoExteriorLinks.cycle_routes C hc).1
  change C.length≤W.card at lower
  change E.card≤6 at small
  have eq : W=E := eq_of_subset_of_card_le inside (by omega)
  have sz : W.card=6 := by
    have n := card_le_card inside
    omega
  obtain ⟨z,zW,higher⟩ : ∃ z∈W, ∀ v∈W, v≠z → 6≤G.degree v := by
    by_cases all : ∀ v∈W, 6≤G.degree v
    · exact ⟨r,List.mem_toFinset.mpr C.start_mem_support,fun v hv _ => all v hv⟩
    push Not at all
    obtain ⟨z,hz,lo⟩ := all
    refine ⟨z,hz,?_⟩
    intro v _ ne
    have h := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) v z ne
    omega
  let R := C.rotate z (List.mem_toFinset.mp zW)
  have rc : R.IsCycle := hc.rotate _
  have rotate (v : V) : v∈R.support ↔ v∈W := by
    simpa only [W,List.mem_toFinset] using (C.mem_support_rotate_iff z (List.mem_toFinset.mp zW) (w:=v))
  have support : R.support.toFinset=W := by ext v; exact List.mem_toFinset.trans (rotate v)
  have rl : R.length=6 := (C.length_rotate z _).trans six
  have part (v : V) : v∈R.support ↔ v∉p.support := by
    rw [rotate,eq]
    simp [E]
  have forced := path_lower p hp mx conn R rc part (by rw [support,rl,sz])
    (fun v hv ne => by rw [rl]; exact higher v ((rotate v).mp hv) ne)
  have n := card_outside_add_path p hp W (fun v hv => off v (List.mem_toFinset.mp hv))
  omega

#print axioms path_lower
#print axioms excluded
end Graph189SixCycleSpanning
