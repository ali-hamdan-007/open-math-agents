import Graph189FiveTripleMatching
import Graph189TwoPortExterior

open Finset SimpleGraph Graph189ExteriorGap Graph189ExteriorDegreeCycle
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189FiveFourExterior
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {u v : V}

private theorem triple (p : G.Walk u v) (hp : p.IsPath) (t : Fin p.support.length)
    (maximal : ∀ {a b}, ∀ q : G.Walk a b, q.IsPath → p.support[t.val]∈q.support → q.length≤p.length)
    (E W : Finset V) (outside : ∀ a∈E, a∉p.support)
    (M : Finset (Fin p.support.length)) (sz : M.card=3) (f : M ↪ W)
    (attached : ∀ i : M, G.Adj p.support[i.val.val] (f i).val)
    (paths : ∀ a b : W, a≠b → ExteriorRoute p a.val b.val E.card) :
    4*E.card+3≤Fintype.card V := by
  classical
  let A := M.orderEmbOfFin (show M.card=2+1 from sz)
  let B := M.orderIsoOfFin sz
  let T (i : Fin 3) := f (B i)
  have inj : Function.Injective T := f.injective.comp B.injective
  have touch (i : Fin 3) : G.Adj p.support[(A i).val] (T i).val := attached (B i)
  have inner (i : Fin 2) : ExteriorRoute p (T i.castSucc).val (T i.succ).val E.card :=
    paths _ _ (inj.ne (ne_of_lt i.castSucc_lt_succ))
  have before := paths (T 1) (T 0) (inj.ne (by decide))
  have after := paths (T (Fin.last 2)) (T 0) (inj.ne (by decide))
  have bound := protected_matched_route_order p hp t maximal A (fun i => (T i).val) touch inner
    ⟨_,before⟩ ⟨_,after⟩
  have total := card_outside_add_path p hp E outside
  change 3*(E.card+1) ≤ p.support.length at bound
  omega

/-- At order four every pair of missing endpoints at the Ore threshold
would have two simplicial contact rows. A third row gives an impossible
matched triple. -/
theorem paths (p : G.Walk u v) (hp : p.IsPath) (t : Fin p.support.length)
    (mx : ∀ {a b}, ∀ q : G.Walk a b, q.IsPath → p.support[t.val]∈q.support → q.length≤p.length)
    (low : G.degree p.support[t.val]<G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    (k5 : G.secondSmallestDegree=5) (order : Fintype.card V≤16)
    (size : (p.support.toFinsetᶜ : Finset V).card=4) :
    let E := (p.support.toFinsetᶜ : Finset V)
    ∀ x y : E, x≠y → ∃ q : (G.induce (E : Set V)).Walk x y, q.IsHamiltonian := by
  classical
  let P := p.support.toFinset
  let E := (Pᶜ : Finset V)
  let H := G.induce (E : Set V)
  let N (x : V) := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] x)
  change E.card=4 at size
  have out (a : V) (mem : a∈E) : a∉p.support := by simpa [E,P] using mem
  have high (x : E) : 5≤G.degree x.val := k5 ▸
    (degree_pair (G:=G) x.val p.support[t.val] (fun h => out _ x.property
      (h ▸ List.getElem_mem _))).resolve_right (not_le.mpr low)
  have half (x : E) : 2≤H.degree x := by
    simpa only [k5] using protected_exterior_minimum p hp t mx low cap x
  have internal (a : E) : H.degree a=(G.neighborFinset a.val \ P).card := by
    rw [show H.degree a=_ from degree_induce_filter (E : Set V) a]
    congr 1
    ext b
    simp [E]
  have count (x : E) : G.degree x.val ≤ H.degree x+(N x.val).card := by
    have inc : G.neighborFinset x.val ∩ P ⊆ (N x.val).image (fun i => p.support[i.val]) := by
      intro w h
      obtain ⟨e,mem⟩ := mem_inter.mp h
      obtain ⟨j,hj,val⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp mem)
      exact mem_image.mpr ⟨⟨j,hj⟩,mem_filter.mpr ⟨mem_univ _,by simpa [val] using
        ((G.mem_neighborFinset _ _).mp e).symm⟩,val⟩
    have le := (card_le_card inc).trans card_image_le
    have parts := card_sdiff_add_card_inter (G.neighborFinset x.val) P
    rw [G.card_neighborFinset_eq_degree,←internal x] at parts
    omega
  have endpoint (x y : E) (ne : x≠y) (deg : H.degree x=2) : ∃ q : H.Walk x y, q.IsHamiltonian := by
    apply Graph189TerminalLeafClosure.prescribed_of_simplicial (G:=H) x y ne
    · intro a
      change Fintype.card E≤2*H.degree a
      rw [Fintype.card_coe,size]
      have := half a
      omega
    intro c e xc xe ce
    have quota : (univ.filter (fun w => G.dist x.val w=2)).card≤5 := by
      let T := univ.filter (fun w => G.dist x.val w=2)
      have no : x.val∉T := by simp [T]
      have sub : insert x.val T⊆univ.filter (fun w => Even (G.dist x.val w)) := by
        intro w hw
        rcases mem_insert.mp hw with rfl|h
        · simp
        · exact mem_filter.mpr ⟨mem_univ _,by rw [(mem_filter.mp h).2]; decide⟩
      have bound := (card_le_card sub).trans (cap x.val)
      rw [card_insert_of_notMem no,k5] at bound
      change T.card≤5
      omega
    exact adjacent_of_odd_equality p hp t mx (out _ x.property) (out _ c.property) (out _ e.property)
      xc xe (fun h => ce (Subtype.ext h)) (d:=2) (high x) (high c) ((internal x).symm.trans deg) quota
  intro x y ne
  apply Graph189TerminalLeafClosure.prescribed_of_supergraph (G:=H) le_top _
    (Graph189TerminalLeafClosure.complete_prescribed x y ne)
  intro a b different _
  change Fintype.card E+1≤H.degree a+H.degree b
  rw [Fintype.card_coe,size]
  by_contra! fail
  have da : H.degree a=2 := by have := half a; have := half b; omega
  have db : H.degree b=2 := by have := half a; have := half b; omega
  have ab : a.val≠b.val := fun h => different.ne (Subtype.ext h)
  obtain ⟨c,hc,notPair⟩ := exists_mem_notMem_of_card_lt_card (s:={a.val,b.val}) (t:=E)
    (by rw [card_pair ab,size]; decide)
  let C : E := ⟨c,hc⟩
  let W := insert c {a.val,b.val}
  have three : W.card=3 := by simp [W,card_insert_of_notMem notPair,card_pair ab]
  have inc : W⊆E := by
    intro w hw
    rcases mem_insert.mp hw with rfl|h
    · exact hc
    rcases mem_insert.mp h with rfl|h
    · exact a.property
    · exact (mem_singleton.mp h).symm ▸ b.property
  let f : W ↪ E := ⟨fun u => ⟨u.val,inc u.property⟩,fun _ _ h => Subtype.ext (congrArg Subtype.val h)⟩
  let root : W := ⟨c,mem_insert_self _ _⟩
  obtain ⟨i,hi⟩ := card_pos.mp (show 0<(N c).card by
    have max := H.degree_lt_card_verts C
    change H.degree C<Fintype.card E at max
    rw [Fintype.card_coe,size] at max
    have cc := count C
    have hh := high C
    change G.degree c≤H.degree C+(N c).card at cc
    change 5≤G.degree c at hh
    omega)
  have alternatives {u : W} (ne : u≠root) : (f u)=a ∨ (f u)=b := by
    have uc : u.val≠c := fun e => ne (Subtype.ext e)
    have mem := (mem_insert.mp u.property).resolve_left uc
    rcases mem_insert.mp mem with h|h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext (mem_singleton.mp h))
  obtain ⟨M,sz,_,attach,edges⟩ := Graph189FiveTripleMatching.forced p W three root i (mem_filter.mp hi).2 (by
    intro w ne
    have c1 := count (f w)
    have d1 := high (f w)
    have d2 : H.degree (f w)=2 := (alternatives ne).elim (fun e => e ▸ da) (fun e => e ▸ db)
    change G.degree w.val≤H.degree (f w)+(N w.val).card at c1
    change 5≤G.degree w.val at d1
    change 3≤(N w.val).card
    omega)
  have order' := triple p hp t mx E W out M sz attach edges (by
    intro u v uv
    have ne := f.injective.ne uv
    have low {w : W} (h : w≠root) : H.degree (f w)=2 :=
      (alternatives h).elim (fun e => e ▸ da) (fun e => e ▸ db)
    by_cases r : u=root
    · have other : v≠root := fun eq => uv (r.trans eq.symm)
      obtain ⟨q,hq⟩ := endpoint (f v) (f u) ne.symm (low other)
      exact route_of_induced_hamilton p E out hq.reverse
    · obtain ⟨q,hq⟩ := endpoint (f u) (f v) ne (low r)
      exact route_of_induced_hamilton p E out hq)
  omega

#print axioms paths
end Graph189FiveFourExterior
