import Graph189PrescribedBatch
import Graph189ExteriorPopulation

open Finset SimpleGraph
namespace Graph189LongPathClosure
variable {V : Type*} {G : SimpleGraph V}

/-- Replace an added edge by an unused common neighbor. A simple path uses
the added edge at most once, so the replacement remains simple. -/
private theorem route_common {a b c : V} (ac : G.Adj a c) (bc : G.Adj b c)
    {u v : V} (p : (G ⊔ edge a b).Walk u v) (hp : p.IsPath) (fresh : c∉p.support) :
    ∃ q : G.Walk u v, q.IsPath ∧ p.support ⊆ q.support ∧
      (∀ t∈q.support, t∈p.support ∨ t=c) ∧ (c∈q.support → a∈p.support ∧ b∈p.support) := by
  induction p with
  | nil =>
    refine ⟨.nil,by simp,fun _ h => h,fun _ h => Or.inl h,fun h => (fresh h).elim⟩
  | @cons u v w e p ih =>
    have xn : u∉p.support := (List.nodup_cons.mp hp.support_nodup).1
    have cu : c≠u := fun eq => fresh (by simp [eq])
    have cf : c∉p.support := fun h => fresh (by simp [h])
    obtain ⟨q,hq,contains,extra,ifc⟩ := ih hp.of_cons cf
    have outside : u∉q.support := by
      intro h
      exact (extra u h).elim xn cu.symm
    by_cases old : G.Adj u v
    · refine ⟨.cons old q,hq.cons outside,?_,?_,?_⟩
      · simpa only [Walk.support_cons] using List.cons_subset_cons u contains
      · intro t ht
        rcases List.mem_cons.mp ht with rfl|h
        · exact Or.inl (by simp)
        · exact (extra t h).imp_left (fun mem => List.mem_cons_of_mem _ mem)
      · intro h
        have both := ifc ((List.mem_cons.mp h).resolve_left cu)
        exact ⟨List.mem_cons_of_mem _ both.1,List.mem_cons_of_mem _ both.2⟩
    · obtain ⟨orient,_⟩ := (edge_adj a b u v).mp (e.resolve_left old)
      have ua : u=a ∨ u=b := orient.imp (fun h => h.1) (fun h => h.1)
      have unused : c∉q.support := fun h => ua.elim (fun eq => xn (eq ▸ (ifc h).1)) (fun eq => xn (eq ▸ (ifc h).2))
      have first : G.Adj u c := ua.elim (fun eq => eq ▸ ac) (fun eq => eq ▸ bc)
      have last : G.Adj c v := orient.elim (fun h => h.2 ▸ bc.symm) (fun h => h.2 ▸ ac.symm)
      refine ⟨.cons first (.cons last q),(hq.cons unused).cons (by simp [outside,cu.symm]),?_,?_,?_⟩
      · intro t ht
        rcases List.mem_cons.mp ht with rfl|h
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (contains h))
      · intro t ht
        rcases List.mem_cons.mp ht with rfl|h
        · exact Or.inl (by simp)
        rcases List.mem_cons.mp h with rfl|h
        · exact Or.inr rfl
        exact (extra t h).imp_left (fun mem => List.mem_cons_of_mem _ mem)
      · intro _
        rcases orient with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [p.start_mem_support]

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- An Ore edge of degree sum at least n+1 preserves every prescribed
endpoint path lower bound, even if the exhibited path is not spanning. -/
theorem long_of_sup_edge {a b u v : V} (degree : Fintype.card V+1 ≤ G.degree a+G.degree b)
    (p : (G⊔edge a b).Walk u v) (hp : p.IsPath) :
    ∃ q : G.Walk u v, q.IsPath ∧ p.support.length ≤ q.support.length := by
  classical
  let U := p.support.toFinset
  by_cases common : ∃ c, c∉p.support ∧ G.Adj a c ∧ G.Adj b c
  · obtain ⟨c,fresh,ac,bc⟩ := common
    obtain ⟨q,path,sub,_,_⟩ := route_common ac bc p hp fresh
    have cmp := card_le_card (show p.support.toFinset ⊆ q.support.toFinset from
      fun t h => List.mem_toFinset.mpr (sub (List.mem_toFinset.mp h)))
    rw [List.toFinset_card_of_nodup hp.support_nodup,List.toFinset_card_of_nodup path.support_nodup] at cmp
    exact ⟨q,path,cmp⟩
  let H := G.induce (U : Set V)
  let K := (G⊔edge a b).induce (U : Set V)
  have reach (t : V) (ht : t∈p.support) : t∈(U : Set V) := List.mem_toFinset.mpr ht
  let r := p.induce (U : Set V) reach
  let lift := (Embedding.induce (G:=G⊔edge a b) (U : Set V)).toHom
  have mapped : r.map lift=p := Walk.map_induce p reach
  have hPath : r.IsPath := (Walk.isPath_map_iff_of_injective (f:=lift) Subtype.val_injective).mp
    (by rw [mapped]; exact hp)
  have hHamilton : r.IsHamiltonian := hPath.isHamiltonian_of_mem (by
    intro t
    have mem : t.val∈p.support := List.mem_toFinset.mp t.property
    have supp : r.support.map lift=p.support := (Walk.support_map lift r).symm.trans
      (congrArg (fun w : (G⊔edge a b).Walk u v => w.support) mapped)
    rw [←supp] at mem
    obtain ⟨z,hz,eq⟩ := List.mem_map.mp mem
    exact (Subtype.ext eq : z=t) ▸ hz)
  have bound (x y : U) (xy : K.Adj x y) (missing : ¬H.Adj x y) :
      Fintype.card U + 1 ≤ H.degree x+H.degree y := by
    obtain ⟨orient,_⟩ := (edge_adj a b x.val y.val).mp (xy.resolve_left missing)
    have d : Fintype.card V+1 ≤ G.degree x.val+G.degree y.val := by
      rcases orient with h|h <;> rw [h.1,h.2] <;> omega
    let A := G.neighborFinset x.val
    let B := G.neighborFinset y.val
    have dis : Disjoint (A \ U) (B \ U) := by
      rw [Finset.disjoint_left]
      intro c ca cb
      have off : c∉p.support := fun h => (mem_sdiff.mp ca).2 (List.mem_toFinset.mpr h)
      have cx := (G.mem_neighborFinset _ _).mp (mem_sdiff.mp ca).1
      have cy := (G.mem_neighborFinset _ _).mp (mem_sdiff.mp cb).1
      rcases orient with h|h <;> rw [h.1] at cx <;> rw [h.2] at cy
      · exact common ⟨c,off,cx,cy⟩
      · exact common ⟨c,off,cy,cx⟩
    have loss := card_le_card (show (A \ U) ∪ (B \ U) ⊆ Uᶜ from by
      intro t ht
      exact mem_compl.mpr ((mem_union.mp ht).elim (fun h => (mem_sdiff.mp h).2) (fun h => (mem_sdiff.mp h).2)))
    rw [card_union_of_disjoint dis] at loss
    have ax := card_sdiff_add_card_inter A U
    have by' := card_sdiff_add_card_inter B U
    change Fintype.card V+1 ≤ A.card+B.card at d
    have count := card_add_card_compl U
    change Fintype.card U+1 ≤ (G.induce (U : Set V)).degree x+(G.induce (U : Set V)).degree y
    rw [Fintype.card_coe,Graph189ExteriorDegreeCycle.degree_induce_filter,Graph189ExteriorDegreeCycle.degree_induce_filter]
    have filter (s : Finset V) : s.filter (fun v => v∈(U : Set V))=s∩U := by ext v; simp
    rw [filter,filter]
    change U.card+1 ≤ (A∩U).card+(B∩U).card
    omega
  obtain ⟨q,hq⟩ := Graph189TerminalLeafClosure.prescribed_of_supergraph (G:=H) (H:=K)
    (fun _ _ h => Or.inl h) bound ⟨r,hHamilton⟩
  let inc := (Embedding.induce (G:=G) (U : Set V)).toHom
  refine ⟨q.map inc,hq.isPath.map Subtype.val_injective,?_⟩
  have size : (q.map inc).support.length=q.support.length := by rw [Walk.support_map,List.length_map]
  have card : Fintype.card U=p.support.length := (Fintype.card_coe _).trans (List.toFinset_card_of_nodup hp.support_nodup)
  exact le_of_eq (size.trans (hq.length_support.trans card)).symm

/-- Close a finite batch of Ore edges while retaining prescribed endpoints
and a lower bound on the number of path vertices. -/
theorem long_of_supergraph {K : SimpleGraph V} (incl : G ≤ K)
    (degree : ∀ x y, K.Adj x y → ¬G.Adj x y → Fintype.card V+1 ≤ G.degree x+G.degree y)
    {u v : V} (p : K.Walk u v) (hp : p.IsPath) :
    ∃ q : G.Walk u v, q.IsPath ∧ p.support.length ≤ q.support.length := by
  classical
  suffices all : ∀ J : SimpleGraph V, G≤J → J≤K →
      ∃ q : J.Walk u v, q.IsPath ∧ p.support.length ≤ q.support.length by
    exact all G le_rfl incl
  intro J
  induction J using WellFoundedGT.induction with
  | ind J ih =>
    intro lower upper
    by_cases eq : J=K
    · subst J
      exact ⟨p,hp,le_rfl⟩
    have miss : ∃ a b, K.Adj a b ∧ ¬J.Adj a b := by
      by_contra! all
      exact eq (le_antisymm upper fun a b hab => all a b hab)
    obtain ⟨a,b,ab,missing⟩ := miss
    have extra : edge a b ≤ K := by
      intro x y xy
      obtain ⟨h,_⟩ := (edge_adj a b x y).mp xy
      rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ab
      · exact ab.symm
    have strict : J < J⊔edge a b := by
      apply lt_of_le_of_ne le_sup_left
      intro same
      have ad : (J⊔edge a b).Adj a b := Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,ab.ne⟩)
      exact missing (same.symm ▸ ad)
    obtain ⟨r,hr,sz⟩ := ih _ strict (lower.trans le_sup_left) (sup_le upper extra)
    have d := (degree a b ab (fun h => missing (lower h))).trans
      (Nat.add_le_add (degree_le_of_le (v:=a) lower) (degree_le_of_le (v:=b) lower))
    obtain ⟨q,hq,size⟩ := long_of_sup_edge d r hr
    exact ⟨q,hq,sz.trans size⟩

end Graph189LongPathClosure
#print axioms Graph189LongPathClosure.long_of_sup_edge

#print axioms Graph189LongPathClosure.long_of_supergraph
