import Graph189CutSides
import Mathlib.Data.Finset.Powerset

open Finset SimpleGraph

namespace Graph189LeafBlockSelection

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] in
private theorem closed_piece {S : Finset V} {b : V} (bs : b∈S)
    (disc : ¬(G.induce (S:Set V)).Preconnected) :
    ∃ D : Finset V, D.Nonempty ∧ D⊆S ∧ b∉D ∧
      ∀ u∈D, ∀ v∈S, G.Adj u v → v∈D := by
  classical
  let H := G.induce (S:Set V)
  let d : S := ⟨b,bs⟩
  let D := S.filter fun v => ∀ h : v∈S, ¬ H.Reachable d ⟨v,h⟩
  obtain ⟨t,unreachable⟩ : ∃ t : S, ¬H.Reachable d t := by
    by_contra! every
    exact disc (fun x y => (every x).symm.trans (every y))
  refine ⟨D,⟨t.val,mem_filter.mpr ⟨t.property,fun _ => unreachable⟩⟩,filter_subset _ _,?_,?_⟩
  · exact fun h => (mem_filter.mp h).2 bs (Reachable.refl _)
  · intro u hu v hv e
    have us := (mem_filter.mp hu).1
    have step : H.Adj ⟨v,hv⟩ ⟨u,us⟩ := e.symm
    exact mem_filter.mpr ⟨hv,fun _ h => (mem_filter.mp hu).2 us (h.trans step.reachable)⟩

/-- A side with all its edges into the rest of C passing through one vertex. -/
structure Side (G : SimpleGraph V) (C D : Finset V) (w : V) : Prop where
  nonempty : D.Nonempty
  subset : D⊆C
  attachment : w∈C
  outside : w∉D
  remainder : (C \ insert w D).Nonempty
  boundary : ∀ u∈D, ∀ v∈C, G.Adj u v → v∈D ∨ v=w

/-- If the deletion of a vertex disconnects C, one may choose a leaf block
of C whose interior avoids any prescribed root. In this formulation the block
is its interior D together with its single attachment w. -/
theorem exists_leaf {C : Finset V} (r : V) (rc : r∈C)
    (cut : ∃ w∈C, ¬(G.induce (C.erase w:Set V)).Preconnected) :
    ∃ D : Finset V, ∃ w : V, Side G C D w ∧ r∉D ∧
      ∀ v∈insert w D, (G.induce ((insert w D).erase v:Set V)).Preconnected := by
  classical
  let Good (D : Finset V) := ∃ w : V, Side G C D w ∧ r∉D
  let family := C.powerset.filter Good
  obtain ⟨w,wc,disc⟩ := cut
  have survives : (C.erase w).Nonempty := by
    by_contra empty
    have no : (C.erase w)=∅ := not_nonempty_iff_eq_empty.mp empty
    rw [no] at disc
    exact disc (fun x => False.elim (by simpa using x.property))
  obtain ⟨b,bs,br⟩ : ∃ b∈C.erase w, r=w ∨ b=r := by
    by_cases e : r=w
    · obtain ⟨b,bs⟩ := survives
      exact ⟨b,bs,Or.inl e⟩
    · exact ⟨r,mem_erase.mpr ⟨e,rc⟩,Or.inr rfl⟩
  obtain ⟨T,tn,ts,bn,closed⟩ := closed_piece bs disc
  have nw : w∉T := fun h => (mem_erase.mp (ts h)).1 rfl
  have seed : T∈family := by
    have sub : T⊆C := ts.trans (erase_subset _ _)
    refine mem_filter.mpr ⟨mem_powerset.mpr sub,w,⟨tn,sub,wc,nw,?_,?_⟩,?_⟩
    · exact ⟨b,mem_sdiff.mpr ⟨(mem_erase.mp bs).2,fun h => (mem_insert.mp h).elim (mem_erase.mp bs).1 bn⟩⟩
    · intro u hu v hv e
      by_cases vw : v=w
      · exact Or.inr vw
      · exact Or.inl (closed u hu v (mem_erase.mpr ⟨vw,hv⟩) e)
    · rcases br with eq|eq
      · simpa only [eq] using nw
      · simpa only [←eq] using bn
  obtain ⟨D,df,least⟩ := family.exists_min_image Finset.card ⟨T,seed⟩
  obtain ⟨w,s,avoid⟩ := (mem_filter.mp df).2
  have minimal {T : Finset V} {v : V} (small : T.card<D.card)
      (side : Side G C T v) (tr : r∉T) : False :=
    (not_lt_of_ge (least T (mem_filter.mpr ⟨mem_powerset.mpr side.subset,v,side,tr⟩))) small
  refine ⟨D,w,s,avoid,?_⟩
  intro v vb
  by_cases atW : v=w
  · subst v
    rw [erase_insert s.outside]
    by_contra discD
    obtain ⟨u,ud⟩ := s.nonempty
    obtain ⟨T,tn,td,un,closed⟩ := closed_piece ud discD
    have sub : T ⊆ D.erase u := fun _ h => mem_erase.mpr ⟨fun eq => un (eq ▸ h),td h⟩
    have lt : T.card < D.card := (card_le_card sub).trans_lt (card_erase_lt_of_mem ud)
    apply minimal lt (v:=w) _ (fun h => avoid (td h))
    refine ⟨tn,td.trans s.subset,s.attachment,fun h => s.outside (td h),?_,?_⟩
    · obtain ⟨b,bh⟩ := s.remainder
      exact ⟨b,mem_sdiff.mpr ⟨(mem_sdiff.mp bh).1,fun hi =>
        (mem_sdiff.mp bh).2 (insert_subset_insert w td hi)⟩⟩
    · intro x hx y yc e
      rcases s.boundary x (td hx) y yc e with yd|same
      · exact Or.inl (closed x hx y yd e)
      · exact Or.inr same
  · have vd := (mem_insert.mp vb).resolve_left atW
    let U := (insert w D).erase v
    have wu : w∈U := mem_erase.mpr ⟨fun eq => atW eq.symm,mem_insert_self _ _⟩
    by_contra discU
    obtain ⟨T,tn,tu,wn,closed⟩ := closed_piece wu discU
    have td : T⊆D.erase v := by
      intro x hx
      obtain ⟨ne,ordinary⟩ := mem_erase.mp (tu hx)
      exact mem_erase.mpr ⟨ne,(mem_insert.mp ordinary).resolve_left (fun e => wn (e ▸ hx))⟩
    have sub := td.trans (erase_subset v D)
    have lt : T.card<D.card := (card_le_card td).trans_lt (card_erase_lt_of_mem vd)
    apply minimal lt (v:=v) _ (fun h => avoid (sub h))
    refine ⟨tn,sub.trans s.subset,s.subset vd,fun h => (mem_erase.mp (td h)).1 rfl,?_,?_⟩
    · exact ⟨w,mem_sdiff.mpr ⟨s.attachment,fun h => (mem_insert.mp h).elim (fun eq => atW eq.symm) wn⟩⟩
    · intro x hx y yc e
      by_cases eq : y=v
      · exact Or.inr eq
      have yb : y∈insert w D := by
        rcases s.boundary x (sub hx) y yc e with h|h
        · exact mem_insert_of_mem h
        · exact mem_insert.mpr (Or.inl h)
      exact Or.inl (closed x hx y (mem_erase.mpr ⟨eq,yb⟩) e)

omit [Fintype V] in
/-- The vertices outside the interior of an attached side stay connected
through its attachment. -/
theorem Side.complement_preconnected {C D : Finset V} {w : V} (s : Side G C D w)
    (conn : (G.induce (C:Set V)).Preconnected) :
    (G.induce ((C \ D : Finset V) : Set V)).Preconnected := by
  classical
  let B := C \ D
  have wb : w∈B := mem_sdiff.mpr ⟨s.attachment,s.outside⟩
  by_contra disc
  obtain ⟨T,tn,tb,wn,closed⟩ := closed_piece wb disc
  obtain ⟨b,bt⟩ := tn
  let source : C := ⟨b,(mem_sdiff.mp (tb bt)).1⟩
  let dest : C := ⟨w,s.attachment⟩
  obtain ⟨q⟩ := conn source dest
  obtain ⟨u,v,ut,vt,e,_⟩ := Graph189CutSides.walk_exits (fun t : C => t.val∈T) q bt wn
  by_cases vd : v.val∈D
  · have alternatives := s.boundary v.val vd u.val u.property e.symm
    exact alternatives.elim (mem_sdiff.mp (tb ut)).2 (fun eq => wn (eq ▸ ut))
  · exact vt (closed u.val ut v.val (mem_sdiff.mpr ⟨v.property,vd⟩) e)

omit [Fintype V] in
/-- Interior noncut vertices of the selected block are also noncut in C.
This supplies the deletion hypothesis for the optimized path exchange. -/
theorem Side.noncut {C D : Finset V} {w v : V} (s : Side G C D w)
    (conn : (G.induce (C:Set V)).Preconnected) (vd : v∈D)
    (localConn : (G.induce ((insert w D).erase v:Set V)).Preconnected) :
    (G.induce (C.erase v:Set V)).Preconnected := by
  classical
  let L := (insert w D).erase v
  let R := C \ D
  let U := C.erase v
  have ne : w≠v := fun eq => s.outside (eq ▸ vd)
  have wl : w∈L := mem_erase.mpr ⟨ne,mem_insert_self _ _⟩
  have wr : w∈R := mem_sdiff.mpr ⟨s.attachment,s.outside⟩
  have wu : w∈U := mem_erase.mpr ⟨ne,s.attachment⟩
  have lsub : L⊆U := by
    intro t ht
    obtain ⟨nv,mem⟩ := mem_erase.mp ht
    exact mem_erase.mpr ⟨nv,(mem_insert.mp mem).elim (fun eq => eq ▸ s.attachment) (fun h => s.subset h)⟩
  have rsub : R⊆U := by
    intro t ht
    obtain ⟨tc,td⟩ := mem_sdiff.mp ht
    exact mem_erase.mpr ⟨fun eq => td (eq ▸ vd),tc⟩
  have all (x : U) : (G.induce (U:Set V)).Reachable x ⟨w,wu⟩ := by
    by_cases h : x.val∈D
    · have xl : x.val∈L := mem_erase.mpr ⟨(mem_erase.mp x.property).1,mem_insert_of_mem h⟩
      exact (localConn ⟨x.val,xl⟩ ⟨w,wl⟩).map (G.induceHomOfLE lsub).toHom
    · have xr : x.val∈R := mem_sdiff.mpr ⟨(mem_erase.mp x.property).2,h⟩
      exact (s.complement_preconnected conn ⟨x.val,xr⟩ ⟨w,wr⟩).map (G.induceHomOfLE rsub).toHom
  exact fun x y => (all x).trans (all y).symm

#print axioms Side.noncut
#print axioms exists_leaf
end Graph189LeafBlockSelection
