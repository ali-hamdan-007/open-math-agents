import Graph189CutSides
import Mathlib.Data.Finset.Max
import Mathlib.Combinatorics.SimpleGraph.Finite

open SimpleGraph Finset
namespace Graph189ExteriorLeaf
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- An interior with a single possible exit in the connected region C. -/
structure Limb (G : SimpleGraph V) (C D : Finset V) (w : V) : Prop where
  nonempty : D.Nonempty
  sub : D⊆C
  gate : w∈C
  fresh : w∉D
  remainder : ∃y∈C,y∉D ∧ y≠w
  exits : ∀x∈D,∀y∈C,G.Adj x y → y∈D ∨ y=w

/-- Partition a disconnected induced subgraph, choosing a nonempty side that
avoids a prescribed vertex (also allowed to be outside the induced graph). -/
private theorem split_away (U : Finset V) (disc : ¬(G.induce (U:Set V)).Preconnected) (z : V) :
    ∃D : Finset V,D⊆U ∧ D.Nonempty ∧ z∉D ∧ (U \ D).Nonempty ∧
      ∀a∈D,∀b∈U,G.Adj a b → b∈D := by
  classical
  let H := G.induce (U:Set V)
  obtain ⟨a,b,noreach⟩ : ∃a b : U,¬H.Reachable a b := by
    by_contra! all
    exact disc all
  let root : U := if h : z∈U then ⟨z,h⟩ else a
  let D := U.filter (fun v => ∀ hv : v∈U,¬H.Reachable root ⟨v,hv⟩)
  have rootOutside : root.val∉D := fun h => (mem_filter.mp h).2 root.property (Reachable.refl _)
  have non : D.Nonempty := by
    by_contra empty
    have all (v : U) : H.Reachable root v := by
      by_contra no
      exact empty ⟨v,mem_filter.mpr ⟨v.property,fun _ => no⟩⟩
    exact noreach ((all a).symm.trans (all b))
  refine ⟨D,filter_subset _ _,non,?_,⟨root.val,mem_sdiff.mpr ⟨root.property,rootOutside⟩⟩,?_⟩
  · intro zd
    have zU := (mem_filter.mp zd).1
    have eq : root.val=z := by simp [root,zU]
    exact rootOutside (eq ▸ zd)
  intro v vd w wu edge
  refine mem_filter.mpr ⟨wu,?_⟩
  intro _ reach
  have fromW : H.Adj ⟨w,wu⟩ ⟨v,(mem_filter.mp vd).1⟩ := edge.symm
  exact (mem_filter.mp vd).2 _ (reach.trans fromW.reachable)

theorem crossing {C T : Finset V} (conn : (G.induce (C:Set V)).Preconnected)
    (sub : T⊆C) (non : T.Nonempty) {v : V} (vc : v∈C) (off : v∉T) :
    ∃x∈T,∃y∈C,y∉T ∧ G.Adj x y := by
  obtain ⟨x,hx⟩ := non
  obtain ⟨p⟩ := conn ⟨x,sub hx⟩ ⟨v,vc⟩
  obtain ⟨i,j,it,jt,edge,_⟩ := Graph189CutSides.walk_exits (fun a : C => a.val∈T) p hx off
  exact ⟨i,it,j,j.property,jt,edge⟩

/-- A genuine exterior endblock with high interior, when z is chosen to be
the possible low vertex. Its interior vertices are noncuts of C itself. -/
theorem exists_leaf {C : Finset V} (conn : (G.induce (C:Set V)).Preconnected) (z : V)
    (cut : ∃w∈C,¬(G.induce (C.erase w:Set V)).Preconnected) :
    ∃D : Finset V,∃w,Limb G C D w ∧ z∉D ∧ (G.induce (D:Set V)).Preconnected ∧
      ∀x∈D,(G.induce (C.erase x:Set V)).Preconnected ∧
        (G.induce ((insert w D).erase x:Set V)).Preconnected := by
  classical
  let candidates := univ.filter (fun D : Finset V => z∉D ∧ ∃w,Limb G C D w)
  have start : candidates.Nonempty := by
    obtain ⟨w,wc,disc⟩ := cut
    obtain ⟨T,sub,non,avoid,rest,closed⟩ := split_away _ disc z
    obtain ⟨y,hy⟩ := rest
    refine ⟨T,mem_filter.mpr ⟨mem_univ _,avoid,w,non,fun x hx => (mem_erase.mp (sub hx)).2,wc,
      fun h => (mem_erase.mp (sub h)).1 rfl,?_,?_⟩⟩
    · exact ⟨y,(mem_erase.mp (mem_sdiff.mp hy).1).2,(mem_sdiff.mp hy).2,(mem_erase.mp (mem_sdiff.mp hy).1).1⟩
    intro x xt v vc e
    by_cases eq : v=w
    · exact Or.inr eq
    exact Or.inl (closed x xt v (mem_erase.mpr ⟨eq,vc⟩) e)
  obtain ⟨D,hd,small⟩ := candidates.exists_min_image Finset.card start
  obtain ⟨avoid,w,L⟩ := (mem_filter.mp hd).2
  have minimal {T : Finset V} (sub : T⊆D) (lt : T.card<D.card) {v : V} (t : Limb G C T v) : False :=
    (Nat.not_lt_of_ge (small T (mem_filter.mpr ⟨mem_univ _,fun h => avoid (sub h),v,t⟩))) lt
  obtain ⟨u,uc,uD,uw⟩ := L.remainder
  have smaller {x : V} (xd : x∈D) {T : Finset V} (sub : T⊆D) (non : T.Nonempty) (absent : x∉T)
      (exit : ∀a∈T,∀b∈C,G.Adj a b → b∈T ∨ b=x) : False := by
    have strict := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub,fun eq => absent (eq ▸ xd)⟩)
    exact minimal sub strict ⟨non,sub.trans L.sub,L.sub xd,absent,
      ⟨u,uc,fun h => uD (sub h),fun eq => uD (eq ▸ xd)⟩,exit⟩
  refine ⟨D,w,L,avoid,?_,?_⟩
  · by_contra disc
    obtain ⟨T,sub,non,_,rem,closed⟩ := split_away D disc w
    obtain ⟨r,hr⟩ := rem
    have strict := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub,fun eq =>
      (mem_sdiff.mp hr).2 (eq ▸ (mem_sdiff.mp hr).1)⟩)
    apply minimal sub strict (v:=w)
    refine ⟨non,sub.trans L.sub,L.gate,fun h => L.fresh (sub h),⟨u,uc,fun h => uD (sub h),uw⟩,?_⟩
    intro a at_ b bc e
    exact (L.exits a (sub at_) b bc e).imp (fun bd => closed a at_ b bd e) id
  intro x xd
  constructor
  · by_contra disc
    obtain ⟨T,sub,non,wo,_,closed⟩ := split_away _ disc w
    have miss : x∉T := fun h => (mem_erase.mp (sub h)).1 rfl
    obtain ⟨v,vt,y,yc,yt,edge⟩ := crossing conn (fun _ h => (mem_erase.mp (sub h)).2) non (L.sub xd) miss
    have yx : y=x := by by_contra eq; exact yt (closed _ vt _ (mem_erase.mpr ⟨eq,yc⟩) edge)
    have vd : v∈D := (L.exits x xd v (mem_erase.mp (sub vt)).2 (yx ▸ edge.symm)).resolve_right (fun eq => wo (eq ▸ vt))
    apply smaller xd (T:=T∩D) inter_subset_right ⟨v,mem_inter.mpr ⟨vt,vd⟩⟩ (fun h => miss (mem_inter.mp h).1)
    intro a ha b bc e
    by_cases eq : b=x
    · exact Or.inr eq
    have bt := closed _ (mem_inter.mp ha).1 _ (mem_erase.mpr ⟨eq,bc⟩) e
    exact Or.inl (mem_inter.mpr ⟨bt,(L.exits _ (mem_inter.mp ha).2 _ bc e).resolve_right (fun eq => wo (eq ▸ bt))⟩)
  by_contra disc
  obtain ⟨T,sub,non,wo,_,closed⟩ := split_away _ disc w
  have subD : T⊆D := fun y yt => (mem_insert.mp (mem_erase.mp (sub yt)).2).resolve_left (fun eq => wo (eq ▸ yt))
  apply smaller xd subD non (fun h => (mem_erase.mp (sub h)).1 rfl)
  intro a at_ b bc e
  by_cases eq : b=x
  · exact Or.inr eq
  have bi : b∈insert w D := (mem_insert.mpr (L.exits a (subD at_) b bc e).symm)
  exact Or.inl (closed a at_ b (mem_erase.mpr ⟨eq,bi⟩) e)

end Graph189ExteriorLeaf
#print axioms Graph189ExteriorLeaf.exists_leaf
