import Graph189LeafBlockRemainder
import Graph189RootedOneLow

open SimpleGraph Finset Graph189ExteriorGap

namespace Graph189LeafBlockSelection
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Count an induced degree directly on the ambient vertex Finset, retaining
the chosen instance on the induced vertex type. -/
theorem degree_in (D : Finset V) (x : D) :
    (G.neighborFinset x.val∩D).card=(G.induce (D:Set V)).degree x := by
  classical
  let H := G.induce (D:Set V)
  let f : D ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have eq : (H.neighborFinset x).map f=G.neighborFinset x.val∩D := by
    ext t
    constructor
    · intro ht
      obtain ⟨u,hu,rfl⟩ := mem_map.mp ht
      exact mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ((H.mem_neighborFinset _ _).mp hu),u.property⟩
    · intro ht
      obtain ⟨adj,inside⟩ := mem_inter.mp ht
      exact mem_map.mpr ⟨⟨t,inside⟩,(H.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp adj),rfl⟩
  have h := congrArg Finset.card eq
  rw [card_map,H.card_neighborFinset_eq_degree] at h
  exact h.symm

/-- From an exterior leaf's attachment one can enter the remainder and traverse
at least ceil(k/2) distinct remainder vertices, even if the unique low
vertex lies there. The returned route is entirely inside the induced remainder. -/
theorem rooted_tail {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    {C D : Finset V} {w : V} (side : Side G C D w)
    (conn : (G.induce (C:Set V)).Preconnected) (outside : ∀u∈C,u∉p.support)
    (component : ∀u∈C,∀v,G.Adj u v → v∉p.support → v∈C)
    {k : ℕ} (large : 3≤k) (quota : ∀v,(univ.filter (fun z => G.dist v z=2)).card≤k)
    (minimum : ∀v,3≤G.degree v) (uniqueLow : ∀u v,G.degree u<k → G.degree v<k → u=v) :
    let R := C \ insert w D
    ∃ e t : R, G.Adj w e.val ∧ ∃ q : (G.induce (R : Set V)).Walk e t,
      q.IsPath ∧ (k+1)/2 ≤ q.support.length := by
  classical
  intro R
  let H := G.induce (R:Set V)
  let h := (k+1)/2
  have wh : w∉R := fun hw => (mem_sdiff.mp hw).2 (mem_insert_self _ _)
  have degree (y : R) (hi : k≤G.degree y.val) : h-1≤H.degree y := by
    let N := G.neighborFinset y.val \ p.support.toFinset
    have yc := (mem_sdiff.mp y.property).1
    have yn := (mem_sdiff.mp y.property).2
    have bound := (high_exterior_half p hp mx (outside y.val yc) (quota y.val) hi minimum uniqueLow).2
    have sub : N ⊆ insert w (G.neighborFinset y.val∩R) := by
      intro v hv
      obtain ⟨adj,no⟩ := mem_sdiff.mp hv
      have e := (G.mem_neighborFinset _ _).mp adj
      have vc := component y.val yc v e (fun hit => no (List.mem_toFinset.mpr hit))
      by_cases eq : v=w
      · exact mem_insert.mpr (Or.inl eq)
      have nd : v∉D := by
        intro vd
        rcases side.boundary v vd y.val yc e.symm with hit|eq
        · exact yn (mem_insert_of_mem hit)
        · exact yn (mem_insert.mpr (Or.inl eq))
      exact mem_insert_of_mem (mem_inter.mpr ⟨adj,mem_sdiff.mpr ⟨vc,fun t => (mem_insert.mp t).elim eq nd⟩⟩)
    have size := (card_le_card sub).trans (card_insert_le _ _)
    rw [degree_in R y] at size
    change N.card ≤ H.degree y+1 at size
    change G.degree y.val≤2*N.card at bound
    dsimp [h]
    omega
  have pair (x y : R) (diff : x≠y) : h-1≤H.degree x ∨ h-1≤H.degree y := by
    by_cases high : k≤G.degree x.val
    · exact Or.inl (degree x high)
    apply Or.inr
    apply degree
    by_contra! low
    exact diff (Subtype.ext (uniqueLow _ _ (by omega) low))
  obtain ⟨⟨y,yr,yh⟩,_⟩ := high_remainder p hp mx side conn outside component quota minimum uniqueLow
  let Y : R := ⟨y,yr⟩
  have init : ∃z,H.Adj Y z := by
    have d := degree Y yh
    have positive : 0 < (H.neighborFinset Y).card := by
      rw [H.card_neighborFinset_eq_degree]
      dsimp [h] at d
      omega
    obtain ⟨z,hz⟩ := card_pos.mp positive
    exact ⟨z,(H.mem_neighborFinset _ _).mp hz⟩
  let R' := C \ D
  let start : R' := ⟨y,mem_sdiff.mpr ⟨(mem_sdiff.mp yr).1,
    fun h => (mem_sdiff.mp yr).2 (mem_insert_of_mem h)⟩⟩
  let finish : R' := ⟨w,mem_sdiff.mpr ⟨side.attachment,side.outside⟩⟩
  let S (u : R') := ∃ hu : u.val∈R, ∃z : R,H.Adj ⟨u.val,hu⟩ z
  obtain ⟨route⟩ := side.complement_preconnected conn start finish
  obtain ⟨u,v,us,vs,uv,_⟩ := Graph189CutSides.walk_exits S route ⟨yr,init⟩
    (fun z => wh z.choose)
  obtain ⟨ur,z,link⟩ := us
  let U : R := ⟨u.val,ur⟩
  have vw : v.val=w := by
    by_contra diff
    obtain ⟨vc,vd⟩ := mem_sdiff.mp v.property
    have vr : v.val∈R := mem_sdiff.mpr ⟨vc,fun t => (mem_insert.mp t).elim diff vd⟩
    exact vs ⟨vr,U,uv.symm⟩
  have wu : G.Adj w u.val := vw ▸ (show G.Adj v.val u.val from uv.symm)
  obtain ⟨t,q,hq,len⟩ := Graph189RootedOneLow.rooted_path (H:=H) U (d:=h-1) ⟨z,link⟩ pair
  have pos : 0<h := by dsimp [h]; omega
  exact ⟨U,t,wu,q,hq,by change h≤q.support.length; omega⟩

#print axioms rooted_tail
end Graph189LeafBlockSelection
