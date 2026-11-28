import Graph189LeafBlockSelection
import Graph189ExteriorHalf

namespace Graph189LeafBlockSelection
open SimpleGraph Finset Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- On either side of a leaf block of a genuine exterior component, the
remainder contains a high vertex and at least half the second degree. -/
theorem high_remainder {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    {C D : Finset V} {w : V} (side : Side G C D w)
    (conn : (G.induce (C:Set V)).Preconnected) (outside : ∀u∈C,u∉p.support)
    (component : ∀u∈C,∀v,G.Adj u v → v∉p.support → v∈C)
    {k : ℕ} (quota : ∀v,(univ.filter (fun z => G.dist v z=2)).card≤k)
    (minimum : ∀v,3≤G.degree v) (uniqueLow : ∀u v,G.degree u<k → G.degree v<k → u=v) :
    let R := C \ insert w D
    (∃y∈R,k≤G.degree y) ∧ (k+1)/2≤R.card := by
  classical
  intro R
  have neighbors {y v : V} (yr : y∈R) (vc : v∈C) (e : G.Adj y v) : v∈insert w R := by
    obtain ⟨yc,notB⟩ := mem_sdiff.mp yr
    by_cases vw : v=w
    · exact mem_insert.mpr (Or.inl vw)
    have nd : v∉D := by
      intro vd
      rcases side.boundary v vd y yc e.symm with yd|yw
      · exact notB (mem_insert_of_mem yd)
      · exact notB (mem_insert.mpr (Or.inl yw))
    exact mem_insert_of_mem (mem_sdiff.mpr ⟨vc,fun h => (mem_insert.mp h).elim vw nd⟩)
  have inside {y : V} (yr : y∈R) : G.neighborFinset y \ p.support.toFinset ⊆ insert w R := by
    intro v hv
    obtain ⟨adj,miss⟩ := mem_sdiff.mp hv
    have e := (G.mem_neighborFinset _ _).mp adj
    exact neighbors yr (component y (mem_sdiff.mp yr).1 v e (fun h => miss (List.mem_toFinset.mpr h))) e
  have high : ∃y∈R,k≤G.degree y := by
    by_contra! low
    obtain ⟨z,zr⟩ := side.remainder
    have zc := (mem_sdiff.mp zr).1
    have zw : z≠w := fun eq => (mem_sdiff.mp zr).2 (mem_insert.mpr (Or.inl eq))
    have only {u : V} (ur : u∈R) : u=z := uniqueLow u z (low u ur) (low z zr)
    have few : G.neighborFinset z \ p.support.toFinset ⊆ {w} := by
      intro u hu
      rcases mem_insert.mp (inside zr hu) with eq|ur
      · exact mem_singleton.mpr eq
      · have diff := ((G.mem_neighborFinset _ _).mp (mem_sdiff.mp hu).1).ne
        exact False.elim (diff (only ur).symm)
    have limit := card_le_card few
    rw [card_singleton] at limit
    obtain ⟨t⟩ := conn (⟨z,zc⟩ : C) ⟨w,side.attachment⟩
    obtain ⟨u,v,uz,vz,e,_⟩ := Graph189CutSides.walk_exits (fun u : C => u.val=z) t rfl (fun h => zw h.symm)
    have zv : G.Adj z v.val := uz ▸ (show G.Adj u.val v.val from e)
    have vw : v.val=w := (mem_insert.mp (neighbors zr v.property zv)).resolve_right (fun vr => vz (only vr))
    have edge : G.Adj z w := vw ▸ zv
    have wh : k≤G.degree w := by
      by_contra! wl
      exact zw (uniqueLow z w (low z zr) wl)
    have bound := adjacent_ambient_degree_sum p hp mx (outside z zc) (outside w side.attachment) edge (quota z)
    have minimumZ := minimum z
    omega
  obtain ⟨y,yr,yh⟩ := high
  have bound := (high_exterior_half p hp mx (outside y (mem_sdiff.mp yr).1) (quota y) yh minimum uniqueLow).2
  let N := G.neighborFinset y \ p.support.toFinset
  have no : y∉N := fun h => G.irrefl ((G.mem_neighborFinset _ _).mp (mem_sdiff.mp h).1)
  have sub : insert y N ⊆ insert w R := insert_subset (mem_insert_of_mem yr) (inside yr)
  have size := card_le_card sub
  have wn : w∉R := fun h => (mem_sdiff.mp h).2 (mem_insert_self _ _)
  rw [card_insert_of_notMem no,card_insert_of_notMem wn] at size
  change G.degree y≤2*N.card at bound
  exact ⟨⟨y,yr,yh⟩,by omega⟩

#print axioms high_remainder
end Graph189LeafBlockSelection
