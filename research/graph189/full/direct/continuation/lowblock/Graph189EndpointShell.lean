import Graph189ContactColumns

open SimpleGraph Finset Graph189ExteriorGap
namespace Graph189EndpointShell
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {a b : V}

/-- When two adjacent exterior rows exhaust the metric cap and all their
contacts lie at least two positions inside the path, the initial endpoint
cannot see a contact of the first row. -/
theorem no_mark (p : G.Walk a b) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    {u v : V} (uo : u∉p.support) (vo : v∉p.support) (edge : G.Adj u v)
    (quota : (univ.filter (fun x => G.dist u x=2)).card≤
        (contactPositions p u).card+(contactPositions p v).card)
    (early : ∀ t, t∈contactPositions p u ∨ t∈contactPositions p v → 2≤t)
    {i : ℕ} (mi : i∈contactPositions p u) : ¬G.Adj a (p.getVert i) := by
  classical
  let A := contactPositions p u
  let B := contactPositions p v
  let T := crossIndices A B
  obtain ⟨count,shell⟩ := cross_position_witnesses p hp mx uo vo edge
  change T.card=A.card+B.card at count
  have positive (i : ℕ) (hi : i∈T) : 0 < i := by
    rcases mem_union.mp hi with h|h
    · rcases mem_union.mp h with h|h
      · obtain ⟨s,hs,rfl⟩ := mem_image.mp h
        have := early s (Or.inl hs)
        omega
      · obtain ⟨s,_,rfl⟩ := mem_image.mp h
        omega
    · have := early i (Or.inr (mem_sdiff.mp h).1)
      omega
  have inj : Set.InjOn p.getVert (T : Set ℕ) := by
    intro i hi j hj e
    have left := (shell i hi).1
    have right := (shell j hj).1
    have len := p.length_support
    exact hp.getVert_injOn (by change i≤p.length; omega) (by change j≤p.length; omega) e
  have no : a∉T.image p.getVert := by
    intro h
    obtain ⟨i,hi,e⟩ := mem_image.mp h
    have pos := positive i hi
    have valid := (shell i hi).1
    have len := p.length_support
    have eq : p.getVert i=p.getVert 0 := by simpa using e
    have zero := hp.getVert_injOn (by change i≤p.length; omega) (by change 0≤p.length; omega) eq
    omega
  intro hit
  have du : u≠a := fun eq => uo (eq ▸ p.start_mem_support)
  have missing : ¬G.Adj u a := by
    intro adj
    have h := mx (p.cons adj) (Walk.IsPath.mk' (by simp [uo,hp.support_nodup]))
    simp at h
  have dist := two_step_metric du missing ((mem_contactPositions p u i).mp mi).2.symm hit
  have subset : insert a (T.image p.getVert)⊆univ.filter (fun x => G.dist u x=2) := by
    intro x hx
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rcases mem_insert.mp hx with rfl|t
    · exact dist
    obtain ⟨i,hi,rfl⟩ := mem_image.mp t
    exact (shell i hi).2
  have bound := (card_le_card subset).trans quota
  rw [card_insert_of_notMem no,card_image_of_injOn inj,count] at bound
  change A.card+B.card+1≤A.card+B.card at bound
  omega

#print axioms no_mark
end Graph189EndpointShell
