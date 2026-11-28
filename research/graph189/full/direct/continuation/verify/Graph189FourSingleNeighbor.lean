import Graph189FourNarrowPorts
import Graph189ExteriorHalf

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189FourSingleNeighbor
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {a b : V}

private theorem ordered_three {A : Finset ℕ} (size : 3 ≤ A.card) :
    ∃ i ∈ A, ∃ j ∈ A, ∃ l ∈ A, i < j ∧ j < l := by
  obtain ⟨i,hi,j,hj,l,hl,ij,il,jl⟩ := two_lt_card.mp size
  rcases lt_or_gt_of_ne ij with h|h <;> rcases lt_or_gt_of_ne il with t|t <;>
    rcases lt_or_gt_of_ne jl with r|r <;> first
    | exact ⟨i,hi,j,hj,l,hl,by omega,by omega⟩
    | exact ⟨i,hi,l,hl,j,hj,by omega,by omega⟩
    | exact ⟨j,hj,i,hi,l,hl,by omega,by omega⟩
    | exact ⟨j,hj,l,hl,i,hi,by omega,by omega⟩
    | exact ⟨l,hl,i,hi,j,hj,by omega,by omega⟩
    | exact ⟨l,hl,j,hj,i,hi,by omega,by omega⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem port_window (p : G.Walk a b) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {x y : V} (q : G.Walk x y) (hq : q.IsPath) (off : List.Disjoint q.support p.support)
    {s : ℕ} (mark : s ∈ contactPositions p x) :
    q.support.length ≤ s ∧ s+1+q.support.length ≤ p.support.length := by
  obtain ⟨sr,adj⟩ := (mem_contactPositions p x s).mp mark
  have link : G.Adj p.support[s] x := by rwa [get_at p sr]
  have rev : List.Disjoint q.reverse.support p.support := by simpa [Walk.support_reverse] using off
  have front := prefix_of_detour p hp longest ⟨s,sr⟩ q.reverse hq.reverse rev link.symm
  have back := suffix_of_detour p hp longest ⟨s,sr⟩ q hq off link
  simp only [Walk.support_reverse,List.length_reverse] at front
  exact ⟨front,back⟩

/-- At second degree four, an omitted high vertex has at least two omitted
neighbors even when the unique low vertex has degree two. -/
theorem high_exterior_neighbors (p : G.Walk a b) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (z : V) (low : G.degree z=2) (high : ∀ v, v≠z → 4≤G.degree v)
    (quota : ∀ v, (univ.filter (fun w => G.dist v w=2)).card ≤ 4)
    (order : Fintype.card V ≤ 13) {x : V} (xz : x≠z) (outside : x∉p.support) :
    2 ≤ (G.neighborFinset x \ p.support.toFinset).card := by
  classical
  let E := G.neighborFinset x \ p.support.toFinset
  change 2 ≤ E.card
  by_contra! small
  have sum := card_sdiff_add_card_inter (G.neighborFinset x) p.support.toFinset
  have row := contact_card_neighbors p hp x
  change E.card + _ = G.degree x at sum
  have large := high x xz
  have row3 : 3 ≤ (contactPositions p x).card := by omega
  have shell := single_positions_lt_path_shell p hp longest outside (card_pos.mp (by omega : 0 < (contactPositions p x).card))
  have sub : p.support.toFinset.filter (fun w => G.dist x w=2) ⊆ univ.filter (fun w => G.dist x w=2) :=
    fun w h => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2⟩
  have use := (card_le_card sub).trans (quota x)
  obtain ⟨y,hy⟩ := card_pos.mp (show 0 < E.card by omega)
  have ey := (G.mem_neighborFinset _ _).mp (mem_sdiff.mp hy).1
  have yo : y∉p.support := fun mem => (mem_sdiff.mp hy).2 (List.mem_toFinset.mpr mem)
  have yz : y=z := by
    by_contra ne
    have cross := cross_contact_degree p hp longest outside yo ey (quota x)
    have gy := high y ne
    change _ + G.degree y ≤ 4+E.card at cross
    omega
  subst y
  obtain ⟨i,hi,j,hj,l,hl,ij,jl⟩ := ordered_three row3
  obtain ⟨eq1,eq2⟩ := Graph189FourNarrowPorts.three_marks_exact p hp longest outside (quota x) hi hj hl ij jl
  by_cases third : ∃ w, G.Adj z w ∧ w∉p.support ∧ w≠x
  · obtain ⟨w,zw,wo,wx⟩ := third
    let q : G.Walk x w := .cons ey (.cons zw .nil)
    have hq : q.IsPath := Walk.IsPath.mk' (by simp [q,xz,wx.symm,zw.ne])
    have dis : List.Disjoint q.support p.support := by simp [q,List.disjoint_left,outside,yo,wo]
    have wi := port_window p hp longest q hq dis hi
    have wl := port_window p hp longest q hq dis hl
    simp only [q,Walk.support_cons,Walk.support_nil,List.length_cons,List.length_nil] at wi wl
    have total := card_outside_add_path p hp ({x,z,w} : Finset V) (by
      intro v hv
      simp only [mem_insert,mem_singleton] at hv
      rcases hv with rfl|rfl|rfl <;> assumption)
    simp [xz,wx.symm,zw.ne] at total
    have := p.length_support
    omega
  · have only : G.neighborFinset z \ p.support.toFinset ⊆ {x} := by
      intro w hw
      apply mem_singleton.mpr
      by_contra ne
      exact third ⟨w,(G.mem_neighborFinset _ _).mp (mem_sdiff.mp hw).1,
        fun on => (mem_sdiff.mp hw).2 (List.mem_toFinset.mpr on),ne⟩
    have lim := card_le_card only
    rw [card_singleton] at lim
    have part := card_sdiff_add_card_inter (G.neighborFinset z) p.support.toFinset
    have contact := contact_card_neighbors p hp z
    change _+_ = G.degree z at part
    obtain ⟨t,ht⟩ := card_pos.mp (show 0 < (contactPositions p z).card by omega)
    have pair {u v : V} (uo : u∉p.support) (vo : v∉p.support) (adj : G.Adj u v)
        {s : ℕ} (hs : s∈contactPositions p u) : 2 ≤ s ∧ s+3 ≤ p.support.length := by
      let q : G.Walk u v := .cons adj .nil
      have hq : q.IsPath := Walk.IsPath.mk' (by simp [q,adj.ne])
      have dis : List.Disjoint q.support p.support := by simp [q,List.disjoint_left,uo,vo]
      have bound := port_window p hp longest q hq dis hs
      simpa [q,Nat.add_assoc] using bound
    have sep {s : ℕ} (hs : s∈contactPositions p x) : s=t ∨ s+3 ≤ t ∨ t+3 ≤ s := by
      obtain ⟨sr,se⟩ := (mem_contactPositions p x s).mp hs
      obtain ⟨tr,te⟩ := (mem_contactPositions p z t).mp ht
      have A : G.Adj p.support[s] x := by rwa [get_at p sr]
      have B : G.Adj p.support[t] z := by rwa [get_at p tr]
      rcases lt_trichotomy s t with less|same|more
      · exact Or.inr (Or.inl (adjacent_omitted_contact_spacing p hp longest outside yo ey
          ⟨s,sr⟩ ⟨t,tr⟩ less A B))
      · exact Or.inl same
      · exact Or.inr (Or.inr (adjacent_omitted_contact_spacing p hp longest yo outside ey.symm
          ⟨t,tr⟩ ⟨s,sr⟩ more B A))
    have wi := pair outside yo ey hi
    have wl := pair outside yo ey hl
    have wt := pair yo outside ey.symm ht
    have s₁ := sep hi
    have s₂ := sep hj
    have s₃ := sep hl
    have total := card_outside_add_path p hp ({x,z} : Finset V) (by
      intro v hv
      simp only [mem_insert,mem_singleton] at hv
      rcases hv with rfl|rfl <;> assumption)
    simp [xz] at total
    have := p.length_support
    omega

end Graph189FourSingleNeighbor
#print axioms Graph189FourSingleNeighbor.high_exterior_neighbors
