import Graph189FiveLeafPorts

open SimpleGraph Finset Graph189ExteriorGap Graph189FiveLeafPorts
namespace Graph189FiveLeafNeighbors
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}

/-- In the degree-two exceptional case all omitted high vertices still
retain three neighbors outside an ordinary longest path. -/
theorem three (p : G.Walk a b) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (z : V) (degree : G.degree z=2) (high : ∀ w, w≠z → 5 ≤ G.degree w)
    (quota : ∀ w, (univ.filter (fun t => G.dist w t=2)).card ≤ 5)
    (order : Fintype.card V ≤ 16) {x : V} (xz : x≠z) (off : x∉p.support) :
    3 ≤ (G.neighborFinset x \ p.support.toFinset).card := by
  classical
  let N := G.neighborFinset x \ p.support.toFinset
  change 3 ≤ N.card
  by_contra! few
  have large := high x xz
  have sole (w : V) (xw : G.Adj x w) (ow : w∉p.support) : w=z := by
    by_contra wz
    have half := half_degree_outside_longest p hp longest off ow xw (quota x) (high w wz)
    change G.degree x ≤ 2*N.card at half
    omega
  obtain ⟨w,xw,wo⟩ := has_neighbor p hp longest off large (quota x)
  have eq := sole w xw wo
  subst w
  have ed : G.Adj x z := xw
  have zOff : z∉p.support := wo
  have singleton : N={z} := by
    ext v
    constructor
    · intro h
      exact mem_singleton.mpr (sole v ((G.mem_neighborFinset _ _).mp (mem_sdiff.mp h).1)
        (fun on => (mem_sdiff.mp h).2 (List.mem_toFinset.mpr on)))
    · rintro h
      obtain rfl := mem_singleton.mp h
      exact mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr ed,fun on => zOff (List.mem_toFinset.mp on)⟩
  have four {v u : V} (nv : G.neighborFinset v \ p.support.toFinset ⊆ {u}) (h : 5 ≤ G.degree v) :
      4 ≤ (contactPositions p v).card := by
    have sz := card_le_card nv
    rw [card_singleton] at sz
    rw [contact_card_neighbors p hp]
    have count := card_sdiff_add_card_inter (G.neighborFinset v) p.support.toFinset
    rw [G.card_neighborFinset_eq_degree] at count
    omega
  obtain ⟨i,h₀,h₂,h₄,h₆⟩ := four_marks p hp longest off (quota x) (four singleton.le large)
  by_cases third : ∃ y, G.Adj z y ∧ y∉p.support ∧ y≠x
  · obtain ⟨y,zy,yo,yx⟩ := third
    let q : G.Walk x y := .cons ed (.cons zy .nil)
    have hq : q.IsPath := Walk.IsPath.mk' (by simp [q,xz,yx.symm,zy.ne])
    have dis : List.Disjoint q.support p.support := by simp [q,List.disjoint_left,off,zOff,yo]
    have vsize : 3+p.support.length ≤ Fintype.card V := by
      have sz := card_outside_add_path p hp ({x,z,y} : Finset V) (by
        intro t ht
        simp only [mem_insert,mem_singleton] at ht
        rcases ht with rfl|rfl|rfl <;> assumption)
      simpa [xz,yx.symm,zy.ne,Nat.add_comm] using sz
    have onlyY : G.neighborFinset y \ p.support.toFinset ⊆ {z} := by
      intro d hd
      apply mem_singleton.mpr
      by_contra dz
      have yd := (G.mem_neighborFinset _ _).mp (mem_sdiff.mp hd).1
      have dOff : d∉p.support := fun h => (mem_sdiff.mp hd).2 (List.mem_toFinset.mpr h)
      have dx : d≠x := by rintro rfl; exact zy.ne.symm (sole y yd.symm yo)
      let r : G.Walk x d := .cons ed (.cons zy (.cons yd .nil))
      have hr : r.IsPath := Walk.IsPath.mk' (by simp [r,xz,yx.symm,zy.ne,yd.ne,dz.symm,dx.symm])
      have dr : List.Disjoint r.support p.support := by simp [r,List.disjoint_left,off,zOff,yo,dOff]
      have low := port_window p hp longest r hr dr h₀
      have up := port_window p hp longest r hr dr h₆
      simp only [r,Walk.support_cons,Walk.support_nil,List.length_cons,List.length_nil] at low up
      omega
    obtain ⟨j,b₀,b₂,_,b₆⟩ := four_marks p hp longest yo (quota y) (four onlyY (high y zy.ne.symm))
    have rd : List.Disjoint q.reverse.support p.support := by simpa [Walk.support_reverse] using dis
    have lo := port_window p hp longest q hq dis h₀
    have hi := port_window p hp longest q hq dis h₆
    have lo' := port_window p hp longest q.reverse hq.reverse rd b₀
    have hi' := port_window p hp longest q.reverse hq.reverse rd b₆
    simp only [Walk.support_reverse,List.length_reverse,q,Walk.support_cons,Walk.support_nil,List.length_cons,List.length_nil] at lo hi lo' hi'
    obtain ⟨ir,ie⟩ := (mem_contactPositions p x i).mp h₀
    obtain ⟨jr,je⟩ := (mem_contactPositions p y (j+2)).mp b₂
    have crossed := interval_of_detour p hp longest ⟨i,ir⟩ ⟨j+2,jr⟩ (by change i<j+2; omega) q hq dis
      (by simpa [get_at] using ie) (by simpa [get_at] using je.symm)
    change i+1+q.support.length ≤ j+2 at crossed
    simp only [q,Walk.support_cons,Walk.support_nil,List.length_cons,List.length_nil] at crossed
    omega
  · have lowN : G.neighborFinset z \ p.support.toFinset ⊆ {x} := by
      intro w hw
      apply mem_singleton.mpr
      by_contra ne
      exact third ⟨w,(G.mem_neighborFinset _ _).mp (mem_sdiff.mp hw).1,
        fun on => (mem_sdiff.mp hw).2 (List.mem_toFinset.mpr on),ne⟩
    have num := card_le_card lowN
    rw [card_singleton] at num
    have count := card_sdiff_add_card_inter (G.neighborFinset z) p.support.toFinset
    rw [G.card_neighborFinset_eq_degree,degree] at count
    have card := contact_card_neighbors p hp z
    obtain ⟨j,jm⟩ := card_pos.mp (show 0 < (contactPositions p z).card by omega)
    have range {u v : V} (uo : u∉p.support) (vo : v∉p.support) (edge : G.Adj u v)
        {l : ℕ} (hl : l∈contactPositions p u) : 2 ≤ l ∧ l+3 ≤ p.support.length := by
      let q : G.Walk u v := .cons edge .nil
      have hq : q.IsPath := Walk.IsPath.mk' (by simp [q,edge.ne])
      have dis : List.Disjoint q.support p.support := by simp [q,List.disjoint_left,uo,vo]
      simpa [q,Nat.add_assoc] using port_window p hp longest q hq dis hl
    have sep {s : ℕ} (hs : s∈contactPositions p x) : s=j ∨ s+3 ≤ j ∨ j+3 ≤ s := by
      obtain ⟨sr,se⟩ := (mem_contactPositions p x s).mp hs
      obtain ⟨jr,je⟩ := (mem_contactPositions p z j).mp jm
      have A : G.Adj p.support[s] x := by rwa [get_at p sr]
      have B : G.Adj p.support[j] z := by rwa [get_at p jr]
      rcases lt_trichotomy s j with lt|same|gt
      · exact Or.inr (Or.inl (adjacent_omitted_contact_spacing p hp longest off zOff ed ⟨s,sr⟩ ⟨j,jr⟩ lt A B))
      · exact Or.inl same
      · exact Or.inr (Or.inr (adjacent_omitted_contact_spacing p hp longest zOff off ed.symm ⟨j,jr⟩ ⟨s,sr⟩ gt B A))
    have a := range off zOff ed h₀
    have b := range off zOff ed h₆
    have c := range zOff off ed.symm jm
    have s₀ := sep h₀
    have s₂ := sep h₂
    have s₄ := sep h₄
    have s₆ := sep h₆
    have path : 14 ≤ p.support.length := by omega
    let E := (p.support.toFinsetᶜ : Finset V)
    have total := card_add_card_compl p.support.toFinset
    rw [List.toFinset_card_of_nodup hp.support_nodup] at total
    change p.support.length+E.card=Fintype.card V at total
    have pair : E={x,z} := by
      symm
      apply eq_of_subset_of_card_le (by
        intro w hw
        rcases mem_insert.mp hw with rfl|h
        · simpa [E] using off
        obtain rfl := mem_singleton.mp h
        simpa [E] using zOff)
      rw [card_pair xz]
      omega
    have only (w : V) (wo : w∉p.support) : w=x ∨ w=z := by
      have mem : w∈E := by simpa [E] using wo
      simpa only [pair,mem_insert,mem_singleton] using mem
    have A := charged_midpoint p hp longest off zOff only high quota h₀ h₂
    have B := charged_midpoint p hp longest off zOff only high quota h₂ (show i+2+2∈contactPositions p x from h₄)
    let v := p.getVert (i+1)
    let w := p.getVert (i+2+1)
    have vw : v≠w := by
      intro h
      have pi := (mem_contactPositions p x (i+6)).mp h₆
      have pl := p.length_support
      have bad := hp.getVert_injOn (show i+1 ≤ p.length by omega) (show i+2+1 ≤ p.length by omega) h
      omega
    have xv : x≠v := fun e => off (e ▸ p.getVert_mem_support _)
    have xw' : x≠w := fun e => off (e ▸ p.getVert_mem_support _)
    have sub : ({x,v,w} : Finset V) ⊆ G.neighborFinset z := by
      intro u hu
      rcases mem_insert.mp hu with rfl|h
      · exact (G.mem_neighborFinset _ _).mpr ed.symm
      rcases mem_insert.mp h with rfl|h
      · exact (G.mem_neighborFinset _ _).mpr A
      obtain rfl := mem_singleton.mp h
      exact (G.mem_neighborFinset _ _).mpr B
    have impossible := card_le_card sub
    rw [G.card_neighborFinset_eq_degree,degree] at impossible
    simp [xv,xw',vw] at impossible

#print axioms three
end Graph189FiveLeafNeighbors
