import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

namespace Graph189UniversalCycle
open SimpleGraph
variable {V : Type*} {G K : SimpleGraph V}

def completeAt (G : SimpleGraph V) (z : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∨ (a = z ∨ b = z) ∧ a ≠ b
  symm := by
    constructor
    rintro a b (h|⟨hz,hn⟩)
    · exact Or.inl h.symm
    · exact Or.inr ⟨hz.symm,hn.symm⟩
  loopless := by
    constructor
    intro a h
    rcases h with h|⟨_,h⟩
    · exact G.loopless.irrefl a h
    · exact h rfl

private theorem transfer_walk {z a b : V}
    (away : ∀ a b, a ≠ z → b ≠ z → G.Adj a b → K.Adj a b)
    (p : G.Walk a b) (avoid : z ∉ p.support) :
    ∃ q : K.Walk a b, q.support = p.support ∧ q.length = p.length := by
  induction p with
  | nil => exact ⟨.nil,rfl,rfl⟩
  | @cons a b c hab p ih =>
    have rest : z ∉ p.support := fun h => avoid (by simp [h])
    obtain ⟨q,hq,hl⟩ := ih rest
    have ax : a ≠ z := by rintro rfl; exact avoid (by simp)
    have bx : b ≠ z := by rintro rfl; exact rest p.start_mem_support
    exact ⟨q.cons (away a b ax bx hab), by simp [hq], by simp [hl]⟩

theorem close_path {z a b : V} (hz : ∀ v, v ≠ z → K.Adj z v)
    (p : K.Walk a b) (hp : p.IsPath) (avoid : z ∉ p.support) (pos : 0 < p.length) :
    ∃ c : K.Walk z z, c.IsCycle ∧ c.length = p.length + 2 := by
  have ha := hz a (fun h => avoid (h ▸ p.start_mem_support))
  have hb := hz b (fun h => avoid (h ▸ p.end_mem_support))
  refine ⟨.cons ha (p.concat hb.symm),?_,by simp [Nat.add_assoc]⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  refine ⟨?_,by simp only [Walk.length_cons,Walk.length_concat]; omega⟩
  rw [Walk.tail_cons]
  exact (Walk.isPath_copy _ _ _).mpr (hp.concat avoid hb.symm)

private theorem open_cycle {z : V} (c : K.Walk z z) (hc : c.IsCycle) :
    ∃ a b, ∃ p : K.Walk a b, p.IsPath ∧ z ∉ p.support ∧
      p.length + 2 = c.length ∧ ∀ v, v ∈ p.support ↔ v ≠ z ∧ v ∈ c.support := by
  cases c with
  | nil => exact (hc.not_nil Walk.Nil.nil).elim
  | @cons _ a _ hza r =>
    have path := ((Walk.cons_isCycle_iff r hza).mp hc).1
    have rn := Walk.not_nil_of_isCycle_cons hc
    have split : r.support = r.dropLast.support ++ [z] := by
      rw [r.support_dropLast rn]
      have ne := r.support_ne_nil
      conv_lhs => rw [←List.dropLast_append_getLast ne]
      congr 1
      simp
    have nd := path.support_nodup
    rw [split,List.nodup_append] at nd
    have avoid : z ∉ r.dropLast.support := fun hz => nd.2.2 z hz z (by simp) rfl
    refine ⟨a,r.penultimate,r.dropLast,Walk.IsPath.mk' nd.1,avoid,?_,?_⟩
    · have := r.length_dropLast_add_one rn
      simp only [Walk.length_cons]
      omega
    · intro v
      rw [Walk.support_cons,split]
      simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
      constructor
      · intro hv
        exact ⟨fun h => avoid (h ▸ hv),Or.inr (Or.inl hv)⟩
      · rintro ⟨hne,h|h|h⟩
        · exact (hne h).elim
        · exact h
        · exact (hne h).elim

/-- Every longest cycle through a universal completion vertex opens to a longest
real path avoiding it, on exactly the surviving vertices of that cycle. -/
theorem longest_cycle_transfer (z : V) (hz : ∀ v, v ≠ z → K.Adj z v)
    (same : ∀ a b, a ≠ z → b ≠ z → (K.Adj a b ↔ G.Adj a b))
    {v : V} (c : K.Walk v v) (hc : c.IsCycle)
    (maximal : ∀ v (r : K.Walk v v), r.IsCycle → r.length ≤ c.length) :
    z ∈ c.support ∧ ∃ a b, ∃ p : G.Walk a b, p.IsPath ∧ z ∉ p.support ∧
      p.length + 2 = c.length ∧ (∀ v, v ∈ p.support ↔ v ≠ z ∧ v ∈ c.support) ∧
      ∀ a' b' (q : G.Walk a' b'), q.IsPath → z ∉ q.support → q.length ≤ p.length := by
  classical
  have belongs : z ∈ c.support := by
    by_contra h
    have path : c.dropLast.IsPath := by
      apply Walk.IsPath.mk'
      rw [c.support_dropLast hc.not_nil]
      exact c.tail_support_perm_dropLast_support.nodup_iff.mp hc.support_nodup
    have av : z ∉ c.dropLast.support := by
      rw [c.support_dropLast hc.not_nil]
      exact fun hz' => h (List.mem_of_mem_dropLast hz')
    have len := c.length_dropLast_add_one hc.not_nil
    have sz := hc.three_le_length
    obtain ⟨r,hr,l⟩ := close_path hz c.dropLast path av (by omega)
    have := maximal z r hr
    omega
  refine ⟨belongs,?_⟩
  obtain ⟨a,b,q,hq,avoid,sz,vertices⟩ := open_cycle (c.rotate z belongs) (hc.rotate belongs)
  obtain ⟨p,hp,pl⟩ := transfer_walk (fun a b ha hb => (same a b ha hb).mp) q avoid
  rw [Walk.length_rotate] at sz
  refine ⟨a,b,p,Walk.IsPath.mk' (by rw [hp]; exact hq.support_nodup),(by rw [hp]; exact avoid),by omega,?_,?_⟩
  · intro y
    rw [hp,vertices,Walk.mem_support_rotate_iff]
  · intro x y t ht av
    by_cases zero : t.length = 0
    · omega
    obtain ⟨r,rs,rl⟩ := transfer_walk (fun a b ha hb => (same a b ha hb).mpr) t av
    have hr : r.IsPath := Walk.IsPath.mk' (by rw [rs]; exact ht.support_nodup)
    obtain ⟨cycle,hcy,le⟩ := close_path hz r hr (by rw [rs]; exact av) (by omega)
    have := maximal z cycle hcy
    omega

theorem completeAt_longest (G : SimpleGraph V) (z : V) {v : V}
    (c : (completeAt G z).Walk v v) (hc : c.IsCycle)
    (maximal : ∀ v (r : (completeAt G z).Walk v v), r.IsCycle → r.length ≤ c.length) :
    z ∈ c.support ∧ ∃ a b, ∃ p : G.Walk a b, p.IsPath ∧ z ∉ p.support ∧
      p.length + 2 = c.length ∧ (∀ v, v ∈ p.support ↔ v ≠ z ∧ v ∈ c.support) ∧
      ∀ a' b' (q : G.Walk a' b'), q.IsPath → z ∉ q.support → q.length ≤ p.length := by
  apply longest_cycle_transfer z _ _ c hc maximal
  · exact fun v h => Or.inr ⟨Or.inl rfl,h.symm⟩
  · intro a b ha hb
    change (G.Adj a b ∨ (a = z ∨ b = z) ∧ a ≠ b) ↔ G.Adj a b
    simp [ha,hb]


/-- The same path in the literal induced graph on the surviving vertex subtype. -/
theorem longest_in_deletion (G : SimpleGraph V) (z : V) {v : V}
    (c : (completeAt G z).Walk v v) (hc : c.IsCycle)
    (maximal : ∀ v (r : (completeAt G z).Walk v v), r.IsCycle → r.length ≤ c.length) :
    ∃ a b, ∃ p : (G.induce {u | u ≠ z}).Walk a b, p.IsPath ∧ p.length+2 = c.length ∧
      (∀ u, u ∈ p.support ↔ u.val ∈ c.support) ∧
      ∀ a' b' (q : (G.induce {u | u ≠ z}).Walk a' b'), q.IsPath → q.length ≤ p.length := by
  classical
  obtain ⟨_,a,b,p,hp,avoid,sz,verts,longest⟩ := completeAt_longest G z c hc maximal
  let S : Set V := {u | u ≠ z}
  have sub : ∀ u ∈ p.support, u ∈ S := by
    intro u hu eq
    exact avoid (eq ▸ hu)
  let q := p.induce S sub
  let f := (Embedding.induce (G:=G) S).toHom
  have mapQ : q.map f = p := Walk.map_induce p sub
  have qp : q.IsPath := (Walk.isPath_map_iff_of_injective
    (f:=f) Subtype.val_injective).mp (by rw [mapQ]; exact hp)
  have ql : q.length = p.length := by
    calc
      q.length = (q.map f).length := (Walk.length_map _ _).symm
      _ = p.length := congrArg (fun walk : G.Walk a b => walk.length) mapQ
  refine ⟨_,_,q,qp,by omega,?_,?_⟩
  · intro u
    have supp : List.map Subtype.val q.support = p.support := by
      calc
        List.map Subtype.val q.support = (q.map f).support := (Walk.support_map f q).symm
        _ = p.support := congrArg (fun walk : G.Walk a b => walk.support) mapQ
    constructor
    · intro hu
      have hh : u.val ∈ p.support := by
        rw [←supp]
        exact List.mem_map.mpr ⟨u,hu,rfl⟩
      exact ((verts u.val).mp hh).2
    · intro hu
      have hh := (verts u.val).mpr ⟨u.property,hu⟩
      rw [←supp] at hh
      obtain ⟨t,ht,eq⟩ := List.mem_map.mp hh
      have et : t = u := Subtype.ext eq
      exact et ▸ ht
  · intro a' b' r path
    have avoid' : z ∉ (r.map f).support := by
      rw [Walk.support_map]
      intro hz
      obtain ⟨t,_,eq⟩ := List.mem_map.mp hz
      exact t.property eq
    have pr : (r.map f).IsPath := (Walk.isPath_map_iff_of_injective
      (f:=f) Subtype.val_injective).mpr path
    have h := longest _ _ (r.map f) pr avoid'
    simpa only [Walk.length_map,ql] using h

/-- A spanning longest cycle yields a Hamiltonian path in the deletion. -/
theorem hamiltonian_deletion [DecidableEq V] (G : SimpleGraph V) (z : V) {v : V}
    (c : (completeAt G z).Walk v v) (hc : c.IsCycle)
    (maximal : ∀ v (r : (completeAt G z).Walk v v), r.IsCycle → r.length ≤ c.length)
    (spans : ∀ a, a ∈ c.support) :
    ∃ a b, ∃ p : (G.induce {u | u ≠ z}).Walk a b, p.IsHamiltonian := by
  obtain ⟨a,b,p,hp,_,members,_⟩ := longest_in_deletion G z c hc maximal
  exact ⟨a,b,p,hp.isHamiltonian_of_mem (fun u => (members u).mpr (spans u.val))⟩

/-- A path in the literal deletion closes to a cycle of length two larger. -/
theorem close_deletion_path (G : SimpleGraph V) (z : V) {a b : {u : V | u ≠ z}}
    (p : (G.induce {u | u ≠ z}).Walk a b) (hp : p.IsPath) (positive : 0 < p.length) :
    ∃ c : (completeAt G z).Walk z z, c.IsCycle ∧ c.length = p.length+2 := by
  let f : G.induce {u | u ≠ z} →g completeAt G z :=
    { toFun := Subtype.val, map_rel' := fun h => Or.inl h }
  have path : (p.map f).IsPath := (Walk.isPath_map_iff_of_injective
    (f:=f) Subtype.val_injective).mpr hp
  have av : z ∉ (p.map f).support := by
    rw [Walk.support_map]
    intro hz
    obtain ⟨u,_,hu⟩ := List.mem_map.mp hz
    exact u.property hu
  obtain ⟨c,hc,sz⟩ := close_path (K:=completeAt G z)
    (fun v h => Or.inr ⟨Or.inl rfl,h.symm⟩) (p.map f) path av (by simpa using positive)
  exact ⟨c,hc,by simpa using sz⟩

#print axioms close_deletion_path
#print axioms hamiltonian_deletion
#print axioms longest_in_deletion
#print axioms completeAt_longest
end Graph189UniversalCycle
