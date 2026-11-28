import Graph189ActualExteriorComponent

namespace Graph189ConeComponentOrder
open SimpleGraph Finset Graph189ExteriorGap

/-- For two distinct vertices on a cycle, the longer of the two genuine arcs
supplies the rounded half-length, regardless of the cyclic ordering. -/
theorem half_cycle_arc {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {r a b : V} (C : G.Walk r r) (hc : C.IsCycle)
    (ha : a∈C.support) (hb : b∈C.support) (ne : a≠b) :
    ∃ q : G.Walk a b, q.IsPath ∧ (C.length+1)/2+1 ≤ q.support.length := by
  let R := C.rotate a ha
  have rc : R.IsCycle := hc.rotate ha
  have on : b∈R.support := (C.mem_support_rotate_iff a ha).mpr hb
  let L := R.takeUntil b on
  let T := R.dropUntil b on
  have split : L.append T = R := R.take_spec on
  have cyc : (L.append T).IsCycle := split ▸ rc
  have lp : L.IsPath := rc.isPath_takeUntil on
  have tp : T.IsPath := cyc.isPath_of_append_right (L.not_nil_of_ne ne)
  have count : L.length+T.length=C.length := by
    rw [← Walk.length_append,split]
    exact C.length_rotate _ _
  by_cases large : (C.length+1)/2 ≤ L.length
  · exact ⟨L,lp,by rw [L.length_support]; omega⟩
  · exact ⟨T.reverse,T.isPath_reverse_iff.mpr tp,by rw [Walk.length_support,Walk.length_reverse]; omega⟩

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {x y : V}

/-- Any genuine Hamilton cycle in a component converts an unordered boundary
matching into two full exterior tails and half-cycle detours in every gap.
No Hamilton-connectedness or prescribed endpoint theorem is needed. -/
theorem cycle_matching_order (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ q : G.Walk a b, q.IsPath → q.length≤p.length)
    (K : Finset V) (outside : ∀ a∈K, a∉p.support)
    {r : K} (C : (G.induce (K:Set V)).Walk r r) (hc : C.IsHamiltonianCycle)
    (M : Finset V) (some : M.Nonempty) (on : ∀ a∈M, a∈p.support)
    (f : M ↪ K) (edges : ∀ a : M, G.Adj a.val (f a).val) :
    3*K.card + 1 + (M.card-1)*((K.card+1)/2+2) ≤ Fintype.card V := by
  classical
  obtain ⟨marks,e,vals⟩ := vertex_positions_equiv p M on
  have sz : marks.card = M.card := by simpa using Fintype.card_congr e
  let j := M.card-1
  have cnt : marks.card=j+1 := by
    have h := Finset.card_pos.mpr some
    dsimp [j]; omega
  let iso := marks.orderIsoOfFin cnt
  let mark := marks.orderEmbOfFin cnt
  let port (i : Fin (j+1)) := f (e (iso i))
  have contact (i : Fin (j+1)) : G.Adj p.support[(mark i).val] (port i).val := by
    rw [show p.support[(mark i).val]=(e (iso i)).val from vals (iso i)]
    exact edges _
  let emb := Embedding.induce (G:=G) (K:Set V)
  have lift {a b : K} (q : (G.induce (K:Set V)).Walk a b) (hq : q.IsPath) :
      ExteriorRoute p a.val b.val q.support.length := by
    refine ⟨q.map emb.toHom,hq.map emb.injective,?_,?_⟩
    · rw [List.disjoint_left]
      intro v hv hit
      change v∈(q.map emb.toHom).support at hv
      rw [Walk.support_map] at hv
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hv
      exact outside _ w.property hit
    · change q.support.length≤(q.map emb.toHom).support.length
      rw [Walk.support_map,List.length_map]
  have cycleLen : C.length = K.card := by simpa using hc.length_eq
  have middle (i : Fin j) : ExteriorRoute p (port i.castSucc).val (port i.succ).val ((K.card+1)/2+1) := by
    have distinct : port i.castSucc ≠ port i.succ :=
      (f.injective.comp (e.injective.comp iso.injective)).ne (ne_of_lt i.castSucc_lt_succ)
    obtain ⟨q,hq,sz⟩ := half_cycle_arc C hc.isCycle (hc.mem_support _) (hc.mem_support _) distinct
    obtain ⟨t,ht,hd,le⟩ := lift q hq
    rw [cycleLen] at sz
    exact ⟨t,ht,hd,sz.trans le⟩
  have tail (a : K) : ∃ b : K, ExteriorRoute p a.val b.val K.card := by
    let R := C.rotate a (hc.mem_support a)
    have rc : R.IsCycle := hc.isCycle.rotate (hc.mem_support a)
    have len : R.length=K.card := (C.length_rotate _ _).trans cycleLen
    have size := R.length_dropLast_add_one rc.not_nil
    obtain ⟨t,ht,hd,le⟩ := lift R.dropLast rc.isPath_dropLast
    rw [Walk.length_support] at le
    exact ⟨_,t,ht,hd,by omega⟩
  obtain ⟨a,t,ht,hd,le⟩ := tail (port 0)
  obtain ⟨b,q,hq,hqdis,hle⟩ := tail (port (Fin.last j))
  have before : ExteriorRoute p a.val (port 0).val K.card :=
    ⟨t.reverse,t.isPath_reverse_iff.mpr ht,by simpa using hd,by simpa using le⟩
  have bound := longest_matched_route_order p hp longest mark (fun i => (port i).val)
    contact middle ⟨a.val,before⟩ ⟨b.val,q,hq,hqdis,hle⟩
  rw [show (K.card+1)/2+1+1 = (K.card+1)/2+2 by omega] at bound
  have pop := card_outside_add_path p hp K outside
  change 3*K.card+1+j*((K.card+1)/2+2) ≤ _
  omega

/-- Connectivity produces the distinct contact edges automatically for an
entire exterior component carrying a spanning cycle. -/
theorem component_cycle_order (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ q : G.Walk a b, q.IsPath → q.length≤p.length)
    (K : Finset V) (outside : ∀ a∈K, a∉p.support)
    (boundary : ∀ a∈K, ∀ b∉K, G.Adj a b → b∈p.support)
    {r : K} (C : (G.induce (K:Set V)).Walk r r) (hc : C.IsHamiltonianCycle)
    {t : ℕ} (pos : 0<t) (sizeK : t≤K.card)
    (connected : ∀ cut : Finset V, cut.card<t → (G.induce {u : V | u∉cut}).Connected) :
    3*K.card+1+(t-1)*((K.card+1)/2+2) ≤ Fintype.card V := by
  classical
  let E := Embedding.induce (G:=G) (K:Set V)
  have long := longest (C.dropLast.map E.toHom) (hc.isCycle.isPath_dropLast.map E.injective)
  rw [Walk.length_map] at long
  have hlen := C.length_dropLast_add_one hc.isCycle.not_nil
  have rank : C.length=K.card := by simpa using hc.length_eq
  have pathSize : t ≤ p.support.toFinset.card := by
    rw [List.toFinset_card_of_nodup hp.support_nodup,Walk.length_support]
    omega
  have apart : Disjoint p.support.toFinset K := Finset.disjoint_left.mpr
    (fun _ h mem => outside _ mem (List.mem_toFinset.mp h))
  obtain ⟨M,sub,wide,f,edges⟩ := matching_at_component_boundary p.support.toFinset K apart
    (fun a ha b hb h => List.mem_toFinset.mpr (boundary a ha b hb h)) pathSize sizeK connected
  have ob := cycle_matching_order p hp longest K outside C hc M (Finset.card_pos.mp (by omega))
    (fun a ha => List.mem_toFinset.mp (sub ha)) f edges
  exact (Nat.add_le_add_left (Nat.mul_le_mul_right _ (show t-1≤M.card-1 by omega)) _).trans ob

#print axioms component_cycle_order
#print axioms half_cycle_arc
#print axioms cycle_matching_order
end Graph189ConeComponentOrder
