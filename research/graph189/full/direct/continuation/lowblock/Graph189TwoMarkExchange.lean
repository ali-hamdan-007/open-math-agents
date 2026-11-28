import Graph189FourTerminalGap
import Graph189GapLocation
import Graph189GapExchange
import Graph189ProtectedExteriorDegree

open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b : V}

/-- If a protected longest path has two uniform marks, an exterior spanning
path exchanges with a tight gap and produces two further witnesses outside it. -/
theorem two_mark_exchange (p : G.Walk a b) (hp : p.IsPath) (t : Fin p.support.length)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → p.support[t.val]∈q.support → q.length≤p.length)
    (E : Finset V) (many : 1<E.card) (outside : ∀ {v}, v∈E → v∉p.support)
    (routes : ∀ x y : E, x≠y → ∃ q : (G.induce (E : Set V)).Walk x y, q.IsHamiltonian)
    (M : Finset (Fin p.support.length)) (sz : M.card=2)
    (links : ∀ w∈E, ∀ i : Fin p.support.length, G.Adj p.support[i.val] w ↔ i∈M)
    (common : ∀ {i j}, ∀ r : G.Walk i j, r.IsPath → p.support[t.val]∈r.support →
      r.length=p.length → ∀ v∈r.support, ∀ u∉r.support, ∀ w∉r.support, G.Adj v u → G.Adj v w)
    (room : p.support.length ≤ 2*E.card+4) (cap : ∀ x∈E, G.distEven x ≤ E.card+2) : False := by
  classical
  obtain ⟨x,hx⟩ := card_pos.mp (by omega : 0<E.card)
  let X : E := ⟨x,hx⟩
  obtain ⟨y,hy,ne⟩ := exists_mem_ne many x
  let Y : E := ⟨y,hy⟩
  obtain ⟨w,hw⟩ := routes X Y (fun e => ne (congrArg Subtype.val e).symm)
  let inc := (Embedding.induce (G:=G) (E : Set V)).toHom
  let q := w.map inc
  have hq : q.IsPath := hw.isPath.map Subtype.val_injective
  have dis : List.Disjoint q.support p.support := by
    apply List.disjoint_left.mpr
    intro v hv
    rw [show q.support=w.support.map inc from Walk.support_map _ _] at hv
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hv
    exact outside u.property
  have qlen : q.support.length=E.card := by
    change (w.map inc).support.length=E.card
    rw [Walk.support_map,List.length_map,hw.length_support]
    exact Fintype.card_coe E
  have touch (i : Fin p.support.length) (hi : i∈M) :
      G.Adj p.support[i.val] x ∧ G.Adj p.support[i.val] y := ⟨(links x hx i).mpr hi,(links y hy i).mpr hi⟩
  let A := M.orderEmbOfFin (show M.card=1+1 from sz)
  have mem (i : Fin 2) : A i∈M := M.orderEmbOfFin_mem sz i
  have adj (i : Fin 2) := touch (A i) (mem i)
  have first := (protected_contact_internal p hp t mx (outside hx) _ (adj 0).1).1
  have last := (protected_contact_internal p hp t mx (outside hx) _ (adj (Fin.last 1)).1).2
  have space (i : Fin 1) := protected_contact_spacing p hp t mx (outside hx) _ _ (A.strictMono i.castSucc_lt_succ)
    (adj i.castSucc).1 (adj i.succ).1
  obtain ⟨lo,hi,nonempty,bound,len,safe,lb,ub,one,unmarked⟩ := locate_tight_protected_gap t M
    (j:=1) (m:=E.card) sz (by omega) first last space
    (fun h => by have ql := protected_prefix_of_detour p hp t mx _ h q hq dis (adj 0).2.symm; simpa only [qlen] using ql)
    (fun h => by have ql := protected_suffix_of_detour p hp t mx _ h q hq dis (adj _).1; simpa only [qlen] using ql)
    (fun i h => by have ql := protected_interval_of_detour p hp t mx _ _ (A.strictMono i.castSucc_lt_succ) h
                    q hq dis (adj i.castSucc).1 (adj i.succ).2.symm; simpa only [qlen] using ql)
    room
  have witnesses := interval_exchange_witnesses p hp t M q hq dis touch common nonempty bound
    (len.trans qlen.symm) safe lb ub one
  let I := A 0
  let J := A (Fin.last 1)
  have spaced : I.val+2 ≤ J.val := space 0
  have neq : I≠J := fun e => by rw [e] at spaced; omega
  have pair : M={I,J} := by
    symm
    apply eq_of_subset_of_card_le (by
      intro v hv
      rcases mem_insert.mp hv with rfl|h
      · exact mem 0
      obtain rfl := mem_singleton.mp h
      exact mem (Fin.last 1))
    rw [card_pair neq,sz]
  have mark : contactPositions p x = {I.val,J.val} := by
    ext l
    constructor
    · intro h
      obtain ⟨hl,edge⟩ := (mem_contactPositions p x l).mp h
      have inM := (links x hx ⟨l,hl⟩).mp (by simpa [get_at] using edge)
      rw [pair] at inM
      simpa only [mem_insert,mem_singleton,Fin.ext_iff] using inM
    · intro h
      rcases mem_insert.mp h with rfl|other
      · exact (mem_contactPositions p x I.val).mpr ⟨I.isLt,by simpa [get_at] using (adj 0).1⟩
      have e := mem_singleton.mp other
      subst l
      exact (mem_contactPositions p x J.val).mpr ⟨J.isLt,by rw [←get_at p J.isLt]; exact (adj (Fin.last 1)).1⟩
  have range : lo+E.card=hi := by rw [←len,Nat.add_sub_of_le nonempty.le]
  refine Graph189FourTerminalGap.impossible_of_length p hp (outside hx) (i:=I.val) (j:=J.val) (lo:=lo) (hi:=hi) first spaced last mark bound range ?_ witnesses ?_
  · intro l hl
    have h := mem_Ico.mp hl
    have old := unmarked I (mem 0)
    have next := unmarked J (mem (Fin.last 1))
    omega
  · exact cap x hx

#print axioms two_mark_exchange
end Graph189ExteriorGap
