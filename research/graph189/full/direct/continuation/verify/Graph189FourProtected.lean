import Graph189ProtectedUniform
import Graph189GapLocation
import Graph189GapExchange
import Graph189FourTerminalGap
import Graph189QuadraticOrder

open SimpleGraph Finset Graph189ExteriorGap
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189FourProtected
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V}
variable [DecidableRel G.Adj] {a b : V}

private theorem uniform (Q : G.Walk a b) (hQ : Q.IsPath) (t : Fin Q.support.length)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → Q.support[t.val] ∈ r.support → r.length ≤ Q.length)
    (low : G.degree Q.support[t.val] < G.secondSmallestDegree) (k4 : G.secondSmallestDegree=4)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) (order : Fintype.card V ≤ 14)
    (size : (Q.support.toFinsetᶜ : Finset V).card=3) :
    let E := (Q.support.toFinsetᶜ : Finset V)
    (∀ x y : E, x≠y → ∃ q : (G.induce (E : Set V)).Walk x y, q.IsHamiltonian) ∧
      ∃ M : Finset (Fin Q.support.length), M.card=2 ∧
        ∀ w∈E, ∀ i : Fin Q.support.length, G.Adj Q.support[i.val] w ↔ i∈M := by
  classical
  let E := (Q.support.toFinsetᶜ : Finset V)
  let H := G.induce (E : Set V)
  change E.card=3 at size
  have out (w : V) (hw : w∈E) : w∉Q.support := by simpa [E] using hw
  have deg (w : E) : 2 ≤ H.degree w := by
    have h := protected_exterior_minimum Q hQ t maximal low cap w
    rw [k4] at h
    exact h
  have routes (x y : E) (ne : x≠y) : ∃ q : H.Walk x y, q.IsHamiltonian := by
    apply Graph189TerminalLeafClosure.prescribed_of_supergraph (G:=H) le_top _
      (Graph189TerminalLeafClosure.complete_prescribed x y ne)
    intro u v _ _
    change Fintype.card E+1 ≤ H.degree u+H.degree v
    rw [Fintype.card_coe,size]
    have := deg u
    have := deg v
    omega
  refine ⟨routes,uniform_contacts_of_order Q hQ t maximal E out (by omega) routes 2 (by omega)
    (by rw [size]; omega) ?_⟩
  intro w hw
  have ne : w ≠ Q.support[t.val] := fun e => out w hw (e ▸ List.getElem_mem _)
  have high := (degree_pair (G:=G) w _ ne).resolve_right (Nat.not_le.mpr low)
  have d := Graph189DenseExteriorOrder.neighbors_on_path Q E
    (fun _ _ x _ nx => by simpa [E] using nx) hw
  rw [size] at d
  omega

/-- A Hamiltonian deletion at the unique vertex of degree two suffices at
second-smallest degree four. -/
theorem traceable_of_two_deletion (hc : G.Connected) (z : V) (zdeg : G.degree z=2)
    (k4 : G.secondSmallestDegree=4) (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    {c d : {v : V | v≠z}} (P : (G.induce {v : V | v≠z}).Walk c d) (hP : P.IsHamiltonian) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  by_contra nontrace
  have order : Fintype.card V ≤ 13 := by
    have bound := Graph189QuadraticOrder.rooted hc z 4 (fun v => by simpa [k4] using cap v)
    rw [zdeg] at bound
    omega
  obtain ⟨a,b,p,hp,t,eq,longest⟩ := exists_longest_through G z
  let E := (p.support.toFinsetᶜ : Finset V)
  have mx : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length :=
    fun r hr h => longest r hr (eq ▸ h)
  have low : G.degree p.support[t.val] < G.secondSmallestDegree := by rw [eq,zdeg,k4]; decide
  have gap := protected_size_of_traceable_deletion z (by omega) P hP p hp longest
  rw [zdeg] at gap
  change 1+2+(2+1)*E.card ≤ Fintype.card V at gap
  have omitted : E.Nonempty := by
    by_contra empty
    apply nontrace
    refine ⟨a,b,p,hp.isHamiltonian_of_mem (fun x => ?_)⟩
    by_contra no
    exact empty ⟨x,by simpa [E] using no⟩
  obtain ⟨x,hx⟩ := omitted
  let X : E := ⟨x,hx⟩
  have deg := protected_exterior_minimum p hp t mx low cap X
  rw [k4] at deg
  have ub := (G.induce (E : Set V)).degree_lt_card_verts X
  change (G.induce (E : Set V)).degree X < Fintype.card E at ub
  rw [Fintype.card_coe] at ub
  change 2 ≤ (G.induce (E : Set V)).degree X at deg
  have size : E.card=3 := by omega
  obtain ⟨routes,M,sz,links⟩ := uniform p hp t mx low k4 cap (by omega) size
  have total := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at total
  change p.support.length+E.card=Fintype.card V at total
  have common {i j} (r : G.Walk i j) (hr : r.IsPath) (retained : p.support[t.val]∈r.support)
      (same : r.length=p.length) (v : V) (hv : v∈r.support) (w : V) (hw : w∉r.support)
      (u : V) (hu : u∉r.support) (vw : G.Adj v w) : G.Adj v u := by
    have count := card_add_card_compl r.support.toFinset
    rw [List.toFinset_card_of_nodup hr.support_nodup] at count
    have len : r.support.length=p.support.length := by rw [r.length_support,same,←p.length_support]
    obtain ⟨i,hi,atZ⟩ := List.mem_iff_getElem.mp (show z∈r.support from eq ▸ retained)
    let T : Fin r.support.length := ⟨i,hi⟩
    have lo : G.degree r.support[T.val] < G.secondSmallestDegree := by change G.degree r.support[i] < _; rw [atZ,zdeg,k4]; decide
    have mx' : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → r.support[T.val]∈q.support → q.length ≤ r.length := by
      intro _ _ q hq ht
      rw [same]
      apply longest q hq
      simpa only [T,atZ] using ht
    obtain ⟨_,_,_,both⟩ := uniform r hr T mx' lo k4 cap (by omega) (by omega)
    obtain ⟨l,hl,ev⟩ := List.mem_iff_getElem.mp hv
    rw [←ev] at vw ⊢
    exact (both u (by simpa using hu) ⟨l,hl⟩).mpr ((both w (by simpa using hw) ⟨l,hl⟩).mp vw)
  obtain ⟨y,hy,ne⟩ := exists_mem_ne (show 1 < E.card by omega) x
  let Y : E := ⟨y,hy⟩
  obtain ⟨w,hw⟩ := routes X Y (fun e => ne (congrArg Subtype.val e).symm)
  let inc := (Embedding.induce (G:=G) (E : Set V)).toHom
  let q := w.map inc
  have hq : q.IsPath := hw.isPath.map Subtype.val_injective
  have outside {v : V} (h : v∈E) : v∉p.support := by simpa [E] using h
  have dis : List.Disjoint q.support p.support := by
    apply List.disjoint_left.mpr
    intro v hv
    rw [show q.support=w.support.map inc from Walk.support_map _ _] at hv
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hv
    exact outside u.property
  have qlen : q.support.length=3 := by
    change (w.map inc).support.length=3
    rw [Walk.support_map,List.length_map,hw.length_support]
    change Fintype.card E=3
    rwa [Fintype.card_coe]
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
    (j:=1) (m:=3) sz (by decide) first last space
    (fun h => by have ql := protected_prefix_of_detour p hp t mx _ h q hq dis (adj 0).2.symm; simpa only [qlen] using ql)
    (fun h => by have ql := protected_suffix_of_detour p hp t mx _ h q hq dis (adj _).1; simpa only [qlen] using ql)
    (fun i h => by have ql := protected_interval_of_detour p hp t mx _ _ (A.strictMono i.castSucc_lt_succ) h
                    q hq dis (adj i.castSucc).1 (adj i.succ).2.symm; simpa only [qlen] using ql)
    (by omega)
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
  have range : lo+3=hi := by rw [←len,Nat.add_sub_of_le nonempty.le]
  refine Graph189FourTerminalGap.impossible p hp (outside hx) (i:=I.val) (j:=J.val) (lo:=lo) (hi:=hi) first spaced last mark bound range ?_ witnesses ?_
  · intro l hl
    have h := mem_Ico.mp hl
    have old := unmarked I (mem 0)
    have next := unmarked J (mem (Fin.last 1))
    omega
  · simpa only [k4] using cap x

#print axioms traceable_of_two_deletion
end Graph189FourProtected
