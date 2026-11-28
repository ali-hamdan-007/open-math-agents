import Graph189FiveLowMarks
import Graph189GapExchange
import Graph189FourTerminalGap

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189FiveLowExchange
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}

/-- A longest path through z cannot omit four vertices at this order:
at least two gaps between the two marks are tight, and one avoids z. -/
theorem no_four_through (p : G.Walk a b) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (z : V) (on : z∈p.support) (high : ∀ w, w≠z → 5 ≤ G.degree w)
    (retain : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length=p.length →
      ∀ w, w≠z → w∉r.support → 3 ≤ (G.neighborFinset w \ r.support.toFinset).card)
    (quota : ∀ w, (univ.filter (fun t => G.dist w t=2)).card ≤ 5)
    (order : Fintype.card V ≤ 19) (size : (p.support.toFinsetᶜ : Finset V).card=4) : False := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  change E.card=4 at size
  obtain ⟨routes,M,card,links⟩ := Graph189FiveLowMarks.data p hp longest z high (retain p hp rfl) order size
  have contacts (v : V) (hv : v∈E) := links v hv (fun e => (mem_compl.mp hv) (List.mem_toFinset.mpr (e ▸ on)))
  obtain ⟨u,v,une,pair⟩ := card_eq_two.mp card
  obtain ⟨i,j,ij,pair⟩ : ∃ i j : Fin p.support.length, i<j ∧ M={i,j} := by
    rcases lt_or_gt_of_ne une with h|h
    · exact ⟨u,v,h,pair⟩
    · exact ⟨v,u,h,by simpa [Finset.pair_comm] using pair⟩
  have first : i∈M := by simp [pair]
  have last : j∈M := by simp [pair]
  obtain ⟨x,hx,y,hy,ne⟩ := one_lt_card.mp (show 1 < E.card by omega)
  let X : E := ⟨x,hx⟩
  let Y : E := ⟨y,hy⟩
  have out {w : V} (hw : w∈E) : w∉p.support := by simpa [E] using hw
  obtain ⟨w,hw⟩ := routes X Y (fun h => ne (congrArg Subtype.val h))
  let inc := (Embedding.induce (G:=G) (E : Set V)).toHom
  let q := w.map inc
  have hq : q.IsPath := hw.isPath.map Subtype.val_injective
  have dis : List.Disjoint q.support p.support := by
    apply List.disjoint_left.mpr
    intro z hz
    rw [show q.support=w.support.map inc from Walk.support_map _ _] at hz
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hz
    exact out c.property
  have qlen : q.support.length=4 := by
    change (w.map inc).support.length=4
    rw [Walk.support_map,List.length_map,hw.length_support]
    change Fintype.card E=4
    rwa [Fintype.card_coe]
  have touch (t : Fin p.support.length) (ht : t∈M) : G.Adj p.support[t.val] x ∧ G.Adj p.support[t.val] y :=
    ⟨(contacts x hx t).mpr ht,(contacts y hy t).mpr ht⟩
  have front := prefix_of_detour p hp longest i q hq dis (touch i first).2.symm
  have middle := interval_of_detour p hp longest i j ij q hq dis (touch i first).1 (touch j last).2.symm
  have back := suffix_of_detour p hp longest j q hq dis (touch j last).1
  rw [qlen] at front middle back
  have total := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at total
  change p.support.length+E.card=Fintype.card V at total
  obtain ⟨n,nr,ev⟩ := List.mem_iff_getElem.mp on
  let t : Fin p.support.length := ⟨n,nr⟩
  have tight : (i.val=4 ∧ i.val≤n) ∨
      (p.support.length-(j.val+1)=4 ∧ n≤j.val) ∨
      (j.val-(i.val+1)=4 ∧ (n < i.val+1 ∨ j.val≤n)) := by omega
  have marks (t : Fin p.support.length) : G.Adj p.support[t.val] x ↔ t.val=i.val ∨ t.val=j.val := by
    rw [contacts x hx t,pair]
    simp only [mem_insert,mem_singleton,Fin.ext_iff]
  have naturalMarks : contactPositions p x = {i.val,j.val} := by
    ext l
    constructor
    · intro h
      obtain ⟨hl,edge⟩ := (mem_contactPositions p x l).mp h
      have value := (marks ⟨l,hl⟩).mp (by simpa only [get_at] using edge)
      simpa only [mem_insert,mem_singleton] using value
    · intro h
      rcases mem_insert.mp h with rfl|other
      · exact (mem_contactPositions p x i.val).mpr ⟨i.isLt,by simpa only [get_at] using (touch i first).1⟩
      obtain rfl := mem_singleton.mp other
      exact (mem_contactPositions p x j.val).mpr ⟨j.isLt,by simpa only [get_at] using (touch j last).1⟩
  have uniform {c d} (r : G.Walk c d) (hr : r.IsPath) (keep : p.support[t.val] ∈ r.support)
      (same : r.length=p.length) (w : V) (hw : w∈r.support) (u : V) (hu : u∉r.support)
      (v : V) (hv : v∉r.support) (edge : G.Adj w u) : G.Adj w v := by
    have count := card_add_card_compl r.support.toFinset
    rw [List.toFinset_card_of_nodup hr.support_nodup] at count
    have len : r.support.length=p.support.length := by rw [r.length_support,same,←p.length_support]
    have retained : z∈r.support := by simpa only [t,ev] using keep
    obtain ⟨_,N,_,common⟩ := Graph189FiveLowMarks.data r hr (fun q h => by rw [same]; exact longest q h)
      z high (retain r hr same) order (by omega)
    obtain ⟨l,hl,value⟩ := List.mem_iff_getElem.mp hw
    let pos : Fin r.support.length := ⟨l,hl⟩
    rw [←value] at edge ⊢
    exact (common v (by simpa using hv) (fun e => hv (e ▸ retained)) pos).mpr
      ((common u (by simpa using hu) (fun e => hu (e ▸ retained)) pos).mp edge)
  rcases tight with ⟨tightLeft,safe⟩|⟨tightRight,safe⟩|⟨tightMiddle,safe⟩
  · have via := interval_exchange_witnesses p hp t M q hq dis touch uniform
      (lo:=0) (hi:=i.val) (by omega) i.isLt.le (by omega) (Or.inr safe) (Or.inl rfl)
      (Or.inr ⟨i,first,rfl⟩) (Or.inr i.isLt)
    apply Graph189FourTerminalGap.impossible_of_exact_length p hp (out hx)
      (by omega) (by omega) (by omega) naturalMarks i.isLt.le (by omega : 0+4=i.val) _ via (quota x)
    intro l hl
    have := mem_Ico.mp hl
    omega
  · have via := interval_exchange_witnesses p hp t M q hq dis touch uniform
      (lo:=j.val+1) (hi:=p.support.length) (by omega) le_rfl (by omega) (Or.inl (by change n<j.val+1; omega))
      (Or.inr ⟨j,last,rfl⟩) (Or.inl rfl) (Or.inl (by omega))
    apply Graph189FourTerminalGap.impossible_of_exact_length p hp (out hx)
      (by omega) (by omega) (by omega) naturalMarks le_rfl (by omega : j.val+1+4=p.support.length) _ via (quota x)
    intro l hl
    have := mem_Ico.mp hl
    omega
  · have via := interval_exchange_witnesses p hp t M q hq dis touch uniform
      (lo:=i.val+1) (hi:=j.val) (by omega) j.isLt.le (by omega) safe
      (Or.inr ⟨i,first,rfl⟩) (Or.inr ⟨j,last,rfl⟩) (Or.inl (by omega))
    apply Graph189FourTerminalGap.impossible_of_exact_length p hp (out hx)
      (by omega) (by omega) (by omega) naturalMarks j.isLt.le (by omega : i.val+1+4=j.val) _ via (quota x)
    intro l hl
    have := mem_Ico.mp hl
    omega

#print axioms no_four_through
end Graph189FiveLowExchange
