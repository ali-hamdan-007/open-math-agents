import Graph189ProtectedUniform
import Graph189ProtectedExchange
import Graph189GapLocation
import Graph189GapExchange

open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A Hamilton path after deleting z gives a Hamilton path in the original
qualifying graph whenever z has degree at least three and 3 deg(z)<k. -/
theorem traceable_of_low_deletion (hc : G.Connected) (z : V)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    {c d : {v : V | v ≠ z}} (P : (G.induce {v : V | v ≠ z}).Walk c d) (hp : P.IsHamiltonian)
    (pos : 3 ≤ G.degree z) (ratio : 3*G.degree z < G.secondSmallestDegree) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  by_contra nontrace
  obtain ⟨a,b,p,path,t,eq,longest⟩ := exists_longest_through G z
  let k := G.secondSmallestDegree
  let s := G.degree z
  let E := (p.support.toFinsetᶜ : Finset V)
  let m := E.card
  change 3 ≤ s at pos
  change 3*s < k at ratio
  obtain ⟨count,enough,_,_⟩ := protected_saturation_data hc z cap nontrace P hp p path t eq longest pos ratio
  change m=k+1-s at count
  change s<m at enough
  have sum : m+s=k+1 := by rw [count,Nat.sub_add_cancel (show s ≤ k+1 by omega)]
  obtain ⟨M,sz,contacts,clique⟩ := protected_uniform_clique hc z cap nontrace P hp p path t eq longest pos ratio
  change M.card=s at sz
  have mx : ∀ {i j}, ∀ r : G.Walk i j, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length :=
    fun r hr h => longest r hr (eq ▸ h)
  have uniform {i j} (r : G.Walk i j) (hr : r.IsPath) (retained : p.support[t.val] ∈ r.support)
      (same : r.length=p.length) (v : V) (hv : v∈r.support) (u : V) (hu : u∉r.support)
      (w : V) (hw : w∉r.support) (vu : G.Adj v u) : G.Adj v w := by
    obtain ⟨l,hl,el⟩ := List.mem_iff_getElem.mp (show z∈r.support from eq ▸ retained)
    obtain ⟨N,_,common,_⟩ := protected_uniform_clique hc z cap nontrace P hp r hr ⟨l,hl⟩ el
      (fun q hq h => by rw [same]; exact longest q hq h) pos ratio
    obtain ⟨j,hj,ej⟩ := List.mem_iff_getElem.mp hv
    let mark : Fin r.support.length := ⟨j,hj⟩
    have hu' : u ∈ (r.support.toFinsetᶜ : Finset V) := by simpa using hu
    have hw' : w ∈ (r.support.toFinsetᶜ : Finset V) := by simpa using hw
    rw [←ej] at vu ⊢
    exact (common w hw' mark).mpr ((common u hu' mark).mp vu)
  obtain ⟨x,hx,y,hy,ne⟩ := one_lt_card.mp (show 1 < E.card by change 1<m; omega)
  let X : E := ⟨x,hx⟩
  let Y : E := ⟨y,hy⟩
  have out {v : V} (h : v∈E) : v∉p.support := by simpa [E] using h
  have low : G.degree p.support[t.val] < k := by rw [eq]; change s<k; omega
  obtain ⟨w,hw⟩ := protected_exterior_hamilton_connected p path t mx low cap
    (by change m+2 ≤ k; omega) X Y (fun h => ne (congrArg Subtype.val h))
  let inc := (Embedding.induce (G:=G) (E : Set V)).toHom
  let q := w.map inc
  have hq : q.IsPath := hw.isPath.map Subtype.val_injective
  have dis : List.Disjoint q.support p.support := by
    apply List.disjoint_left.mpr
    intro v hv
    rw [show q.support=w.support.map inc from Walk.support_map _ _] at hv
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hv
    exact out u.property
  have qlen : q.support.length=m := by
    change (w.map inc).support.length=E.card
    rw [Walk.support_map,List.length_map,hw.length_support]
    change Fintype.card E=E.card
    exact Fintype.card_coe E
  have touch (i : Fin p.support.length) (hi : i∈M) : G.Adj p.support[i.val] x ∧ G.Adj p.support[i.val] y :=
    ⟨(contacts x hx i).mpr hi,(contacts y hy i).mpr hi⟩
  obtain ⟨j,hj⟩ : ∃ j, M.card=j+1 := ⟨s-1,by omega⟩
  let A := M.orderEmbOfFin hj
  have adj (i : Fin (j+1)) := touch (A i) (M.orderEmbOfFin_mem hj i)
  have bound := Graph189LayerCutoff.order_of_small_degree G hc z k cap (by change 2*s ≤ k+1; omega)
  change Fintype.card V ≤ 1+s+k+s*(k+1-s) at bound
  rw [←count] at bound
  have total := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup path.support_nodup] at total
  change p.support.length+m=Fintype.card V at total
  have close : p.support.length ≤ (j+1)*m+2*(j+1) := by
    rw [←hj,sz]
    have plus : m+s=k+1 := by omega
    omega
  obtain ⟨lo,hi,nonempty,le,size,safe,left,right,one,unmarked⟩ :=
    locate_tight_protected_gap t M hj (by omega : 0<m)
      (protected_contact_internal p path t mx (out hx) _ (adj 0).1).1
      (protected_contact_internal p path t mx (out hx) _ (adj (Fin.last j)).1).2
      (fun i => protected_contact_spacing p path t mx (out hx) _ _ (A.strictMono i.castSucc_lt_succ)
        (adj i.castSucc).1 (adj i.succ).1)
      (fun h => qlen ▸ protected_prefix_of_detour p path t mx _ h q hq dis (adj 0).2.symm)
      (fun h => qlen ▸ protected_suffix_of_detour p path t mx _ h q hq dis (adj _).1)
      (fun i h => qlen ▸ protected_interval_of_detour p path t mx _ _ (A.strictMono i.castSucc_lt_succ)
        h q hq dis (adj i.castSucc).1 (adj i.succ).2.symm) close
  have via := interval_exchange_witnesses p path t M q hq dis touch uniform nonempty le
    (size.trans qlen.symm) safe left right one
  apply Graph189ProtectedExchange.contradiction_of_uniform_marks (lo:=lo) (hi:=hi) (k:=k) p path t mx (out hx) (out hy)
    (clique hx hy ne) M (contacts _ hx) (contacts _ hy) le _ _
    (by rw [size,sz]; exact sum) (by rwa [sz]) (cap x)
  · intro i lo' hi' mem
    exact (unmarked i mem).elim (Nat.not_lt.mpr lo') (Nat.not_le.mpr hi')
  · intro i lo' hi'
    obtain ⟨c,xc,ic⟩ := via i.val (mem_Ico.mpr ⟨lo',hi'⟩)
    exact ⟨c,xc,(get_at p i.isLt).symm ▸ ic⟩

#print axioms traceable_of_low_deletion
end Graph189ExteriorGap
