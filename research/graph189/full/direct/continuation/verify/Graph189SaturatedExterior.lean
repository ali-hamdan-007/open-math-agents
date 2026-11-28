import Graph189AllHighExterior
import Graph189LowDeletionTraceable

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189SaturatedExterior
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem data {a b : V} (p : G.Walk a b) (hp : p.IsPath) (t : Fin p.support.length)
    (mx : ∀ {i j}, ∀ q : G.Walk i j, q.IsPath → p.support[t.val]∈q.support → q.length≤p.length)
    (high : ∀ {v : V}, v∉p.support → G.secondSmallestDegree≤G.degree v)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    (m s : ℕ) (size : (p.support.toFinsetᶜ : Finset V).card=m)
    (sum : m+s=G.secondSmallestDegree+1) (three : 3≤s) (less : s<m)
    (order : Fintype.card V<(s+2)*m+(s+1)) :
    let E := (p.support.toFinsetᶜ : Finset V)
    (∀ x y : E, x≠y → ∃ q : (G.induce (E : Set V)).Walk x y, q.IsHamiltonian) ∧
    ∃ M : Finset (Fin p.support.length), M.card=s ∧
      (∀ w∈E, ∀ i : Fin p.support.length, G.Adj p.support[i.val] w ↔ i∈M) ∧ G.IsClique (E : Set V) := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  let H := G.induce (E : Set V)
  change E.card=m at size
  have out (w : V) (hw : w∈E) : w∉p.support := by simpa [E] using hw
  have routes (x y : E) (ne : x≠y) : ∃ q : H.Walk x y, q.IsHamiltonian := by
    apply Graph189TerminalLeafClosure.prescribed_of_supergraph (G:=H) le_top _
      (Graph189TerminalLeafClosure.complete_prescribed x y ne)
    intro i j _ _
    have deg (w : E) : G.secondSmallestDegree/2≤H.degree w :=
      Graph189AllHighExterior.minimum p hp t mx (by omega) high cap w
    have := deg i
    have := deg j
    change Fintype.card E+1≤H.degree i+H.degree j
    rw [Fintype.card_coe,size]
    omega
  obtain ⟨M,sz,links⟩ := uniform_contacts_of_order p hp t mx E out (by omega) routes s
    (by omega) (by rwa [size]) (by
      intro w hw
      have reach := Graph189DenseExteriorOrder.neighbors_on_path p E
        (fun _ _ x _ nx => by simpa [E] using nx) hw
      have := high (out w hw)
      omega)
  exact ⟨routes,M,sz,links,exterior_clique_of_common_contacts p M G.secondSmallestDegree
    (by change E.card+M.card≤_; omega) (fun w hw => high (out w hw))
    (fun w hw i => (links w hw i).mp)⟩

/-- A longest path through a minimum-degree vertex cannot have a saturated
exterior in the order range where one protected gap can be exchanged. -/
theorem exclude {a b : V} (p : G.Walk a b) (path : p.IsPath) (t : Fin p.support.length)
    (mx : ∀ {i j}, ∀ q : G.Walk i j, q.IsPath → p.support[t.val]∈q.support → q.length≤p.length)
    (high : ∀ v, v≠p.support[t.val] → G.secondSmallestDegree≤G.degree v)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    (m s : ℕ) (size : (p.support.toFinsetᶜ : Finset V).card=m)
    (sum : m+s=G.secondSmallestDegree+1) (three : 3≤s) (less : s<m)
    (order : Fintype.card V<(s+2)*m+(s+1)) (room : p.support.length≤s*m+2*s) : False := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  let k := G.secondSmallestDegree
  change E.card=m at size
  have rootmem : p.support[t.val]∈p.support := List.getElem_mem _
  have outside : ∀ {w : V}, w∉p.support → G.secondSmallestDegree≤G.degree w :=
    fun {w} h => high w (fun eq => h (by simpa only [eq] using rootmem))
  obtain ⟨paths,M,sz,contacts,clique⟩ := data p path t mx outside cap m s size sum three less order
  have uniform {i j} (r : G.Walk i j) (hr : r.IsPath) (retain : p.support[t.val]∈r.support)
      (same : r.length=p.length) (w : V) (hw : w∈r.support) (u : V) (hu : u∉r.support)
      (v : V) (hv : v∉r.support) (wu : G.Adj w u) : G.Adj w v := by
    obtain ⟨l,hl,atZ⟩ := List.mem_iff_getElem.mp retain
    let T : Fin r.support.length := ⟨l,hl⟩
    have eq : r.support[T.val]=p.support[t.val] := atZ
    have mx' : ∀ {i j}, ∀ q : G.Walk i j, q.IsPath → r.support[T.val]∈q.support → q.length≤r.length :=
      fun q hq seen => by rw [same]; exact mx q hq (eq ▸ seen)
    have total := card_add_card_compl r.support.toFinset
    have orig := card_add_card_compl p.support.toFinset
    rw [List.toFinset_card_of_nodup hr.support_nodup,r.length_support,same,←p.length_support] at total
    rw [List.toFinset_card_of_nodup path.support_nodup] at orig
    change p.support.length+E.card=Fintype.card V at orig
    obtain ⟨_,_,_,links,_⟩ := data r hr T mx'
      (fun {v} h => high v (fun e => h (by simpa only [e] using retain))) cap m s (by omega) sum three less order
    obtain ⟨j,hj,atW⟩ := List.mem_iff_getElem.mp hw
    rw [←atW] at wu ⊢
    exact (links v (by simpa using hv) ⟨j,hj⟩).mpr ((links u (by simpa using hu) ⟨j,hj⟩).mp wu)
  obtain ⟨x,hx,y,hy,ne⟩ := one_lt_card.mp (show 1 < E.card by omega)
  let X : E := ⟨x,hx⟩
  let Y : E := ⟨y,hy⟩
  have out {v : V} (h : v∈E) : v∉p.support := by simpa [E] using h
  obtain ⟨w,hw⟩ := paths X Y (fun h => ne (congrArg Subtype.val h))
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
    change (w.map inc).support.length=m
    rw [Walk.support_map,List.length_map,hw.length_support]
    change Fintype.card E=m
    exact (Fintype.card_coe E).trans size
  have touch (i : Fin p.support.length) (hi : i∈M) : G.Adj p.support[i.val] x ∧ G.Adj p.support[i.val] y :=
    ⟨(contacts x hx i).mpr hi,(contacts y hy i).mpr hi⟩
  obtain ⟨j,hj⟩ : ∃ j, M.card=j+1 := ⟨s-1,by omega⟩
  let A := M.orderEmbOfFin hj
  have adj (i : Fin (j+1)) := touch (A i) (M.orderEmbOfFin_mem hj i)
  have close : p.support.length≤(j+1)*m+2*(j+1) := by rwa [←hj,sz]
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
    (by rw [size,sz]; exact sum) (by simpa only [sz] using three) (cap x)
  · intro i lo' hi' mem
    exact (unmarked i mem).elim (Nat.not_lt.mpr lo') (Nat.not_le.mpr hi')
  · intro i lo' hi'
    obtain ⟨c,xc,ic⟩ := via i.val (mem_Ico.mpr ⟨lo',hi'⟩)
    exact ⟨c,xc,(get_at p i.isLt).symm ▸ ic⟩

#print axioms exclude
end Graph189SaturatedExterior
