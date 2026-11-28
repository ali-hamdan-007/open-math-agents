import Graph189SixCycleExtra
import Graph189ExtraPort

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189FiveCycleContacts
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}

omit [DecidableRel G.Adj] in
/-- Three distinct matches to the vertices of any exterior five-cycle
force two five-vertex tails and two four-vertex intervals. -/
theorem triple {r : V} (p : G.Walk a b) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (C : G.Walk r r) (hc : C.IsCycle) (five : C.length=5) (off : ∀ v∈C.support,v∉p.support)
    (M : Finset (Fin p.support.length)) (sz : M.card=3) (f : M↪C.support.toFinset)
    (contact : ∀ i : M, G.Adj p.support[i.val.val] (f i).val) : 26≤Fintype.card V := by
  classical
  let W := C.support.toFinset
  obtain ⟨_,start,join⟩ := Graph189TwoExteriorLinks.cycle_routes C hc
  let A := M.orderEmbOfFin sz
  let mark (i : Fin 3) : M := ⟨A i,M.orderEmbOfFin_mem sz i⟩
  let v (i : Fin 3) := (f (mark i)).val
  have has (i : Fin 3) : v i∈W := (f (mark i)).property
  have away {u v : V} {q : G.Walk u v} (stays : ∀ x∈q.support,x∈W) : List.Disjoint q.support p.support :=
    List.disjoint_left.mpr fun x hx => off x (List.mem_toFinset.mp (stays x hx))
  have tail (i : Fin 3) : ∃ z, ExteriorRoute p (v i) z (4+1) := by
    obtain ⟨w,q,hq,len,inc⟩ := start (v i) (has i)
    exact ⟨w,q,hq,away inc,by omega⟩
  have mid (i : Fin 2) : ExteriorRoute p (v i.castSucc) (v i.succ) 4 := by
    have ne : v i.castSucc≠v i.succ := by
      intro eq
      exact i.castSucc_lt_succ.ne (A.injective (congrArg Subtype.val (f.injective (Subtype.ext eq))))
    obtain ⟨q,hq,len,inc⟩ := join _ (has _) _ (has _) ne
    exact ⟨q,hq,away inc,by omega⟩
  obtain ⟨w,q,hq,dis,len⟩ := tail 0
  have pre : ∃ z, ExteriorRoute p z (v 0) (4+1) :=
    ⟨w,q.reverse,hq.reverse,by simpa [Walk.support_reverse] using dis,by simpa using len⟩
  have upper := exterior_order_with_tails p hp mx W (fun z hz => off z (List.mem_toFinset.mp hz))
    (j:=2) (N:=4) (A:=1) A v (fun i => contact (mark i)) mid pre (tail _)
  have size : W.card=5 := (Graph189SixCycleExtra.cycle_card C hc).trans five
  omega

omit [Fintype V] [DecidableEq V] in
/-- If a rich set of at least three rows each has at least two entries,
a matching cap of two gives two common columns on all rich rows and
covers every remaining row as well. -/
theorem pair (p : G.Walk a b) (W D : Finset V) (sub : D⊆W) (many : 3≤D.card)
    (rows : ∀ v∈D, 2≤((univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] v)).card)
    (bound : ∀ M : Finset (Fin p.support.length), M.card=3 → ∀ f : M↪W,
      (∀ i : M, G.Adj p.support[i.val.val] (f i).val) → False) :
    ∃ M : Finset (Fin p.support.length), M.card=2 ∧
      (∀ v∈D, ∀ i : Fin p.support.length, G.Adj p.support[i.val] v ↔ i∈M) ∧
      ∀ v∈W, ∀ i : Fin p.support.length, G.Adj p.support[i.val] v → i∈M := by
  classical
  let N (v : V) := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] v)
  let M := D.biUnion N
  have inc {v : V} (vd : v∈D) : N v⊆M := fun i hi => mem_biUnion.mpr ⟨v,vd,hi⟩
  have max : M.card≤2 := by
    by_contra! more
    obtain ⟨T,hT,f,edge⟩ := Graph189ExteriorAttachment.extra_port p D 2 (by omega) rows more
    let incl : D↪W := ⟨fun u => ⟨u.val,sub u.property⟩,fun _ _ e => Subtype.ext (congrArg (fun t : W => t.val) e)⟩
    exact bound T hT (f.trans incl) edge
  obtain ⟨u,hu,v,hv,uv⟩ := one_lt_card.mp (show 1<D.card by omega)
  have same (z : V) (zd : z∈D) : N z=M := eq_of_subset_of_card_le (inc zd) (max.trans (rows z zd))
  have two : M.card=2 := le_antisymm max ((rows u hu).trans (card_le_card (inc hu)))
  have covers (z : V) (zd : z∈D) (i : Fin p.support.length) : G.Adj p.support[i.val] z ↔ i∈M := by
    rw [←same z zd]
    simp [N]
  refine ⟨M,two,covers,?_⟩
  intro z zw i iz
  by_contra out
  have zd : z∉D := fun h => out ((covers z h i).mp iz)
  obtain ⟨j,jM,k,kM,jk⟩ := one_lt_card.mp (show 1<M.card by omega)
  have pair : M={j,k} := by
    symm
    apply eq_of_subset_of_card_le (by simpa [insert_subset_iff] using And.intro jM kM)
    rw [two,card_pair jk]
  let T := insert i M
  have count : T.card=3 := by rw [show T=insert i M by rfl,card_insert_of_notMem out,two]
  let port (h : T) : W := if h.val=i then ⟨z,zw⟩ else if h.val=j then ⟨u,sub hu⟩ else ⟨v,sub hv⟩
  have casesT (h : T) : h.val=i ∨ h.val=j ∨ h.val=k := by
    have mem := h.property
    change h.val∈insert i M at mem
    simpa only [pair,mem_insert,mem_singleton] using mem
  have ij : i≠j := fun e => out (e ▸ jM)
  have ik : i≠k := fun e => out (e ▸ kM)
  have zu : z≠u := fun e => zd (e ▸ hu)
  have zv : z≠v := fun e => zd (e ▸ hv)
  have inject : Function.Injective port := by
    intro h g eq
    apply Subtype.ext
    have values := congrArg Subtype.val eq
    rcases casesT h with hi|hi|hi <;> rcases casesT g with gi|gi|gi <;>
      simp only [port,hi,gi,if_neg ij.symm,if_neg ik.symm,if_neg jk.symm,Subtype.coe_mk] at values ⊢ <;>
      first | rfl | exact (zu values).elim | exact (zu.symm values).elim | exact (zv values).elim |
        exact (zv.symm values).elim | exact (uv values).elim | exact (uv.symm values).elim
  apply bound T count ⟨port,inject⟩
  intro h
  rcases casesT h with hi|hj|hk
  · simpa [port,hi] using iz
  · simpa [port,hj,ij.symm] using (covers u hu j).mpr jM
  · simpa [port,hk,ik.symm,jk.symm] using (covers v hv k).mpr kM

#print axioms triple
#print axioms pair
end Graph189FiveCycleContacts
