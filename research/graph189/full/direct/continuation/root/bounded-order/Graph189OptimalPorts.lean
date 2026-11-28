import Graph189OptimalHighCore
import Graph189HallDeficiency
import Graph189ExteriorMatching

open SimpleGraph Finset Graph189ExteriorGap
namespace Graph189OptimalExterior
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- All omitted vertices can be counted even when only a subset supplies the
matched gap routes. A separate tail bonus can be used at both ends. -/
theorem core_ports {a b : V} {p : G.Walk a b} {C : Finset V} {k : ℕ} (h : Chosen p C k)
    (H : Finset V) (sub : H⊆C) {s extra : ℕ} (pos : 0<s) (size : s≤H.card)
    (rows : ∀v∈H,s≤(contactPositions p v).card)
    (routes : ∀u v : H,u≠v → ∃q : (G.induce (H:Set V)).Walk u v,q.IsHamiltonian)
    (tails : ∀v∈H,∃w,ExteriorRoute p w v (H.card+extra)) :
    C.card+s+(s+1)*H.card+2*extra≤Fintype.card V := by
  classical
  obtain ⟨U,inH,num⟩ := Finset.exists_subset_card_eq size
  obtain ⟨f,row⟩ := hall_on_dense_vertices (contactPositions p) s U num (fun v hv => rows v (inH hv))
  let index : U ↪ Fin p.support.length :=
    ⟨fun v => ⟨f v,((mem_contactPositions p v.val _).mp (row v)).1⟩,
      fun u v e => f.injective (congrArg Fin.val e)⟩
  let M := (univ:Finset U).map index
  have order : M.card=s := by simp [M,num]
  let j := s-1
  have count : M.card=j+1 := by dsimp [j]; omega
  let iso := M.orderIsoOfFin count
  let mark := M.orderEmbOfFin count
  have chosen (i : Fin (j+1)) : ∃v : U,index v=mark i := by
    obtain ⟨v,_,e⟩ := mem_map.mp (iso i).property
    exact ⟨v,e⟩
  let port (i : Fin (j+1)) : H := ⟨(chosen i).choose.val,inH (chosen i).choose.property⟩
  have edge (i : Fin (j+1)) : G.Adj p.support[(mark i).val] (port i).val := by
    rw [get_at]
    have m := (mem_contactPositions p _ _).mp (row (chosen i).choose)
    have eq := congrArg Fin.val (chosen i).choose_spec
    change f (chosen i).choose=(mark i).val at eq
    exact eq ▸ m.2
  have inj : Function.Injective port := by
    intro i l e
    have picks : (chosen i).choose=(chosen l).choose := Subtype.ext (congrArg (fun u:H => u.val) e)
    exact mark.injective ((chosen i).choose_spec.symm.trans ((congrArg index picks).trans (chosen l).choose_spec))
  have inner (i : Fin j) : ExteriorRoute p (port i.castSucc).val (port i.succ).val H.card := by
    obtain ⟨q,hq⟩ := routes _ _ (inj.ne (ne_of_lt i.castSucc_lt_succ))
    exact route_of_induced_hamilton p H (fun v hv => h.outside v (sub hv)) hq
  obtain ⟨w,r⟩ := tails (port (Fin.last j)).val (port (Fin.last j)).property
  obtain ⟨q,hq,off,len⟩ := r
  have after : ExteriorRoute p (port (Fin.last j)).val w (H.card+extra) :=
    ⟨q.reverse,hq.reverse,by simpa using off,by simpa using len⟩
  have bound := exterior_order_with_tails p h.path h.longest C h.outside mark (fun i => (port i).val)
    edge inner (tails (port 0).val (port 0).property) ⟨w,after⟩
  rwa [show j+1=s by omega,show j+2=s+1 by omega] at bound

end Graph189OptimalExterior
#print axioms Graph189OptimalExterior.core_ports
