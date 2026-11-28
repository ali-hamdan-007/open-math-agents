import Graph189ShortLeafRoutes
import Graph189BoundaryMatching
import Graph189MinimumCut

open SimpleGraph Finset Graph189OptimalExterior Graph189ExteriorGap
namespace Graph189ExteriorLeaf
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Two actual path contacts suffice for the long-leaf-interior size case.
Both tails may extend past the matched core. -/
private theorem two_contacts {a b : V} {p : G.Walk a b} {C D : Finset V} {w : V} {k extra : ℕ}
    (h : Chosen p C k) (L : Limb G C D w) (conn : 3≤G.vertexConnectivity)
    (wide : 2≤D.card) (routes : ∀u v : D,u≠v → ∃q : (G.induce (D:Set V)).Walk u v,q.IsHamiltonian)
    (tails : ∀x∈D,∃y,ExteriorRoute p y x (D.card+extra)) :
    C.card+2+3*D.card+2*extra≤Fintype.card V := by
  classical
  have doff (v : V) (vd : v∈D) := h.outside v (L.sub vd)
  obtain ⟨v,vd,u,ud,vu⟩ := one_lt_card.mp (by omega : 1<D.card)
  obtain ⟨q,hq⟩ := routes ⟨v,vd⟩ ⟨u,ud⟩ (fun eq => vu (congrArg (fun i : D => i.val) eq))
  obtain ⟨s,hs,_,len⟩ := route_of_induced_hamilton p D doff hq
  have long := h.longest s hs
  have sl := s.length_support
  have pl := p.length_support
  have room : 2≤p.support.toFinset.card := by rw [List.toFinset_card_of_nodup h.path.support_nodup]; omega
  have bound (x : V) (xd : x∈D) (y : V) (yo : y∉D) (e : G.Adj x y) :
      y∈p.support.toFinset ∨ y∈({w}:Finset V) := by
    by_cases yp : y∈p.support
    · exact Or.inl (List.mem_toFinset.mpr yp)
    have yc := h.closed x (L.sub xd) y e yp
    exact Or.inr (mem_singleton.mpr ((L.exits x xd y yc e).resolve_left yo))
  obtain ⟨M,on,many,f,edges⟩ := matching_at_buffered_boundary (G:=G) p.support.toFinset D {w}
    (Finset.disjoint_left.mpr (fun _ yp yd => doff _ yd (List.mem_toFinset.mp yp)))
    (by simpa using h.outside w L.gate) (by simpa using L.fresh) bound room wide
    (fun cut lt => Graph189CutSides.connected_after_smaller_deletion cut (by simp at lt; omega))
  obtain ⟨S,sub,size⟩ := Finset.exists_subset_card_eq many
  obtain ⟨marks,iso,values⟩ := vertex_positions_equiv p S (fun v vs => List.mem_toFinset.mp (on (sub vs)))
  have two : marks.card=1+1 := by
    have e := Fintype.card_congr iso
    simpa only [Fintype.card_coe,size] using e
  let index := marks.orderIsoOfFin two
  let mark := marks.orderEmbOfFin two
  let landing (i : Fin 2) : M := ⟨(iso (index i)).val,sub (iso (index i)).property⟩
  let port (i : Fin 2) := f (landing i)
  have touch (i : Fin 2) : G.Adj p.support[(mark i).val] (port i).val := by
    rw [show p.support[(mark i).val]=(iso (index i)).val from values (index i)]
    exact edges (landing i)
  have inj : Function.Injective port := by
    intro i j eq
    apply index.injective
    apply iso.injective
    exact Subtype.ext (congrArg (fun v:M => v.val) (f.injective eq))
  have gap (i : Fin 1) : ExteriorRoute p (port i.castSucc).val (port i.succ).val D.card := by
    obtain ⟨z,hz⟩ := routes _ _ (inj.ne (ne_of_lt i.castSucc_lt_succ))
    exact route_of_induced_hamilton p D doff hz
  obtain ⟨v,r,hr,off,rl⟩ := tails (port (Fin.last 1)).val (port (Fin.last 1)).property
  have after : ExteriorRoute p (port (Fin.last 1)).val v (D.card+extra) :=
    ⟨r.reverse,hr.reverse,by simpa using off,by simpa using rl⟩
  exact exterior_order_with_tails p h.path h.longest C h.outside mark (fun i => (port i).val)
    touch gap (tails (port 0).val (port 0).property) ⟨v,after⟩

private theorem product_bound {k d : ℕ} (lo : 7≤k) (hi : k≤21)
    (half : k≤2*d) (small : d+2<k) :
    5*k-5<d+1+(k+1)/2+(k-d)+(k-d+1)*d+2*(1+(k+1)/2) := by
  have table : (List.range 15).all (fun t => let k := 7+t
    (List.range k).all (fun d => decide (k≤2*d → d+2<k →
      5*k-5<d+1+(k+1)/2+(k-d)+(k-d+1)*d+2*(1+(k+1)/2))))=true := by decide
  have row := List.all_eq_true.mp table (k-7) (List.mem_range.mpr (by omega))
  rw [show 7+(k-7)=k by omega] at row
  exact of_decide_eq_true (List.all_eq_true.mp row d (List.mem_range.mpr (by omega))) half small

/-- The short endblock alternative in the paper is impossible throughout the
entire remaining degree and order window. -/
theorem no_short_leaf {a b : V} {p : G.Walk a b} {C D : Finset V} {w : V} {k : ℕ}
    (h : Chosen p C k) (L : Limb G C D w) (conn : 3≤G.vertexConnectivity)
    (noncut : ∀x∈D,(G.induce ((insert w D).erase x:Set V)).Preconnected)
    (high : ∀x∈D,k≤G.degree x) (dense : ∀x∈D,D.card+3≤2*(G.neighborFinset x∩C).card)
    (lo : 7≤k) (hi : k≤21) (order : Fintype.card V≤5*k-5)
    (quota : ∀v,(univ.filter (fun z => G.dist v z=2)).card≤k)
    (minimum : ∀v,3≤G.degree v) (uniqueLow : ∀u v,G.degree u<k → G.degree v<k → u=v) : False := by
  classical
  let hhalf := (k+1)/2
  have capD (x : V) (xd : x∈D) : (G.neighborFinset x∩C).card≤D.card := by
    have sub : G.neighborFinset x∩C⊆(insert w D).erase x := by
      intro y hy
      obtain ⟨adj,yc⟩ := mem_inter.mp hy
      have e := (G.mem_neighborFinset _ _).mp adj
      exact mem_erase.mpr ⟨e.ne.symm,mem_insert.mpr (L.exits _ xd _ yc e).symm⟩
    have h := card_le_card sub
    have m := card_erase_add_one (show x∈insert w D from mem_insert_of_mem xd)
    rw [card_insert_of_notMem L.fresh] at m
    omega
  obtain ⟨x,xd⟩ := L.nonempty
  have half := internal_half h (L.sub xd) (high _ xd) (quota _) minimum uniqueLow
  have hx := high _ xd
  have bound := capD _ xd
  have size : k≤2*D.card := by omega
  have routes := short_routes L dense
  have tails := extended_tails h L noncut (by omega) routes (by omega) quota minimum uniqueLow
  have R := (remainder_route h L (by omega) quota minimum uniqueLow).1
  have compare := card_sdiff_add_card_eq_card (insert_subset L.gate L.sub)
  rw [card_insert_of_notMem L.fresh] at compare
  change (k+1)/2≤(C \ insert w D).card at R
  have bigC : D.card+1+(k+1)/2≤C.card := by omega
  by_cases big : k≤D.card+2
  · have count := two_contacts h L conn (by omega) routes tails
    omega
  have width (y : V) (yd : y∈D) : k-D.card≤(contactPositions p y).card := by
    have degree := degree_split h (L.sub yd)
    have min := high y yd
    have max := capD y yd
    omega
  have count := core_ports h D L.sub (s:=k-D.card) (by omega) (by omega) width routes tails
  have lower := product_bound lo hi size (by omega)
  omega

end Graph189ExteriorLeaf
#print axioms Graph189ExteriorLeaf.no_short_leaf
