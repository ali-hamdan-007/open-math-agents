import Graph189BondyExterior
import Graph189CriticalExterior
import Graph189LongestCycleMaximum

open Finset SimpleGraph Graph189ExteriorDegreeCycle Graph189UniversalCycle
namespace Graph189RepairedConeOrder
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- If completion both raises connectivity and attains the second degree,
the surviving original deletion has degree at least k−1 at every vertex.
At k≥7 this produces a four-cycle or longer in every longest-cycle exterior. -/
theorem order_three (w : V) (k7 : 7≤G.secondSmallestDegree)
    (notTrace : ¬∃ a b, ∃ q : G.Walk a b, q.IsHamiltonian)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    (half : G.secondSmallestDegree<2*G.minDegree)
    (conn : 3≤(completeAt G w).vertexConnectivity) (min : G.secondSmallestDegree≤(completeAt G w).minDegree) :
    4*(G.secondSmallestDegree-3+2)-1≤Fintype.card V := by
  classical
  let K := completeAt G w
  let k := G.secondSmallestDegree
  change 7≤k at k7
  change k<2*G.minDegree at half
  change k≤K.minDegree at min
  have two (v : V) : 2≤K.degree v := by have := K.minDegree_le_degree v; omega
  obtain ⟨b,R,hR,_⟩ := cycle_of_degree (G:=K) w (d:=2) (by decide) two
  obtain ⟨a,C,hC,mxC⟩ := exists_longest_cycle K ⟨b,R,hR⟩
  let U : Set V := {v | v≠w}
  let H := G.induce U
  have same : K.induce U=H := by
    ext x y
    constructor
    · rintro (orig|⟨touch,_⟩)
      · exact orig
      · exact (touch.elim x.property y.property).elim
    · exact fun e => Or.inl e
  have inH (v : U) : k≤H.degree v+1 := by
    have loss := degree_le_deletion_add_one (G:=K) w v
    change K.degree v.val≤(K.induce U).degree v+1 at loss
    have comp := degree_le_of_le (v:=v) same.le
    exact min.trans ((K.minDegree_le_degree v.val).trans (loss.trans (Nat.add_le_add_right comp 1)))
  obtain ⟨u,v,p,hp,_,supp,maxp⟩ := longest_in_deletion G w C hC mxC
  have mx {x y} (q : H.Walk x y) (hq : q.IsPath) : q.length≤p.length := maxp _ _ q hq
  let T : Set U := {t | t∉p.support.toFinset}
  let J := H.induce T
  have gap := high_min_all_paths_gap notTrace (by change 5≤k; omega) cap (fun t => by
    have := G.minDegree_le_degree t
    change k<2*G.degree t
    omega)
  have missed := deletion_gap w p hp gap
  have edge : ∃ x y : T, J.Adj x y := by
    by_contra! no
    have independent : ∀ a∉p.support, ∀ b∉p.support, ¬H.Adj a b := by
      intro a ha b hb
      exact no ⟨a,fun h => ha (List.mem_toFinset.mp h)⟩ ⟨b,fun h => hb (List.mem_toFinset.mp h)⟩
    have ub := independent_omits_at_most_two w p hp mx independent (by change 2≤k; omega) cap
    omega
  have degree (x y : T) (adj : J.Adj x y) : 3≤J.degree x := by
    have lim := induced_second_layer U x.val (cap x.val.val)
    have bound := Graph189ExteriorGap.cross_contact_degree p hp mx
      (a:=x.val) (b:=y.val) (fun h => x.property (List.mem_toFinset.mpr h))
      (fun h => y.property (List.mem_toFinset.mpr h)) adj lim
    have pop := card_sdiff_add_card_inter (H.neighborFinset x.val) p.support.toFinset
    have dx := inH x.val
    have dy := inH y.val
    change (H.neighborFinset x.val∩p.support.toFinset).card+H.degree y.val ≤
      k+(H.neighborFinset x.val\p.support.toFinset).card at bound
    change _+_=H.degree x.val at pop
    change 3≤(H.induce T).degree x
    rw [degree_induce_filter]
    have filt : (H.neighborFinset x.val).filter (fun v => v∈T)=H.neighborFinset x.val\p.support.toFinset := by
      ext t
      simp [T]
    rw [filt]
    omega
  obtain ⟨r,q,hq,sz⟩ := cycle_of_nonisolated_degree (G:=J) (d:=3) (by decide) edge degree
  let f : J →g K.induce {t : V | t∉C.support} := {
    toFun := fun t => ⟨t.val.val,fun h => t.property (List.mem_toFinset.mpr ((supp _).mpr h))⟩
    map_rel' := fun h => Or.inl h }
  have inj : Function.Injective f := fun x y h => Subtype.ext (Subtype.ext
    (congrArg (fun t : {v : V | v∉C.support} => t.val) h))
  have long : 4≤(q.map f).length := by rwa [Walk.length_map]
  have order := Graph189BondyExterior.order_of_long_exterior (G:=K) (k:=3) (by decide) conn
    (by omega) C hC mxC (q.map f) (hq.map inj) long (by omega)
  change 4*(k-3+2)-1≤Fintype.card V
  omega

end Graph189RepairedConeOrder
#print axioms Graph189RepairedConeOrder.order_three
