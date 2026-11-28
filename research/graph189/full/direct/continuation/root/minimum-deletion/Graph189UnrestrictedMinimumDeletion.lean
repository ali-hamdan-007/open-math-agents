import Graph189UniformExchangeInterface
import Graph189BalancedContactRows
import Graph189FullGapPositions

open Finset SimpleGraph Graph189ExteriorGap Graph189ContactGroupCensus
namespace Graph189RootedSplice
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem omitted_plus_vertices {a b : V} (q : G.Walk a b) (hq : q.IsPath) :
    ((univ : Finset V) \ q.support.toFinset).card+q.support.length=Fintype.card V := by
  have c := card_sdiff_add_card_inter (univ : Finset V) q.support.toFinset
  rwa [univ_inter,List.toFinset_card_of_nodup hq.support_nodup,card_univ] at c

private theorem transfer_contacts {a b : V} (q : G.Walk a b)
    (A : Finset ℕ) (uniform : ∀ v : {w : V // w∈((univ : Finset V) \ q.support.toFinset)}, contactPositions q v.val=A)
    {i j : V} (iOff : i∉q.support) (jOff : j∉q.support) {c : V} (member : c∈q.support)
    (edge : G.Adj c i) : G.Adj c j := by
  let x : {w : V // w∈((univ : Finset V) \ q.support.toFinset)} := ⟨i,mem_sdiff.mpr ⟨mem_univ _,fun h => iOff (List.mem_toFinset.mp h)⟩⟩
  let y : {w : V // w∈((univ : Finset V) \ q.support.toFinset)} := ⟨j,mem_sdiff.mpr ⟨mem_univ _,fun h => jOff (List.mem_toFinset.mp h)⟩⟩
  obtain ⟨t,valid,value⟩ := List.mem_iff_getElem.mp member
  have atPos := (get_at q valid).symm.trans value
  have hit : t∈contactPositions q x.val := (mem_contactPositions _ _ _).mpr ⟨valid,by rwa [atPos]⟩
  rw [uniform x,←uniform y] at hit
  have actual := ((mem_contactPositions _ _ _).mp hit).2
  rwa [atPos] at actual

/-- All required contact censuses and swaps are made on actual paths in G. -/
theorem uniform_gap_exclusion : UniformGapExclusion G := by
  classical
  intro root m u k two balanced total cap budget initial setup
  obtain ⟨x,y,p,hp,rootOn,order,longest⟩ := initial
  have uniform {a b : V} (q : G.Walk a b) (hq : q.IsPath) (on : root∈q.support)
      (mx : ∀ {x y}, ∀ s : G.Walk x y, s.IsPath → root∈s.support → s.length≤q.length)
      (eq : ((univ : Finset V) \ q.support.toFinset).card=m) :
      ∃ A : Finset ℕ, A.card=u ∧ ∀ v : {w : V // w∈((univ : Finset V) \ q.support.toFinset)}, contactPositions q v.val=A := by
    let E : Finset V := univ \ q.support.toFinset
    obtain ⟨routes,rows⟩ := setup q hq on mx eq
    obtain ⟨j,range,value⟩ := List.mem_iff_getElem.mp on
    let t : Fin q.support.length := ⟨j,range⟩
    have position : q.support[t.val]=root := value
    have num := omitted_plus_vertices q hq
    refine uniform_of_protected_census q hq t (fun r hr member => mx r hr (position ▸ member))
      E (fun w hw h => (mem_sdiff.mp hw).2 (List.mem_toFinset.mpr h)) routes u two
      (by change u≤((univ : Finset V) \ q.support.toFinset).card; omega) rows ?_
    change q.support.length+((univ : Finset V) \ q.support.toFinset).card+2≤_
    rw [eq]
    omega
  let E : Finset V := univ \ p.support.toFinset
  have omits (i : V) (h : i∈E) : i∉p.support := fun on =>
    (mem_sdiff.mp h).2 (List.mem_toFinset.mpr on)
  obtain ⟨A,marks,old⟩ := uniform p hp rootOn longest order
  obtain ⟨routes,_⟩ := setup p hp rootOn longest order
  have count : Fintype.card E=m := by rw [Fintype.card_coe]; exact order
  have many : 1<(univ : Finset E).card := by rw [card_univ,count]; omega
  obtain ⟨a,_⟩ := card_pos.mp (by omega : 0<(univ : Finset E).card)
  obtain ⟨b,_,different⟩ := exists_mem_ne many a
  have oldEdge (v : V) (on : v∈p.support) : G.Adj v a.val → G.Adj v b.val :=
    transfer_contacts p A old (omits _ a.property) (omits _ b.property) on
  obtain ⟨i,valid,atRoot⟩ := List.mem_iff_getElem.mp rootOn
  let t : Fin p.support.length := ⟨i,valid⟩
  have location : p.getVert t.val=root := (get_at p valid).symm.trans atRoot
  have num := omitted_plus_vertices p hp
  have room : p.support.length+m+2≤(u+1)*(m+1)+u := by omega
  have rowCount : (contactPositions p a.val).card=u := by rw [old a,marks]
  obtain ⟨I,J,dis,safeI,safeJ⟩ := two_full_gaps_on_protected_path p hp root t location longest
    E m u order two balanced omits a b different.symm routes oldEdge rowCount room
  have alt {c e : V} (q : G.Walk c e) (hq : q.IsPath) (on : root∈q.support) (same : q.length=p.length) :
      ∀ i, i∉q.support → ∀ j, j∉q.support → ∀ w∈q.support, G.Adj w i → G.Adj w j := by
    have longestQ {f g} (s : G.Walk f g) (hs : s.IsPath) (mem : root∈s.support) : s.length≤q.length := by
      rw [same]
      exact longest s hs mem
    have sizes := omitted_plus_vertices q hq
    have lp := p.length_support
    have lq := q.length_support
    have eq : ((univ : Finset V) \ q.support.toFinset).card=m := by omega
    obtain ⟨B,_,common⟩ := uniform q hq on longestQ eq
    intro i hi j hj w hw
    exact transfer_contacts q B common hi hj hw
  have measure (g : TightGap p a.val m) (safe : root∉g.block) :=
    full_gap_dist_two p hp root rootOn E m order omits a b different.symm routes oldEdge
      (fun r hr on same => alt r hr on same) g safe
  have excess := even_budget_of_full_gaps p hp a.val m k I J dis (measure I safeI) (measure J safeJ) (cap a.val)
  omega

/-- A Hamiltonian path after deleting a minimum-degree vertex of degree
at least three guarantees a Hamiltonian path of the original Graph 189 graph. -/
theorem traceable_of_hamiltonian_minimum_deletion_unrestricted (hc : G.Connected) (z : V)
    (least : G.degree z=G.minDegree) (three : 3≤G.degree z) (k5 : 5≤G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    {a b : {w : V | w≠z}} (r : (G.induce {w : V | w≠z}).Walk a b)
    (hr : r.IsHamiltonian) : ∃ x y, ∃ p : G.Walk x y, p.IsHamiltonian :=
  traceable_of_minimum_deletion_via_uniform_exchange uniform_gap_exclusion hc z least three k5 cap r hr

#print axioms uniform_gap_exclusion
#print axioms traceable_of_hamiltonian_minimum_deletion_unrestricted
end Graph189RootedSplice
