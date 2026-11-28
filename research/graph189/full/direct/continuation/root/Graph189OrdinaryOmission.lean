import Graph189MinimumDeletionTraceable
import Graph189DenseExteriorOrder
import Graph189DegreeTwoOriginal
import Graph189PrescribedBatch
import Graph189ThreeRegularMinimum

open SimpleGraph Finset Graph189ExteriorGap Graph189ExteriorDegreeCycle
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189OrdinaryOmission
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Remove a single minimum-degree vertex from the exterior of a longest
path. The remaining vertices have half-degree up to a loss of one. In the
small-exterior range they therefore admit all prescribed spanning paths. -/
theorem small_exterior_order_extended {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length ≤ p.length)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) (minimum : ∀ v, 3≤G.degree v)
    {m : ℕ} (size : (p.support.toFinsetᶜ : Finset V).card=m) (two : 2≤m)
    (small : m+2≤G.secondSmallestDegree) :
    (G.secondSmallestDegree+1)/2+1≤m ∧ m*(G.secondSmallestDegree+3-m) ≤ Fintype.card V+2 := by
  classical
  let k := G.secondSmallestDegree
  let E := p.support.toFinsetᶜ
  change E.card=m at size
  change m+2≤k at small
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  let W := E.erase z
  have wsize : m-1≤W.card := by
    by_cases h : z∈E
    · have := card_erase_add_one h
      change m-1≤(E.erase z).card
      omega
    · simp [W,erase_eq_of_notMem h,size]
  have le : W.card≤m := (card_le_card (erase_subset z E)).trans size.le
  have out (w : V) (mem : w∈E) : w∉p.support := by simpa [E] using mem
  have high (w : V) (mem : w∈W) : k≤G.degree w := by
    rcases degree_pair (G:=G) w z (mem_erase.mp mem).1 with h|h
    · exact h
    · rw [←hz] at h
      exact h.trans (G.minDegree_le_degree _)
  have quota (w : V) : (univ.filter (fun v => G.dist w v=2)).card≤k := by
    let T := univ.filter (fun v => G.dist w v=2)
    have no : w∉T := by simp [T]
    have inc : insert w T ⊆ univ.filter (fun v => Even (G.dist w v)) := by
      intro v hv
      rcases mem_insert.mp hv with rfl|h
      · simp
      · exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2 ▸ (by decide : Even (2:ℕ))⟩
    have bd := card_le_card inc
    rw [card_insert_of_notMem no] at bd
    have h := cap w
    change T.card+1≤G.distEven w at bd
    change G.distEven w≤k+1 at h
    change T.card≤k
    omega
  have unique (a b : V) (la : G.degree a<k) (lb : G.degree b<k) : a=b := by
    by_contra ne
    exact (degree_pair (G:=G) a b ne).elim (fun h => False.elim ((not_le.mpr la) h))
      (fun h => False.elim ((not_le.mpr lb) h))
  obtain ⟨w,hw⟩ := card_pos.mp (show 0<W.card by omega)
  have actual := high_outside_order_gap p hp longest (out w (mem_erase.mp hw).2)
    (quota w) (high w hw) minimum unique
  have total := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at total
  change p.support.length+E.card=Fintype.card V at total
  have floor : (k+1)/2+1≤m := by omega
  let H := G.induce (W : Set V)
  have internal (w : W) : k ≤ 2*(H.degree w+1) ∧ (z∉E → k≤2*H.degree w) := by
    let D := G.neighborFinset w.val \ p.support.toFinset
    have half := (high_exterior_half p hp longest (out _ (mem_erase.mp w.property).2)
      (quota _) (high _ w.property) minimum unique).2
    change G.degree w.val≤2*D.card at half
    have eq : H.degree w=(D.erase z).card := by
      rw [degree_induce_filter]
      congr 1
      ext v
      simp [D,W,E,and_assoc,and_comm]
    have debit : D.card≤(D.erase z).card+1 := by
      by_cases h : z∈D
      · exact (card_erase_add_one h).ge
      · simp [erase_eq_of_notMem h]
    have := high _ w.property
    refine ⟨by omega,fun absent => ?_⟩
    have nz : z∉D := fun h => absent (mem_compl.mpr (mem_sdiff.mp h).2)
    rw [erase_eq_of_notMem nz] at eq
    omega
  have hc (a b : W) (ne : a≠b) : ∃ q : H.Walk a b, q.IsHamiltonian := by
    apply Graph189TerminalLeafClosure.prescribed_of_supergraph (G:=H) le_top _
      (Graph189TerminalLeafClosure.complete_prescribed a b ne)
    intro u v _ _
    have d1 := internal u
    have d2 := internal v
    change Fintype.card W+1≤H.degree u+H.degree v
    rw [Fintype.card_coe]
    by_cases member : z∈E
    · have count := card_erase_add_one member
      change W.card+1=E.card at count
      have du := d1.1
      have dv := d2.1
      omega
    have du := d1.2 member
    have dv := d2.2 member
    omega
  let j := k+1-m
  have counts (w : V) (hw : w∈W) : j≤((univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] w)).card := by
    have degree := Graph189DenseExteriorOrder.neighbors_on_path p E
      (fun _ _ _ _ no => by simpa [E] using no) (mem_erase.mp hw).2
    have := high w hw
    dsimp [j]
    omega
  obtain ⟨M,eq,ports,edges⟩ := Graph189ExteriorAttachment.marks_of_many_neighbors p W j
    (by dsimp [j]; omega) counts
  have bd := exterior_hamilton_connected_matching p hp longest W (by omega)
    (fun w hw => out _ (mem_erase.mp hw).2) hc M (card_pos.mp (by dsimp [j] at eq; omega)) ports edges
  rw [eq] at bd
  have product := Nat.mul_le_mul_left (j+2) wsize
  have lift : m-1+1=m := by omega
  have bookkeeping : (j+2)*m = (j+2)*(m-1)+j+2 := by
    calc
      _ = (j+2)*(m-1+1) := by rw [lift]
      _ = _ := by ring
  have offset : k+3-m=j+2 := by dsimp [j]; omega
  refine ⟨floor,?_⟩
  change m*(k+3-m)≤_
  rw [offset,Nat.mul_comm m,bookkeeping]
  omega

/-- The original three-vertex margin follows from the stronger exterior bound. -/
theorem small_exterior_order {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length ≤ p.length)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) (minimum : ∀ v, 3≤G.degree v)
    {m : ℕ} (size : (p.support.toFinsetᶜ : Finset V).card=m) (two : 2≤m)
    (small : m+3≤G.secondSmallestDegree) :
    (G.secondSmallestDegree+1)/2+1≤m ∧ m*(G.secondSmallestDegree+3-m) ≤ Fintype.card V+2 :=
  small_exterior_order_extended p hp longest cap minimum size two (by omega)

/-- At every order and every connectivity at least two, a path missing at
most k+1−floor((k+2)/4) vertices suffices for traceability at k≥26. -/
theorem traceable_of_near (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (conn : 2≤G.vertexConnectivity) (large : 26≤G.secondSmallestDegree)
    {a b : V} (r : G.Walk a b) (hr : r.IsPath)
    (near : Fintype.card V≤r.support.length+G.secondSmallestDegree+1-(G.secondSmallestDegree+2)/4) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let k := G.secondSmallestDegree
  let l := (k+2)/4
  change 26≤k at large
  have point (v : V) : G.distEven v≤k+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  obtain ⟨z,eq⟩ := G.exists_minimal_degree_vertex
  have minz := Graph189CutSides.connectivity_le_degree (G:=G) z
  by_cases two : G.degree z=2
  · exact Graph189DegreeTwoOriginal.traceable hc cap conn z two (by omega)
  have minimum (v : V) : 3≤G.degree v := by
    have := G.minDegree_le_degree v
    omega
  by_contra bad
  have noLow (v : V) (low : G.degree v<k)
      (path : ∃ x y, ∃ q : (G.induce {t : V | t≠v}).Walk x y, q.IsHamiltonian) : False := by
    obtain ⟨x,y,q,hq⟩ := path
    have minv : G.degree v=G.minDegree := by
      by_cases same : v=z
      · exact same ▸ eq.symm
      rcases degree_pair (G:=G) v z same with h|h
      · omega
      have := G.minDegree_le_degree v
      omega
    exact bad (Graph189StructuralConclusion.traceable_of_traceable_minimum_deletion hc cap large
      v minv (minimum v) q hq)
  obtain ⟨x,y,p,hp,maximal⟩ := Graph189ThreeRegularMinimum.longest_path (G:=G) z
  let m := (p.support.toFinsetᶜ : Finset V).card
  have total := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at total
  change p.support.length+m=Fintype.card V at total
  have gap := gap_of_no_hamiltonian_low_deletion bad (by omega) point minimum noLow x y p hp
  have len := maximal r hr
  have rl := r.length_support
  have pl := p.length_support
  change Fintype.card V≤r.support.length+k+1-l at near
  have ub : m≤k+1-l := by dsimp [l] at *; omega
  obtain ⟨floor,prod⟩ := small_exterior_order p hp maximal point minimum (m:=m) rfl
    (by omega) (by change m+3≤k; dsimp [l] at ub; omega)
  change (k+1)/2+1≤m at floor
  change m*(k+3-m)≤Fintype.card V+2 at prod
  have lsmall : l+2≤m := by dsimp [l]; omega
  have lcomp : l≤k := by dsimp [l]; omega
  have mk : m≤k := by dsimp [l] at ub; omega
  have comp : (l+1)*(k-l+2)≤Fintype.card V+1 := by
    zify [mk,lcomp,show m≤k+3 by omega] at prod ⊢
    have prod' := mul_nonneg (show 0≤(m:ℤ)-l-2 by omega) (show 0≤(k:ℤ)+1-l-m by omega)
    have diff : 2*(l:ℤ)+2≤k := by dsimp [l]; omega
    nlinarith only [prod,prod',diff]
  have base := (Graph189QuarterOrder.lower_estimates large comp).1
  have width := Graph189ActualScalarWidth.bounds hc cap bad (by change 4*k+2≤_; omega)
  exact Graph189QuarterOrder.impossible large comp width.1 width.2.1 width.2.2.2.1 width.2.2.2.2

#print axioms small_exterior_order
#print axioms traceable_of_near
end Graph189OrdinaryOmission
