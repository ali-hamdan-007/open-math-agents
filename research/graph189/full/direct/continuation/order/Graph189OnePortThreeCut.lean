import Graph189OnePortCover
import Graph189LowAnchorOriginal
import Graph189EqualMinimumConnectivity
import Graph189TightCutJoint

open SimpleGraph Finset Graph189UniversalCycle
namespace Graph189OnePortCover
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Excluding a low vertex on a minimum cut raises the available order index by one. -/
theorem additional_index_of_exclusion (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (two : 2≤G.vertexConnectivity)
    (wide : 4*G.vertexConnectivity+1≤G.secondSmallestDegree)
    (exclude : ∀ (T : Finset V), T.card=G.vertexConnectivity →
      ¬(G.induce {v : V | v∉T}).Connected → ∀ z∈T, G.degree z<G.secondSmallestDegree →
        ∃a b, ∃p : G.Walk a b,p.IsHamiltonian)
    (bad : ¬∃a b, ∃p : G.Walk a b,p.IsHamiltonian) :
    (G.vertexConnectivity+2)*(G.secondSmallestDegree-(G.vertexConnectivity+1)+2)≤Fintype.card V+1 := by
  classical
  let s := G.vertexConnectivity
  let k := G.secondSmallestDegree
  change 2≤s at two
  change 4*s+1≤k at wide
  have point (v : V) : G.distEven v≤k+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  have up := (secondDegree_le_completeAt_minDegree (G:=G) z hz.symm).trans ((completeAt G z).minDegree_le_degree z)
  rw [completeAt_degree_self] at up
  change k≤Fintype.card V-1 at up
  have room : G.vertexConnectivity<Fintype.card V-1 := by change s<_; omega
  by_cases low : G.degree z<k
  · have free (T : Finset V) (sz : T.card=G.vertexConnectivity) (inside : z∈T) :
        (G.induce {v : V | v∉T}).Connected := by
      by_contra cut
      exact bad (exclude T sz cut z inside low)
    have conn := completeAt_connectivity_add_one z room free
    by_cases del : ∃a b, ∃p : (G.induce {x : V | x≠z}).Walk a b,p.IsHamiltonian
    · obtain ⟨a,b,p,hp⟩ := del
      have sep := Graph189CutSides.connectivity_le_degree (G:=G) z
      have gt : G.vertexConnectivity+1≤G.degree z := by
        by_contra! fail
        have equal : G.minDegree=G.vertexConnectivity := hz.trans (by omega)
        exact bad (Graph189EqualMinimumConnectivity.traceable hc cap two equal (by change 3*s<k; omega))
      exact Graph189ExteriorGap.order_of_traceable_low_deletion z low point bad p hp (s:=s+1) (by omega)
        (by change 2*(s+1)≤k; omega) gt
    have lo := Graph189RotationLinked.minimum_order z hz.symm bad del point (l:=s+1) (by omega)
      conn (by change 2*(s+1)+1≤k; omega)
    change (s+2)*(k-(s+1)+2)≤Fintype.card V+1
    change (s+2)*(k-(s+1)+2)-1≤Fintype.card V at lo
    omega
  have min : k≤G.minDegree := by rw [hz]; omega
  have lower := Graph189ArbitraryHalfExterior.critical_bondy_order bad point two wide room
    (by change k+2*s+2≤2*G.minDegree; omega)
  have size : k-(s+1)+2≤G.minDegree-(s+1)+2 := by omega
  have h := Nat.mul_le_mul_left (s+2) size
  change (s+2)*(G.minDegree-(s+1)+2)-1≤Fintype.card V at lower
  change (s+2)*(k-(s+1)+2)≤Fintype.card V+1
  omega

/-- The low-anchor theorem raises the order index by one above the separator incidence threshold. -/
theorem additional_index (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (two : 2≤G.vertexConnectivity)
    (large : G.vertexConnectivity^2+3*G.vertexConnectivity+2≤G.secondSmallestDegree)
    (bad : ¬∃a b, ∃p : G.Walk a b,p.IsHamiltonian) :
    (G.vertexConnectivity+2)*(G.secondSmallestDegree-(G.vertexConnectivity+1)+2)≤Fintype.card V+1 := by
  apply additional_index_of_exclusion hc cap two _ _ bad
  · nlinarith only [large,two,Nat.le_mul_self G.vertexConnectivity]
  · intro T size disconnected z zin low
    exact Graph189LowAnchorOriginal.traceable hc cap two large T size disconnected zin low

/-- Any low vertex in a separating pair has degree k−1. Restoring it
supplies the two genuine contacts for the tight-pair path theorem. -/
private theorem tight_pair (hc : G.Connected)
    (point : ∀v,G.distEven v≤G.secondSmallestDegree+1) (large : 5≤G.secondSmallestDegree)
    (conn : G.vertexConnectivity=2) (T : Finset V) (size : T.card=G.vertexConnectivity)
    (disconnected : ¬(G.induce {v : V | v∉T}).Connected) (z : V) (zin : z∈T)
    (low : G.degree z<G.secondSmallestDegree) :
    ∃a b, ∃p : G.Walk a b,p.IsHamiltonian := by
  classical
  have two := size.trans conn
  have survive : ∃v, v∉T := by
    by_contra! full
    have eq := eq_univ_iff_forall.mpr full
    rw [eq,card_univ] at two
    obtain ⟨w,hw⟩ := G.exists_minimal_degree_vertex
    have room := (secondDegree_le_completeAt_minDegree (G:=G) w hw.symm).trans ((completeAt G w).minDegree_le_degree w)
    rw [completeAt_degree_self] at room
    omega
  obtain ⟨A,B,sides⟩ := Graph189CutSides.exists_cutSides_of_disconnected T survive disconnected
  have smaller (X : Finset V) (h : X.card<T.card) :=
    Graph189CutSides.connected_after_smaller_deletion (G:=G) X (h.trans_eq size)
  have atLeast := sides.anchor_degree smaller (fun v => by simpa only [Nat.add_comm] using point v) zin
  have eq : G.degree z+1=G.secondSmallestDegree := by omega
  obtain ⟨⟨a,aa,az⟩,⟨b,bb,bz⟩⟩ := sides.contacts_of_minimum smaller zin
  have finish (t : V) (ne : z≠t) (form : T={z,t}) :=
    Graph189TightTwoCut.traceable hc (form ▸ sides) ne eq large point aa bb az.symm bz.symm
  obtain ⟨p,q,diff,form⟩ := Finset.card_eq_two.mp two
  have member : z=p ∨ z=q := by simpa [form] using zin
  rcases member with rfl|rfl
  · exact finish q diff form
  · exact finish p diff.symm (form.trans (Finset.pair_comm _ _))

/-- A two-cut puts the graph below the actual order floor whenever its
order plus five is strictly less than four times the second degree. -/
theorem below_four (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (two : 2≤G.vertexConnectivity) (large : 9≤G.secondSmallestDegree)
    (below : Fintype.card V+5<4*G.secondSmallestDegree) :
    ∃a b,∃r : G.Walk a b,r.IsHamiltonian := by
  classical
  by_contra bad
  by_cases three : 3≤G.vertexConnectivity
  · have point (u : V) : G.distEven u≤G.secondSmallestDegree+1 := by
      simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ u))).trans cap
    have lower := Graph189RotationLinked.base_order bad point (l:=3) (by decide) three (by omega)
    omega
  have conn : G.vertexConnectivity=2 := by omega
  have point (u : V) : G.distEven u≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ u))).trans cap
  have lower := additional_index_of_exclusion hc cap two (by rw [conn]; omega)
    (tight_pair hc point (by omega) conn) bad
  rw [conn] at lower
  omega

/-- A one-port cover on each side at a minimum three-cut forces an original
Hamiltonian path at all second degrees at least twenty. -/
theorem three_cut (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    {A B S : Finset V} (sides : Graph189CutSides.CutSides G A B S) (sc : S.card=G.vertexConnectivity)
    (three : S.card=3) (large : 20≤G.secondSmallestDegree) {x p y q : V}
    (left : Cover G A S x p) (right : Cover G B S y q) :
    ∃a b, ∃r : G.Walk a b,r.IsHamiltonian := by
  classical
  by_contra bad
  have conn : G.vertexConnectivity=3 := sc.symm.trans three
  have lo := additional_index hc cap (by omega) (by rw [conn]; omega) bad
  rw [conn] at lo
  have point (u : V) : G.distEven u≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ u))).trans cap
  have Acount := population hc sides.swap sc.le point right
  have Bcount := population hc sides sc.le point left
  have hp : (Graph189PortLabels.support G S p).card≤S.card := card_le_card (filter_subset _ _)
  have hq : (Graph189PortLabels.support G S q).card≤S.card := card_le_card (filter_subset _ _)
  have total := Graph189SoleNearestSides.order_of_high_sides sides
  omega

#print axioms additional_index
#print axioms three_cut
end Graph189OnePortCover
