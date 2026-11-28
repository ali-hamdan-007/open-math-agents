import Graph189SmallMixedOrders
import Graph189MixedDeepCounts
import Graph189CleanTwoAnchorJoin

open SimpleGraph Finset Graph189DeepCommonPair
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189SmallMixedPair

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

private theorem loss_or_clique {k n a b : ℕ} (lo : 7≤k) (hi : k≤8)
    (bound : 2*n≤7*k) (partition : a+b+2=n) (lower : k≤b) (small : b+1≤2*k) :
    max 1 (a-(2*k-4))+(b-(2*k-2))+3≤k ∨
      (b=k ∧ max 1 (a-(2*k-4))+2≤k) := by
  omega

/-- A deep common side opposite a clean, common-free side at degrees seven
and eight. In the remaining size rows, the order-k private side is a clique
and the two-anchor join saves one omission. -/
theorem deep_clean_small (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 7≤G.secondSmallestDegree) (small : G.secondSmallestDegree≤8)
    (minimum : 3≤G.minDegree) (big : 3*G.secondSmallestDegree+2<Fintype.card V)
    (floor : 4*G.secondSmallestDegree≤Fintype.card V+5)
    (sides : Graph189CutSides.CutSides G A B S) (pair : S={p,q}) (ne : p≠q) (sc : S.card≤G.vertexConnectivity)
    (nonadj : ¬G.Adj p q) (cleanB : Graph189CleanSideCounts.Clean G B p q)
    (conA : (G.induce (A:Set V)).Connected) (conB : (G.induce (B:Set V)).Connected)
    (common : ∃x∈A,∀i∈S,G.Adj x i) (deep : ∃y,Deep G A S y) :
    ∃u v, ∃r : G.Walk u v,r.IsHamiltonian := by
  classical
  let k := G.secondSmallestDegree
  let R (W : Finset V) := (W.filter (fun x => G.dist p x≠1 ∧ G.dist q x≠1)).card
  let T := A.filter (fun x => G.dist p x=1 ∧ G.dist q x=1)
  have sz : S.card=2 := by simp [pair,ne]
  have ps : p∈S := by simp [pair]
  have qs : q∈S := by simp [pair]
  have n := total sides sz
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have row := Graph189CleanPairOrder.nonport_order hc point sides.swap pair ne sc big cleanB
  change Fintype.card V+R B+R A+T.card≤4*k+2 at row
  have column := Graph189PrivateContactProfile.order_of_common hc sides pair ne sc point cleanB.private_ports common
  change A.card+3≤2*k+R A at column
  obtain ⟨z,za,both⟩ := common
  have share : 1≤T.card := card_pos.mpr ⟨z,mem_filter.mpr ⟨za,
    dist_eq_one_iff_adj.mpr (both p ps).symm,dist_eq_one_iff_adj.mpr (both q qs).symm⟩⟩
  have portsB : (ports G B S).card≤k := port_bound hc sides point za both
  have sums (W : Finset V) : (ports G W S).card+R W=W.card := by
    have eq : W.filter (fun x => ¬∃i∈S,G.Adj i x)=
        W.filter (fun x => G.dist p x≠1 ∧ G.dist q x≠1) := by
      ext x
      simp [pair,dist_eq_one_iff_adj,not_or]
    simpa only [ports,R,←eq] using (card_filter_add_card_filter_not (s:=W) (p:=fun x => ∃i∈S,G.Adj i x))
  have sumA := sums A
  have sumB := sums B
  have order : 2*Fintype.card V≤7*k := by omega
  have upper : Fintype.card V≤5*G.secondSmallestDegree-5 := by change Fintype.card V≤5*k-5; omega
  have room : A.card<2*(G.secondSmallestDegree-1)+(ports G A S).card := by
    change A.card<2*(k-1)+(ports G A S).card
    change 4*k≤Fintype.card V+5 at floor
    change 7≤k at large
    omega
  obtain ⟨y,hy⟩ := deep
  have sideBound := Graph189MixedDeepCounts.opposite hc point sides.swap sc sz hy za both
  have two := Graph189DirtyRoutes.contacts hc point sides.swap pair sc big cleanB.private_ports
  obtain ⟨u,up,v,vp,uv⟩ := one_lt_card.mp two
  have regular (v : B) (hv : k≤G.degree v.val) : k≤B.card := by
    have lost := Graph189CleanSideRoute.loss sides.swap pair cleanB.private_ports v
    have fit := (G.induce (B:Set V)).degree_lt_card_verts v
    change _<Fintype.card B at fit
    rw [Fintype.card_coe] at fit
    omega
  have bmin := (degree_pair (G:=G) u v uv).elim (regular ⟨u,(mem_filter.mp up).1⟩)
    (regular ⟨v,(mem_filter.mp vp).1⟩)
  rcases loss_or_clique large small order n bmin sideBound with fits | ⟨bsize,lossA⟩
  · exact mixed hc cap large minimum big upper sides pair ne sc nonadj cleanB.private_ports conA conB
      (Or.inl ⟨sideBound,room⟩) fits
  have maxDegree (v : B) (hv : k≤G.degree v.val) : B.card-1≤(G.induce (B:Set V)).degree v := by
    have lost := Graph189CleanSideRoute.loss sides.swap pair cleanB.private_ports v
    omega
  have complete := Graph189CleanTwoAnchorJoin.complete_of_max_degree (G:=G) B
    (fun u v apart => (degree_pair (G:=G) u.val v.val (fun eq => apart (Subtype.ext eq))).imp
      (maxDegree u) (maxDegree v))
  have sub : A.filter (G.Adj p)⊆ports G A S := fun v h =>
    mem_filter.mpr ⟨(mem_filter.mp h).1,p,ps,(mem_filter.mp h).2⟩
  have many := (Graph189BalancedPair.two_contacts hc point sides sc pair nonadj big).trans (card_le_card sub)
  obtain ⟨x,xP,w,Q,hQ,inA,len⟩ := Graph189SmallPrivatePair.common_from_marks sides pair ne conA large minimum
    (ports G A S) (filter_subset _ _) many (fun v va e => mem_filter.mpr ⟨va,p,ps,e⟩) room
  obtain ⟨_,i,iS,ix⟩ := mem_filter.mp xP
  have contact (j : V) (jS : j∈S) :=
    (sides.contacts_of_minimum (fun T h => Graph189CutSides.connected_after_smaller_deletion T
      (h.trans_le sc)) jS).2
  obtain ⟨a,ab,ap⟩ := contact p ps
  obtain ⟨b,bb,bq⟩ := contact q qs
  have abDifferent : a≠b := fun eq => cleanB.private_ports a ab ⟨ap,eq.symm ▸ bq⟩
  have finish {t : V} (r : G.Walk t w) (hr : r.IsPath)
      (near : Fintype.card V≤r.support.length+max 1 (A.card-(2*k-4))) :=
    Graph189ExteriorLeaf.traceable_of_near_degree hc cap large upper minimum r hr (by omega)
  rcases (show i=p ∨ i=q by simpa [pair] using iS) with rfl|rfl
  · obtain ⟨r,hr,near⟩ := Graph189CleanTwoAnchorJoin.join_complete sides.swap pair ne bb ab abDifferent.symm
      complete bq.symm ap Q hQ inA ix len
    exact finish r hr near
  obtain ⟨r,hr,near⟩ := Graph189CleanTwoAnchorJoin.join_complete sides.swap
    (pair.trans (Finset.pair_comm _ _)) ne.symm ab bb abDifferent complete ap.symm bq Q hQ inA ix len
  exact finish r hr near

#print axioms deep_clean_small
end Graph189SmallMixedPair
