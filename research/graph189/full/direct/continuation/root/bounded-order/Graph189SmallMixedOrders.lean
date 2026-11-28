import Graph189SmallMixedPaths
import Graph189ShallowMixedCensus
import Graph189CleanPairOrder
import Graph189CommonContactDebit

open SimpleGraph Finset Graph189DeepCommonPair
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189SmallMixedPair
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

omit [Nontrivial V] [DecidableRel G.Adj] in
theorem total (sides : Graph189CutSides.CutSides G A B S) (size : S.card=2) :
    A.card+B.card+2=Fintype.card V := by
  have all : A∪B∪S=univ := eq_univ_of_forall (by
    intro u
    rcases sides.cover u with h|h|h
    · exact mem_union_left _ (mem_union_left _ h)
    · exact mem_union_left _ (mem_union_right _ h)
    · exact mem_union_right _ h)
  have count := congrArg Finset.card all
  rwa [card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨sides.left_cut,sides.right_cut⟩),
    card_union_of_disjoint sides.apart,size,card_univ] at count

private theorem port_sum (W : Finset V) (pair : S={p,q}) :
    (ports G W S).card+(W.filter (fun x => G.dist p x≠1 ∧ G.dist q x≠1)).card=W.card := by
  classical
  have eq : W.filter (fun v => ¬∃i∈S,G.Adj i v)=W.filter (fun v => G.dist p v≠1 ∧ G.dist q v≠1) := by
    ext v
    simp [pair,dist_eq_one_iff_adj,not_or]
  simpa only [ports,←eq] using (card_filter_add_card_filter_not (s:=W) (p:=fun v => ∃i∈S,G.Adj i v))

/-- Both sides have order below twice k. The common side costs at most three
vertices, and the common-free side costs at most one. -/
theorem balanced (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 7≤G.secondSmallestDegree) (minimum : 3≤G.minDegree) (big : 3*G.secondSmallestDegree+2<Fintype.card V)
    (sides : Graph189CutSides.CutSides G A B S) (pair : S={p,q}) (ne : p≠q) (sc : S.card≤G.vertexConnectivity)
    (nonadj : ¬G.Adj p q) (free : ∀x∈B,¬(G.Adj x p ∧ G.Adj x q))
    (conA : (G.induce (A:Set V)).Connected) (conB : (G.induce (B:Set V)).Connected)
    (ordA : A.card+1≤2*G.secondSmallestDegree) (ordB : B.card+1≤2*G.secondSmallestDegree) :
    ∃u v, ∃r : G.Walk u v,r.IsHamiltonian := by
  classical
  have n := total sides (by simp [pair,ne])
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have many := Graph189BalancedPair.two_contacts hc point sides sc pair nonadj big
  have sub : A.filter (G.Adj p)⊆ports G A S := fun x hx =>
    mem_filter.mpr ⟨(mem_filter.mp hx).1,p,by simp [pair],(mem_filter.mp hx).2⟩
  have sz := card_le_card sub
  exact mixed hc cap large minimum big (by omega) sides pair ne sc nonadj free conA conB (Or.inl ⟨ordB,by omega⟩) (by omega)

/-- The shallow common side has both private contact types; the opposite
common-free side is large. Keeping the port count in the census gives at
least six starting ports. -/
theorem large_shallow (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 7≤G.secondSmallestDegree) (small : G.secondSmallestDegree≤10) (minimum : 3≤G.minDegree)
    (big : 3*G.secondSmallestDegree+2<Fintype.card V)
    (sides : Graph189CutSides.CutSides G A B S) (pair : S={p,q}) (ne : p≠q) (sc : S.card≤G.vertexConnectivity)
    (nonadj : ¬G.Adj p q) (free : ∀x∈B,¬(G.Adj x p ∧ G.Adj x q))
    (conA : (G.induce (A:Set V)).Connected) (conB : (G.induce (B:Set V)).Connected)
    (shallow : ∀x∈A,G.secondSmallestDegree≤G.degree x → ∃i∈S,G.Adj i x) (wide : 2*G.secondSmallestDegree≤B.card)
    (common : ∃x∈A,∀i∈S,G.Adj x i)
    (privateP : ∃x∈A,G.Adj x p ∧ ¬G.Adj x q) (privateQ : ∃x∈A,G.Adj x q ∧ ¬G.Adj x p) :
    ∃u v, ∃r : G.Walk u v,r.IsHamiltonian := by
  classical
  have n := total sides (by simp [pair,ne])
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  obtain ⟨a,count,limit⟩ := Graph189ShallowMixedPair.census_with_ports hc sides pair ne nonadj sc conA point wide
    shallow free common privateP privateQ
  change 2*Fintype.card V≤6*G.secondSmallestDegree+(ports G B S).card at count
  change (ports G B S).card≤G.secondSmallestDegree at limit
  exact mixed hc cap large minimum big (by omega) sides pair ne sc nonadj free conA conB (Or.inr ⟨by omega,by omega⟩) (by omega)

/-- A clean common-free side bounds all nonports across the two sides.
An opposite common port pays in both anchor columns, so 2n≤7k. -/
theorem clean (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 9≤G.secondSmallestDegree) (minimum : 3≤G.minDegree) (big : 3*G.secondSmallestDegree+2<Fintype.card V)
    (floor : 4*G.secondSmallestDegree≤Fintype.card V+5)
    (sides : Graph189CutSides.CutSides G A B S) (pair : S={p,q}) (ne : p≠q) (sc : S.card≤G.vertexConnectivity)
    (nonadj : ¬G.Adj p q) (cleanB : Graph189CleanSideCounts.Clean G B p q)
    (conA : (G.induce (A:Set V)).Connected) (conB : (G.induce (B:Set V)).Connected)
    (common : ∃x∈A,∀i∈S,G.Adj x i) : ∃u v, ∃r : G.Walk u v,r.IsHamiltonian := by
  classical
  let k := G.secondSmallestDegree
  let R (W : Finset V) := (W.filter (fun x => G.dist p x≠1 ∧ G.dist q x≠1)).card
  let T := A.filter (fun v => G.dist p v=1 ∧ G.dist q v=1)
  have n := total sides (by simp [pair,ne])
  have lo : 9≤k := large
  change 4*k≤Fintype.card V+5 at floor
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have row := Graph189CleanPairOrder.nonport_order hc point sides.swap pair ne sc big cleanB
  change Fintype.card V+R B+R A+T.card≤4*k+2 at row
  have col := Graph189PrivateContactProfile.order_of_common hc sides pair ne sc point cleanB.private_ports common
  change A.card+3≤2*k+R A at col
  obtain ⟨z,za,both⟩ := common
  have share : 1≤T.card := card_pos.mpr ⟨z,mem_filter.mpr ⟨za,dist_eq_one_iff_adj.mpr (both p (by simp [pair])).symm,
    dist_eq_one_iff_adj.mpr (both q (by simp [pair])).symm⟩⟩
  have marks : (ports G B S).card≤k := port_bound hc sides point za both
  have sumB : (ports G B S).card+R B=B.card := port_sum _ pair
  have sumA : (ports G A S).card+R A=A.card := port_sum _ pair
  have two := Graph189DirtyRoutes.contacts hc point sides.swap pair sc big cleanB.private_ports
  obtain ⟨x,xp,y,yp,xy⟩ := one_lt_card.mp two
  have reg (v : V) (vc : v∈B) (h : k≤G.degree v) : k≤B.card := by
    let t : B := ⟨v,vc⟩
    have drop := Graph189CleanSideRoute.loss sides.swap pair cleanB.private_ports t
    have room := (G.induce (B:Set V)).degree_lt_card_verts t
    change _<Fintype.card B at room
    rw [Fintype.card_coe] at room
    change G.degree v≤_+1 at drop
    omega
  have bmin := (degree_pair (G:=G) x y xy).elim (reg x (mem_filter.mp xp).1) (reg y (mem_filter.mp yp).1)
  apply mixed hc cap (by omega) minimum big (by change Fintype.card V≤5*k-5; omega) sides pair ne sc nonadj cleanB.private_ports conA conB
  · left; change B.card+1≤2*k ∧ A.card<2*(k-1)+(ports G A S).card
    constructor <;> omega
  · change max 1 (A.card-(2*k-4))+(B.card-(2*k-2))+3≤k
    omega

end Graph189SmallMixedPair
#print axioms Graph189SmallMixedPair.balanced
#print axioms Graph189SmallMixedPair.large_shallow
#print axioms Graph189SmallMixedPair.clean
