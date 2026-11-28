import Graph189SmallMixedOrders
import Graph189PrivateSmallDegrees
import Graph189TwoConnectivity

open SimpleGraph Finset Graph189DeepCommonPair
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189SmallMixedPair
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

theorem nonadjacent_from_seven (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 7≤G.secondSmallestDegree) (small : G.secondSmallestDegree≤10) (minimum : 3≤G.minDegree)
    (big : 3*G.secondSmallestDegree+2<Fintype.card V) (floor : 4*G.secondSmallestDegree≤Fintype.card V+5)
    (sides : Graph189CutSides.CutSides G A B S) (sc : S.card≤G.vertexConnectivity)
    (pair : S={p,q}) (ne : p≠q) (nonadj : ¬G.Adj p q) (conA : (G.induce (A:Set V)).Connected)
    (conB : (G.induce (B:Set V)).Connected)
    (common : ∃u∈A,∀i∈S,G.Adj u i) (free : ∀x∈B,¬(G.Adj x p ∧ G.Adj x q))
    (chosen : (∀ C D T, Graph189CutSides.CutSides G C D T → T.card=2 → A.card≤C.card) ∨ B.card≤A.card) :
    ∃a b,∃r : G.Walk a b,r.IsHamiltonian := by
  classical
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have sz : S.card=2 := by simp [pair,ne]
  by_cases cleanB : Graph189CleanSideCounts.Clean G B p q
  · exact clean_from_seven hc cap large minimum big floor sides pair ne sc nonadj cleanB conA conB common
  have aSize := Graph189DirtySideOrder.order hc point sides.swap pair ne sc conB free cleanB
  by_cases hasDeep : ∃y,Deep G A S y
  · obtain ⟨y,deep⟩ := hasDeep
    obtain ⟨z,za,com⟩ := common
    exact balanced hc cap (by omega) minimum big sides pair ne sc nonadj free conA conB aSize
      (Graph189MixedDeepCounts.opposite hc point sides.swap sc sz deep za com)
  have shallow (x : V) (xa : x∈A) (high : G.secondSmallestDegree≤G.degree x) : ∃i∈S,G.Adj i x := by
    by_contra! miss
    exact hasDeep ⟨x,xa,high,miss⟩
  by_cases wide : 2*G.secondSmallestDegree≤B.card
  swap
  · exact balanced hc cap (by omega) minimum big sides pair ne sc nonadj free conA conB aSize (by omega)
  have missingCase {i j : V} (eq : S={i,j}) (diff : i≠j)
      (absent : ∀x∈A,G.Adj x j → G.Adj x i) (fb : ∀x∈B,¬(G.Adj x i ∧ G.Adj x j)) :
      ∃a b,∃r : G.Walk a b,r.IsHamiltonian := by
    obtain ⟨aSize,bSize⟩ := Graph189MissingPrivateMixed.sizes_above_moderate hc cap large minimum big sides sc eq diff
      conB shallow fb absent chosen
    have mp := Graph189DirtyRoutes.contacts hc point sides.swap pair sc big free
    have mq := Graph189DirtyRoutes.contacts hc point sides.swap (pair.trans (Finset.pair_comm _ _)) sc big (fun _ hx e => free _ hx e.symm)
    have dis : Disjoint (B.filter (G.Adj p)) (B.filter (G.Adj q)) := disjoint_left.mpr (by
      intro v vp vq
      exact free v (mem_filter.mp vp).1 ⟨(mem_filter.mp vp).2.symm,(mem_filter.mp vq).2.symm⟩)
    have inc : B.filter (G.Adj p)∪B.filter (G.Adj q)⊆ports G B S := by
      intro v hv
      rcases mem_union.mp hv with h|h
      · exact mem_filter.mpr ⟨(mem_filter.mp h).1,p,by simp [pair],(mem_filter.mp h).2⟩
      · exact mem_filter.mpr ⟨(mem_filter.mp h).1,q,by simp [pair],(mem_filter.mp h).2⟩
    have four := card_le_card inc
    rw [card_union_of_disjoint dis] at four
    have n := total sides sz
    exact mixed hc cap large minimum big (by omega) sides pair ne sc nonadj free conA conB (Or.inr ⟨by omega,by omega⟩) (by omega)
  by_cases qOnly : ∃x∈A,G.Adj x q ∧ ¬G.Adj x p
  swap
  · exact missingCase pair ne (fun x xa xq => by by_contra xp; exact qOnly ⟨x,xa,xq,xp⟩) free
  by_cases pOnly : ∃x∈A,G.Adj x p ∧ ¬G.Adj x q
  · exact large_shallow hc cap (by omega) small minimum big sides pair ne sc nonadj free conA conB shallow wide common pOnly qOnly
  exact missingCase (pair.trans (Finset.pair_comm _ _)) ne.symm
    (fun x xa xp => by by_contra xq; exact pOnly ⟨x,xa,xp,xq⟩) (fun x xb h => free x xb h.symm)

theorem nonadjacent_from_nine (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 9≤G.secondSmallestDegree) (small : G.secondSmallestDegree≤10) (minimum : 3≤G.minDegree)
    (big : 3*G.secondSmallestDegree+2<Fintype.card V) (floor : 4*G.secondSmallestDegree≤Fintype.card V+5)
    (sides : Graph189CutSides.CutSides G A B S) (sc : S.card≤G.vertexConnectivity)
    (pair : S={p,q}) (ne : p≠q) (nonadj : ¬G.Adj p q) (conA : (G.induce (A:Set V)).Connected)
    (conB : (G.induce (B:Set V)).Connected)
    (common : ∃u∈A,∀i∈S,G.Adj u i) (free : ∀x∈B,¬(G.Adj x p ∧ G.Adj x q))
    (chosen : (∀ C D T, Graph189CutSides.CutSides G C D T → T.card=2 → A.card≤C.card) ∨ B.card≤A.card) :
    ∃a b,∃r : G.Walk a b,r.IsHamiltonian :=
  nonadjacent_from_seven hc cap (by omega) small minimum big floor sides sc pair ne nonadj conA conB common free chosen

end Graph189SmallMixedPair
namespace Graph189TwoConnectivity
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- All orders and second-smallest degrees from ten at connectivity exactly two. -/
theorem of_ten (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 10≤G.secondSmallestDegree) (conn : G.vertexConnectivity=2) :
    ∃a b,∃r : G.Walk a b,r.IsHamiltonian := by
  classical
  by_cases eleven : 11≤G.secondSmallestDegree
  · exact of_eleven hc cap eleven conn
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  by_cases small : Fintype.card V+5<4*G.secondSmallestDegree
  · exact Graph189OnePortCover.below_four hc cap conn.ge (by omega) small
  by_cases minimum : 3≤G.minDegree
  swap
  · obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
    have low := Graph189CutSides.connectivity_le_degree (G:=G) z
    exact Graph189DegreeTwoOriginal.traceable hc cap conn.ge z (by omega) (by omega)
  obtain ⟨A,B,p,q,ne,sides,conA,conB,_,_,least⟩ :=
    Graph189TwoCutSelect.exists_connected_least_cut conn (by omega) minimum (by omega) point
  have size : ({p,q}:Finset V).card=2 := by simp [ne]
  have sc : ({p,q}:Finset V).card≤G.vertexConnectivity := by omega
  by_cases adj : G.Adj p q
  · exact Graph189AdjacentDeepPair.unrestricted hc cap sides sc rfl adj large
  let C (H : Finset V) := ∃x∈H,∀i∈({p,q}:Finset V),G.Adj x i
  have free {H : Finset V} (absent : ¬C H) (v : V) (vH : v∈H) : ¬(G.Adj v p ∧ G.Adj v q) := by
    rintro ⟨vp,vq⟩
    apply absent
    refine ⟨v,vH,fun i hi => ?_⟩
    rcases (show i=p ∨ i=q by simpa using hi) with rfl|rfl
    · exact vp
    · exact vq
  by_cases a : C A
  · by_cases b : C B
    · exact Graph189BothCommonPair.traceable hc cap sides sc rfl ne large a b
    · exact Graph189SmallMixedPair.nonadjacent_from_nine hc cap (by omega) (by omega) minimum (by omega) (by omega)
        sides sc rfl ne adj conA conB a (free b) (Or.inl least)
  by_cases b : C B
  · exact Graph189SmallMixedPair.nonadjacent_from_nine hc cap (by omega) (by omega) minimum (by omega) (by omega)
      sides.swap sc rfl ne adj conB conA b (free a) (Or.inr (least B A {p,q} sides.swap size))
  exact Graph189SmallPrivatePair.private_from_seven hc cap (by omega) (by omega) minimum (by omega)
    sides rfl ne sc (free a) (free b) conA conB

end Graph189TwoConnectivity
#print axioms Graph189SmallMixedPair.nonadjacent_from_nine
#print axioms Graph189TwoConnectivity.of_ten
#print axioms Graph189SmallMixedPair.nonadjacent_from_seven
