import Graph189BothCommonPair
import Graph189PrivatePairOriginal
import Graph189MixedDeepOriginal
import Graph189ShallowMixedPair
import Graph189MissingPrivateMixed
import Graph189TwoCutSelectJoint

open SimpleGraph Finset Graph189DeepCommonPair
namespace Graph189TwoConnectivity
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The two-cut argument with a common contact on exactly one side.
Choosing a globally smallest side makes the recut available in either orientation. -/
private theorem mixed (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 12≤G.secondSmallestDegree) {A B S : Finset V} {p q : V}
    (sides : Graph189CutSides.CutSides G A B S) (sc : S.card≤G.vertexConnectivity)
    (pair : S={p,q}) (ne : p≠q) (conB : (G.induce (B:Set V)).Connected)
    (common : ∃u∈A,∀i∈S,G.Adj u i) (free : ∀x∈B,¬(G.Adj x p ∧ G.Adj x q))
    (chosen : (∀ C D T, Graph189CutSides.CutSides G C D T → T.card=2 → A.card≤C.card) ∨ B.card≤A.card) :
    ∃a b,∃r : G.Walk a b,r.IsHamiltonian := by
  classical
  by_cases hasDeep : ∃y,Deep G A S y
  · obtain ⟨y,deep⟩ := hasDeep
    obtain ⟨z,za,com⟩ := common
    exact Graph189MixedDeepOriginal.traceable hc cap (by omega) sides.swap pair ne sc conB free deep za com
  have shallow (x : V) (xa : x∈A) (high : G.secondSmallestDegree≤G.degree x) : ∃i∈S,G.Adj i x := by
    by_contra! miss
    exact hasDeep ⟨x,xa,high,miss⟩
  by_cases qOnly : ∃x∈A,G.Adj x q ∧ ¬G.Adj x p
  swap
  · exact Graph189MissingPrivateMixed.traceable hc cap (by omega) sides sc pair ne conB shallow free
      (fun x xa xq => by by_contra xp; exact qOnly ⟨x,xa,xq,xp⟩) chosen
  by_cases pOnly : ∃x∈A,G.Adj x p ∧ ¬G.Adj x q
  · exact Graph189ShallowMixedPair.traceable hc cap (by omega) sides sc pair ne shallow free common pOnly qOnly
  exact Graph189MissingPrivateMixed.traceable hc cap (by omega) sides sc
    (pair.trans (Finset.pair_comm _ _)) ne.symm conB shallow (fun x xb h => free x xb h.symm)
    (fun x xa xp => by by_contra xq; exact pOnly ⟨x,xa,xp,xq⟩) chosen

/-- The original graph has a Hamiltonian path at connectivity two for all
orders and every second-smallest degree at least twelve. -/
theorem traceable (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 12≤G.secondSmallestDegree) (conn : G.vertexConnectivity=2) :
    ∃a b,∃r : G.Walk a b,r.IsHamiltonian := by
  classical
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
    · exact Graph189BothCommonPair.traceable hc cap sides sc rfl ne (by omega) a b
    · exact mixed hc cap large sides sc rfl ne conB a (free b) (Or.inl least)
  by_cases b : C B
  · exact mixed hc cap large sides.swap sc rfl ne conA b (free a)
      (Or.inr (least B A {p,q} sides.swap size))
  exact Graph189PrivatePairOriginal.traceable hc cap large sides rfl ne sc (free a) (free b) conA conB

end Graph189TwoConnectivity
#print axioms Graph189TwoConnectivity.traceable
