import Graph189LeastSideContacts
import Graph189ShallowCommonOrder
import Graph189MixedDeepCounts

open SimpleGraph Finset Graph189DenseSideRoute Graph189DeepCommonPair
namespace Graph189SmallMixedPair
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

private theorem join_common (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 7≤G.secondSmallestDegree) (minimum : 3≤G.minDegree) (upper : Fintype.card V≤5*G.secondSmallestDegree-5)
    (sides : Graph189CutSides.CutSides G A B S) (pair : S={p,q}) (ne : p≠q) (sc : S.card≤G.vertexConnectivity)
    (conB : (G.induce (B:Set V)).Connected) (two : 2≤B.card)
    (room : B.card<2*(G.secondSmallestDegree-1)+(ports G B S).card) (loss : ℕ)
    (left : ∀i∈S,Route G A i loss)
    (enough : loss+min (max 1 (B.card-(2*G.secondSmallestDegree-4))) (max 2 (B.card-(2*G.secondSmallestDegree-3)))+3≤G.secondSmallestDegree) :
    ∃a b,∃r : G.Walk a b,r.IsHamiltonian := by
  classical
  have sz : S.card=2 := by simp [pair,ne]
  have many := two_side_ports sides.swap sz sc two
  obtain ⟨x,xP,y,Q,hQ,inB,lB⟩ := Graph189SmallPrivatePair.common_from_marks_sharp sides.swap pair ne conB large minimum
    (ports G B S) (filter_subset _ _) many (fun v vb e => mem_filter.mpr ⟨vb,p,by simp [pair],e⟩) room
  obtain ⟨_,i,si,ix⟩ := mem_filter.mp xP
  obtain ⟨a,b,r,hr,len⟩ := Graph189TwoSoleNearest.join_routes sides si (left i si)
    (show Route G B i (min (max 1 (B.card-(2*G.secondSmallestDegree-4))) (max 2 (B.card-(2*G.secondSmallestDegree-3)))) from ⟨x,y,Q,hQ,ix,inB,lB⟩)
  rw [sz] at len
  exact Graph189ExteriorLeaf.traceable_of_near_degree hc cap large upper minimum r hr (by omega)

theorem both_shallow (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 7≤G.secondSmallestDegree) (minimum : 3≤G.minDegree) (big : 3*G.secondSmallestDegree+2<Fintype.card V)
    (sides : Graph189CutSides.CutSides G A B S) (pair : S={p,q}) (ne : p≠q) (sc : S.card≤G.vertexConnectivity)
    (conA : (G.induce (A:Set V)).Connected) (conB : (G.induce (B:Set V)).Connected) (twoB : 2≤B.card)
    (cA : ∃u∈A,∀i∈S,G.Adj u i) (cB : ∃u∈B,∀i∈S,G.Adj u i) (absent : ¬∃x,Deep G A S x) :
    ∃a b,∃r : G.Walk a b,r.IsHamiltonian := by
  classical
  have sz : S.card=2 := by simp [pair,ne]
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have shallow (x : V) (xa : x∈A) (high : G.secondSmallestDegree≤G.degree x) : ∃i∈S,G.Adj i x := by
    by_contra! miss
    exact absent ⟨x,xa,high,miss⟩
  by_cases high : ∃x∈A,G.secondSmallestDegree≤G.degree x
  swap
  · obtain ⟨x,_,d⟩ := Graph189ShallowCommonOrder.no_high sides sc sz high
    have h := minimum.trans (G.minDegree_le_degree x)
    omega
  rcases Graph189ShallowCommonOrder.profile hc sides sc sz point shallow high cA cB with impossible|⟨left,right,count⟩
  · omega
  change B.card≤G.secondSmallestDegree+1+(ports G B S).card at right
  change (ports G B S).card≤G.secondSmallestDegree at count
  have n := total sides sz
  apply join_common hc cap large minimum (by omega) sides pair ne sc conB twoB (by omega) 0 _ (by omega)
  intro i si
  obtain ⟨⟨x,xa,xi⟩,_⟩ := sides.contacts_of_minimum (fun T lt => Graph189CutSides.connected_after_smaller_deletion T (lt.trans_le sc)) si
  have mark : (A.filter (G.Adj i)).Nonempty := ⟨x,mem_filter.mpr ⟨xa,xi.symm⟩⟩
  rcases (show i=p ∨ i=q by simpa [pair] using si) with rfl|rfl
  · exact Graph189SmallPrivatePair.short_common sides pair ne conA large minimum mark (by omega)
  · exact Graph189SmallPrivatePair.short_common sides (pair.trans (Finset.pair_comm _ _)) ne.symm conA large minimum mark (by omega)

theorem both (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 7≤G.secondSmallestDegree) (minimum : 3≤G.minDegree) (big : 3*G.secondSmallestDegree+2<Fintype.card V)
    (sides : Graph189CutSides.CutSides G A B S) (pair : S={p,q}) (ne : p≠q) (sc : S.card≤G.vertexConnectivity)
    (conA : (G.induce (A:Set V)).Connected) (conB : (G.induce (B:Set V)).Connected) (twoA : 2≤A.card) (twoB : 2≤B.card)
    (least : ∀ C D T,Graph189CutSides.CutSides G C D T → T.card=2 → A.card≤C.card)
    (cA : ∃u∈A,∀i∈S,G.Adj u i) (cB : ∃u∈B,∀i∈S,G.Adj u i) :
    ∃a b,∃r : G.Walk a b,r.IsHamiltonian := by
  classical
  have sz : S.card=2 := by simp [pair,ne]
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  by_cases dA : ∃x,Deep G A S x
  swap
  · exact both_shallow hc cap large minimum big sides pair ne sc conA conB twoB cA cB dA
  by_cases dB : ∃x,Deep G B S x
  swap
  · exact both_shallow hc cap large minimum big sides.swap pair ne sc conB conA twoA cB cA dB
  obtain ⟨x,dx⟩ := dA
  obtain ⟨y,dy⟩ := dB
  obtain ⟨u,ua,cu⟩ := cA
  obtain ⟨v,vb,cv⟩ := cB
  let k := G.secondSmallestDegree
  have lo : 7≤k := large
  have b := Graph189MixedDeepCounts.opposite hc point sides.swap sc sz dx ua cu
  have a := Graph189MixedDeepCounts.opposite hc point sides sc sz dy vb cv
  have remA := Graph189MixedDeepCounts.nonports hc point sides.swap sc dy
  have remB := Graph189MixedDeepCounts.nonports hc point sides sc dx
  rw [sz] at remA remB
  change (A\ports G A S).card+2≤k+1 at remA
  change (B\ports G B S).card+2≤k+1 at remB
  have sumA := card_sdiff_add_card_eq_card (show ports G A S⊆A from filter_subset _ _)
  have sumB := card_sdiff_add_card_eq_card (show ports G B S⊆B from filter_subset _ _)
  change A.card+1≤2*k at a
  change B.card+1≤2*k at b
  have n := total sides sz
  have order := least B A S sides.swap sz
  have short : A.card+3≤2*k := by
    by_contra! long
    have rich := Graph189ShallowCommonOrder.rich_order hc sides (by omega) sz point ua cu vb cv
      (by change k≤(ports G A S).card+1; omega) (by change k≤(ports G B S).card+1; omega)
    change Fintype.card V≤3*k+4 at rich
    omega
  apply join_common hc cap large minimum (by change Fintype.card V≤5*k-5; omega) sides pair ne sc conB twoB
    (by change B.card<2*(k-1)+(ports G B S).card; omega) 1 _ (by
      change 1+min (max 1 (B.card-(2*k-4))) (max 2 (B.card-(2*k-3)))+3≤k
      omega)
  intro i si
  have run (j : V) (eq : S={i,j}) (diff : i≠j) : Route G A i 1 := by
    have two := least_two_marks sides eq diff sc twoA least
    obtain ⟨a,am,b,Q,hQ,inside,len⟩ := Graph189SmallPrivatePair.common_from_marks sides eq diff conA large minimum
      (A.filter (G.Adj i)) (filter_subset _ _) two (fun _ va e => mem_filter.mpr ⟨va,e⟩) (by change A.card<2*(k-1)+_; omega)
    refine ⟨a,b,Q,hQ,(mem_filter.mp am).2,inside,?_⟩
    change A.card≤Q.support.length+max 1 (A.card-(2*k-4)) at len
    omega
  rcases (show i=p ∨ i=q by simpa [pair] using si) with rfl|rfl
  · exact run q pair ne
  · exact run p (pair.trans (Finset.pair_comm _ _)) ne.symm

end Graph189SmallMixedPair
#print axioms Graph189SmallMixedPair.both_shallow
#print axioms Graph189SmallMixedPair.both
