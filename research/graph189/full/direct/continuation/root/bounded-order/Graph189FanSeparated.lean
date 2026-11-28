import Graph189FanAssembly
import Graph189FanPrefix

open SimpleGraph
namespace Graph189FanCycle

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem neighbor_route_length {x : V} {T : List V} (nd : T.Nodup)
    (root : x ∈ T) (neighbors : ∀ v, G.Adj x v → v ∈ T) : G.degree x + 1 ≤ T.length := by
  have contained : insert x (G.neighborFinset x) ⊆ T.toFinset := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | h
    · exact List.mem_toFinset.mpr root
    exact List.mem_toFinset.mpr (neighbors v ((G.mem_neighborFinset _ _).mp h))
  have count := Finset.card_le_card contained
  rw [Finset.card_insert_of_notMem (by simp), G.card_neighborFinset_eq_degree,
    List.toFinset_card_of_nodup nd] at count
  exact count

/-- The two regions may share their boundary vertex. Using the trimmed
middle link as the anchor still supplies distinct terminals in each region. -/
theorem separated_routes (two : G.IsKConnected 2) {x y r s : V} (L R M : List V)
    (left : L.Nodup) (leftChain : L.IsChain G.Adj)
    (leftStart : L.head? = some x) (leftEnd : L.getLast? = some r) (leftChord : G.Adj x r)
    (leftNeighbors : ∀ v, G.Adj x v → v ∈ L)
    (right : R.Nodup) (rightChain : R.IsChain G.Adj)
    (rightStart : R.head? = some y) (rightEnd : R.getLast? = some s) (rightChord : G.Adj y s)
    (rightNeighbors : ∀ v, G.Adj y v → v ∈ R)
    (middle : Graph189FanLinkage.Link G (L.toFinset : Set V) (R.toFinset : Set V) M)
    (middleStart : M.head? = some r) (middleEnd : M.getLast? = some s)
    (meet : ∀ v ∈ L, v ∈ R → v = r) (degreeSum : 3 ≤ G.degree x + G.degree y) :
    ∃ a, ∃ cycle : G.Walk a a, cycle.IsCycle ∧ G.degree x + G.degree y ≤ cycle.length := by
  classical
  let A := L.toFinset
  let B := R.toFinset
  have wideA : 2 ≤ A.card := Finset.one_lt_card.mpr
    ⟨x,List.mem_toFinset.mpr (List.mem_of_mem_head? leftStart),
      r,List.mem_toFinset.mpr (List.mem_of_getLast? leftEnd),leftChord.ne⟩
  have wideB : 2 ≤ B.card := Finset.one_lt_card.mpr
    ⟨y,List.mem_toFinset.mpr (List.mem_of_mem_head? rightStart),
      s,List.mem_toFinset.mpr (List.mem_of_getLast? rightEnd),rightChord.ne⟩
  obtain ⟨P,Q,pLink,qLink,pq,starts,ends⟩ := Graph189FanLinkage.two_anchored_links two A B wideA wideB middle
  have assemble {U W : List V} (first : Graph189FanLinkage.Link G (A : Set V) (B : Set V) U)
      (second : Graph189FanLinkage.Link G (A : Set V) (B : Set V) W)
      (apart : U.Disjoint W) (secondStart : W.head? = some r)
      (finish : U.getLast? = some s ∨ W.getLast? = some s) :
      ∃ a, ∃ C : G.Walk a a, C.IsCycle ∧ G.degree x + G.degree y ≤ C.length := by
    obtain ⟨a,aA,firstStart⟩ := first.fromA
    obtain ⟨b,bB,firstEnd⟩ := first.toB
    obtain ⟨d,dB,secondEnd⟩ := second.toB
    have ar : a ≠ r := by
      intro eq
      subst a
      exact apart (List.mem_of_mem_head? firstStart) (List.mem_of_mem_head? secondStart)
    have bd : b ≠ d := by
      intro eq
      subst b
      exact apart (List.mem_of_getLast? firstEnd) (List.mem_of_getLast? secondEnd)
    obtain ⟨I,iNd,iCh,iStart,iEnd,iMem,xi,iNeighbors⟩ :=
      prefix_route left leftChain leftStart leftEnd leftChord (List.mem_toFinset.mp aA) ar
    obtain ⟨J,jNd,jCh,jStart,jEnd,jMem,yj,jNeighbors⟩ : ∃ J : List V,
        J.Nodup ∧ J.IsChain G.Adj ∧ J.head? = some b ∧ J.getLast? = some d ∧
        (∀ v ∈ J, v ∈ R) ∧ y ∈ J ∧ (∀ v, G.Adj y v → v ∈ J) := by
      rcases finish with bs | ds
      · have e : b = s := Option.some.inj (firstEnd.symm.trans bs)
        have ds : d ≠ s := fun h => bd (e.trans h.symm)
        obtain ⟨K,kNd,kCh,kStart,kEnd,kMem,yk,kNeighbors⟩ :=
          prefix_route right rightChain rightStart rightEnd rightChord (List.mem_toFinset.mp dB) ds
        refine ⟨K.reverse,List.nodup_reverse.mpr kNd,
          List.isChain_reverse.mpr (kCh.imp fun _ _ edge => edge.symm),?_,?_,?_,
          List.mem_reverse.mpr yk,?_⟩
        · simpa only [List.head?_reverse,← e] using kEnd
        · simpa only [List.getLast?_reverse] using kStart
        · exact fun v h => kMem v (List.mem_reverse.mp h)
        · exact fun v h => List.mem_reverse.mpr (kNeighbors v (rightNeighbors v h) h)
      · have e : d = s := Option.some.inj (secondEnd.symm.trans ds)
        have bs : b ≠ s := fun h => bd (h.trans e.symm)
        obtain ⟨K,kNd,kCh,kStart,kEnd,kMem,yk,kNeighbors⟩ :=
          prefix_route right rightChain rightStart rightEnd rightChord (List.mem_toFinset.mp bB) bs
        exact ⟨K,kNd,kCh,kStart,e.symm ▸ kEnd,kMem,yk,fun v h => kNeighbors v (rightNeighbors v h) h⟩
    have iIn : ∀ v ∈ I, v ∈ (A : Set V) := fun v h => List.mem_toFinset.mpr (iMem v h)
    have jIn : ∀ v ∈ J, v ∈ (B : Set V) := fun v h => List.mem_toFinset.mpr (jMem v h)
    have inter : ∀ v ∈ I, v ∈ J → v = d := by
      intro v vi vj
      have vr := meet v (iMem v vi) (jMem v vj)
      have vw : v ∈ W := vr.symm ▸ List.mem_of_mem_head? secondStart
      exact Option.some.inj ((second.onlyB v vw (jIn v vj)).symm.trans secondEnd)
    have iLen := neighbor_route_length iNd xi (fun v h => iNeighbors v (leftNeighbors v h) h)
    have jLen := neighbor_route_length jNd yj jNeighbors
    have uLen := List.length_pos_of_mem (List.mem_of_mem_head? firstStart)
    have wLen := List.length_pos_of_mem (List.mem_of_mem_head? secondStart)
    have long : 3 ≤ (I.length - 1) + (J.length - 1) + (U.length - 1) + (W.length - 1) := by omega
    obtain ⟨C,hC,_,len⟩ := Graph189FanLinkage.join_routes I J U W
      iNd iCh iStart iEnd iIn jNd jCh jStart jEnd jIn inter
      first second apart firstStart firstEnd secondStart secondEnd long
    exact ⟨a,C,hC,by omega⟩
  rw [middleStart] at starts
  rw [middleEnd] at ends
  rcases starts with pStarts | qStarts
  · exact assemble qLink pLink pq.symm pStarts (ends.elim Or.inr Or.inl)
  · exact assemble pLink qLink pq qStarts ends

end Graph189FanCycle

#print axioms Graph189FanCycle.separated_routes
