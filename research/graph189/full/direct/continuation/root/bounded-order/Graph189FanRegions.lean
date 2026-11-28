import Graph189FanLinkage

open SimpleGraph Finset
namespace Graph189FanCycle
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The oriented left and right end regions of a longest path, with the middle
path furnishing the two required terminals. The right region is reversed. -/
structure Regions (G : SimpleGraph V) (x y : V) where
  r : V
  s : V
  L : List V
  R : List V
  M : List V
  leftNodup : L.Nodup
  leftChain : L.IsChain G.Adj
  leftHead : L.head? = some x
  leftLast : L.getLast? = some r
  leftEdge : G.Adj x r
  leftNeighbors : ∀ v, G.Adj x v → v ∈ L
  rightNodup : R.Nodup
  rightChain : R.IsChain G.Adj
  rightHead : R.head? = some y
  rightLast : R.getLast? = some s
  rightEdge : G.Adj y s
  rightNeighbors : ∀ v, G.Adj y v → v ∈ R
  middle : Graph189FanLinkage.Link G (L.toFinset : Set V) R.toFinset M
  middleHead : M.head? = some r
  middleLast : M.getLast? = some s
  meet : ∀ v ∈ L, v ∈ R → v = r

private def seg (l : List V) (i j : ℕ) := (l.drop i).take (j+1-i)

omit [Fintype V] [DecidableEq V] in
private theorem mem_seg {l : List V} (x : V) {i j : ℕ} (ij : i≤j) (jl : j<l.length) {v : V} :
    v ∈ seg l i j ↔ ∃ t, i≤t ∧ t≤j ∧ l.getD t x = v := by
  unfold seg
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨u,ub,eq⟩
    have top := lt_of_lt_of_le ub (min_le_left _ _)
    refine ⟨i+u,by omega,by omega,?_⟩
    rw [List.getD_eq_getElem _ _ (by omega)]
    simpa only [List.getElem_drop] using eq
  · rintro ⟨t,ti,tj,eq⟩
    have pos : t-i < min (j+1-i) (l.drop i).length := by rw [List.length_drop]; omega
    refine ⟨t-i,pos,?_⟩
    rw [List.getElem_drop]
    simpa only [show i+(t-i)=t by omega,List.getD_eq_getElem _ _ (by omega : t<l.length)] using eq

omit [Fintype V] [DecidableEq V] in
private theorem seg_ends {l : List V} (x : V) {i j : ℕ} (ij : i≤j) (jl : j<l.length) :
    (seg l i j).head? = some (l.getD i x) ∧ (seg l i j).getLast? = some (l.getD j x) := by
  constructor
  · simp only [seg,List.head?_take,if_neg (by omega : j+1-i ≠ 0),List.head?_drop,
      List.getElem?_eq_getElem (by omega : i<l.length),List.getD_eq_getElem _ _ (by omega : i<l.length)]
  · rw [seg,List.getLast?_take,if_neg (by omega),List.getElem?_drop]
    have sum : i+(j+1-i-1)=j := by omega
    rw [sum,List.getElem?_eq_getElem jl,List.getD_eq_getElem _ _ jl]
    rfl

/-- Cut a simple path at the last neighbour of its first vertex and the first
neighbour of its last vertex. The cuts are allowed to coincide. -/
theorem regions_of_indices {l : List V} (nd : l.Nodup) (ch : l.IsChain G.Adj) (hn : l ≠ [])
    {x y : V} (start : l.head hn=x) (stop : l.getLast hn=y)
    {r s : ℕ} (rs : r≤s) (sl : s<l.length)
    (left : G.Adj x (l.getD r x)) (right : G.Adj y (l.getD s x))
    (before : ∀v, G.Adj x v → ∃i,i≤r ∧ l.getD i x=v)
    (after : ∀v, G.Adj y v → ∃ (t : ℕ), (s ≤ t) ∧ (t < l.length) ∧ l.getD t x = v) :
    Nonempty (Regions G x y) := by
  classical
  let last := l.length-1
  let A := seg l 0 r
  let B := (seg l s last).reverse
  let M := seg l r s
  have last_lt : last < l.length := by dsimp [last]; omega
  have slast : s ≤ last := by dsimp [last]; omega
  have ax := seg_ends x (Nat.zero_le r) (rs.trans_lt sl)
  have by' := seg_ends x slast last_lt
  have mids := seg_ends x rs sl
  have first : l.getD 0 x=x := by cases l with | nil => contradiction | cons a t => exact start
  have final : l.getD last x=y := by rw [List.getD_eq_getElem _ _ last_lt,←List.getLast_eq_getElem]; exact stop
  have inj (i j : ℕ) (hi : i<l.length) (hj : j<l.length) (eq : l.getD i x=l.getD j x) : i=j := by
    simp only [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj] at eq
    exact nd.getElem_inj_iff.mp eq
  have sub (i j : ℕ) : (seg l i j).Sublist l := (List.take_sublist _ _).trans (List.drop_sublist _ _)
  have chain (i j : ℕ) : (seg l i j).IsChain G.Adj := (ch.drop _).take _
  have am {v : V} : v∈A ↔ ∃ (t : ℕ), (0 ≤ t) ∧ (t ≤ r) ∧ l.getD t x = v := mem_seg x (Nat.zero_le _) (rs.trans_lt sl)
  have bm {v : V} : v∈B ↔ ∃ (t : ℕ), (s ≤ t) ∧ (t ≤ last) ∧ l.getD t x = v := by
    rw [show B=(seg l s last).reverse from rfl,List.mem_reverse,mem_seg x slast last_lt]
  have mm {v : V} : v∈M ↔ ∃ (t : ℕ), (r ≤ t) ∧ (t ≤ s) ∧ l.getD t x = v := mem_seg x rs sl
  have ra : l.getD r x ∈ A := am.mpr ⟨r,by omega,by omega,rfl⟩
  have sb : l.getD s x ∈ B := bm.mpr ⟨s,by omega,slast,rfl⟩
  have middle : Graph189FanLinkage.Link G (A.toFinset : Set V) B.toFinset M := by
    refine ⟨nd.sublist (sub _ _),chain _ _,⟨_,List.mem_toFinset.mpr ra,mids.1⟩,⟨_,List.mem_toFinset.mpr sb,mids.2⟩,?_,?_⟩
    · intro v vm va
      obtain ⟨i,ri,is,iv⟩ := mm.mp vm
      obtain ⟨j,_,jr,jv⟩ := am.mp (List.mem_toFinset.mp va)
      have eq := inj i j (by omega) (by omega) (iv.trans jv.symm)
      exact mids.1.trans (congrArg some ((show r=i by omega) ▸ iv))
    · intro v vm vb
      obtain ⟨i,ri,is,iv⟩ := mm.mp vm
      obtain ⟨j,sj,jl,jv⟩ := bm.mp (List.mem_toFinset.mp vb)
      have eq := inj i j (by omega) (by omega) (iv.trans jv.symm)
      exact mids.2.trans (congrArg some ((show s=i by omega) ▸ iv))
  refine ⟨⟨_,_,A,B,M,nd.sublist (sub _ _),chain _ _,ax.1.trans (congrArg some first),ax.2,left,?_,
    List.nodup_reverse.mpr (nd.sublist (sub _ _)),OMA.BondyK.chain_rev (chain _ _),?_,?_,right,?_,
    middle,mids.1,mids.2,?_⟩⟩
  · intro v e
    obtain ⟨i,ir,iv⟩ := before v e
    exact am.mpr ⟨i,by omega,ir,iv⟩
  · exact List.head?_reverse.trans (by'.2.trans (congrArg some final))
  · exact List.getLast?_reverse.trans by'.1
  · intro v e
    obtain ⟨i,si,il,iv⟩ := after v e
    exact bm.mpr ⟨i,si,by dsimp [last]; omega,iv⟩
  · intro v va vb
    obtain ⟨i,_,ir,iv⟩ := am.mp va
    obtain ⟨j,sj,jl,jv⟩ := bm.mp vb
    have eq := inj i j (by omega) (by omega) (iv.trans jv.symm)
    exact (show r=i by omega) ▸ iv.symm

end Graph189FanCycle
#print axioms Graph189FanCycle.regions_of_indices
