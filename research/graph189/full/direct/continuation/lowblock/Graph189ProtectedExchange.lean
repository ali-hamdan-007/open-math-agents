import Graph189ProtectedExteriorDegree
import Graph189R1Metric

open Finset SimpleGraph
namespace Graph189ProtectedExchange
open Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {a b : V}

/-- Inside an unmarked interval, a predecessor or successor of a mark must
be the first or last index of the interval. This also covers either tail. -/
private theorem overlap (A : Finset ℕ) (lo hi : ℕ)
    (unmarked : ∀ i ∈ Ico lo hi, i ∉ A)
    (internal : ∀ i ∈ A, 0 < i) :
    ((crossIndices A A) ∩ Ico lo hi).card ≤ 2 := by
  have subset : (crossIndices A A) ∩ Ico lo hi ⊆ {lo,hi-1} := by
    intro v hv
    obtain ⟨w,hv⟩ := mem_inter.mp hv
    obtain ⟨vlow,vhigh⟩ := mem_Ico.mp hv
    have shifts : v ∈ A.image (fun i => i-1) ∪ A.image (fun i => i+1) := by
      rcases mem_union.mp w with h | h
      · simpa only [inter_self] using h
      · exact False.elim ((mem_sdiff.mp h).2 (mem_sdiff.mp h).1)
    apply mem_insert.mpr
    rcases mem_union.mp shifts with left | right
    · obtain ⟨i,hiA,eq⟩ := mem_image.mp left
      have := internal i hiA
      have notInside : ¬(lo ≤ i ∧ i < hi) := fun h => unmarked i (mem_Ico.mpr h) hiA
      exact Or.inr (mem_singleton.mpr (by omega))
    · obtain ⟨i,hiA,eq⟩ := mem_image.mp right
      have notInside : ¬(lo ≤ i ∧ i < hi) := fun h => unmarked i (mem_Ico.mpr h) hiA
      exact Or.inl (by omega)
  exact (card_le_card subset).trans card_le_two

/-- A tight unmarked interval cannot be exchanged for a saturated exterior.
The claimed second-neighborhood witnesses have union size at least
|J|+2|A|−3, exceeding the even-distance budget when |A|≥3. -/
theorem terminal_contradiction (p : G.Walk a b) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {x y : V} (outx : x ∉ p.support) (outy : y ∉ p.support) (edge : G.Adj x y)
    (shared : contactPositions p y = contactPositions p x)
    {lo hi k : ℕ} (bound : hi ≤ p.support.length)
    (unmarked : ∀ i ∈ Ico lo hi, i ∉ contactPositions p x)
    (via : ∀ i ∈ Ico lo hi, ∃ w, G.Adj x w ∧ G.Adj (p.getVert i) w)
    (tight : hi-lo+(contactPositions p x).card = k+1)
    (three : 3 ≤ (contactPositions p x).card)
    (cap : G.distEven x ≤ k+1) : False := by
  classical
  let A := contactPositions p x
  let W := crossIndices A A
  let J := Ico lo hi
  obtain ⟨count,witness⟩ := protected_cross_indices p hp t longest outx outy edge
  rw [shared] at count witness
  change A.card+A.card ≤ W.card+1 at count
  have internal (i : ℕ) (h : i ∈ A) : 0 < i := by
    obtain ⟨hi,adj⟩ := (mem_contactPositions p x i).mp h
    exact (protected_contact_internal p hp t longest outx ⟨i,hi⟩ (by simpa [get_at] using adj)).1
  have lose : (W ∩ J).card ≤ 2 := overlap A lo hi unmarked internal
  have good (i : ℕ) (mem : i ∈ W ∪ J) : i < p.support.length ∧ G.dist x (p.getVert i)=2 := by
    rcases mem_union.mp mem with h|h
    · exact witness i h
    · obtain ⟨_,lt⟩ := mem_Ico.mp h
      have ri := lt.trans_le bound
      obtain ⟨w,hx,hw⟩ := via i h
      have different : x ≠ p.getVert i := fun e => outx (e ▸ p.getVert_mem_support i)
      have missing : ¬G.Adj x (p.getVert i) := fun adj =>
        unmarked i h ((mem_contactPositions p x i).mpr ⟨ri,adj.symm⟩)
      exact ⟨ri,two_step_metric different missing hx hw⟩
  let T := (W ∪ J).image p.getVert
  have inj : Set.InjOn p.getVert ((W ∪ J : Finset ℕ) : Set ℕ) := by
    intro i hi j hj eq
    have := (good _ hi).1
    have := (good _ hj).1
    have := p.length_support
    exact hp.getVert_injOn (by change i ≤ p.length; omega) (by change j ≤ p.length; omega) eq
  have absent : x ∉ T := by
    intro h
    obtain ⟨i,_,eq⟩ := mem_image.mp h
    exact outx (eq ▸ p.getVert_mem_support i)
  have sub : insert x T ⊆ univ.filter (fun v => Even (G.dist x v)) := by
    intro v h
    rcases mem_insert.mp h with rfl|mem
    · simp
    · obtain ⟨i,hi,rfl⟩ := mem_image.mp mem
      exact mem_filter.mpr ⟨mem_univ _,by rw [(good _ hi).2]; decide⟩
  have total := card_le_card sub
  change (insert x T).card ≤ G.distEven x at total
  rw [card_insert_of_notMem absent,show T.card=(W∪J).card from card_image_of_injOn inj] at total
  have union := card_union_add_card_inter W J
  have size : J.card=hi-lo := Nat.card_Ico _ _
  change hi-lo+A.card=k+1 at tight
  change 3 ≤ A.card at three
  omega

/-- Finite-position interface for a uniform marked set and a bounding
contact joined to every vertex of the exchanged interval. -/
theorem contradiction_of_uniform_marks (p : G.Walk a b) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {x y : V} (outx : x ∉ p.support) (outy : y ∉ p.support) (edge : G.Adj x y)
    (marks : Finset (Fin p.support.length))
    (mx : ∀ i : Fin p.support.length, G.Adj p.support[i.val] x ↔ i ∈ marks)
    (my : ∀ i : Fin p.support.length, G.Adj p.support[i.val] y ↔ i ∈ marks)
    {lo hi k : ℕ} (bound : hi ≤ p.support.length)
    (unmarked : ∀ i : Fin p.support.length, lo ≤ i.val → i.val < hi → i ∉ marks)
    (via : ∀ i : Fin p.support.length, lo ≤ i.val → i.val < hi →
      ∃ w, G.Adj x w ∧ G.Adj p.support[i.val] w)
    (tight : hi-lo+marks.card = k+1) (three : 3 ≤ marks.card)
    (cap : G.distEven x ≤ k+1) : False := by
  classical
  have eq {v : V} (mark : ∀ i : Fin p.support.length, G.Adj p.support[i.val] v ↔ i ∈ marks) :
      contactPositions p v=marks.image Fin.val := by
    ext i
    constructor
    · intro h
      obtain ⟨ri,edge⟩ := (mem_contactPositions p v i).mp h
      exact mem_image.mpr ⟨⟨i,ri⟩,(mark ⟨i,ri⟩).mp (by simpa [get_at] using edge),rfl⟩
    · intro h
      obtain ⟨j,hj,rfl⟩ := mem_image.mp h
      exact (mem_contactPositions p v j.val).mpr ⟨j.isLt,by simpa [get_at] using (mark j).mpr hj⟩
  have size : (contactPositions p x).card=marks.card := by
    rw [eq mx,card_image_of_injective _ Fin.val_injective]
  apply terminal_contradiction (lo:=lo) (hi:=hi) (k:=k) p hp t longest outx outy edge ((eq my).trans (eq mx).symm) bound _ _
    (by simpa [size] using tight) (by simpa [size] using three) cap
  · intro i hiA h
    obtain ⟨ri,edge⟩ := (mem_contactPositions p x i).mp h
    obtain ⟨left,right⟩ := mem_Ico.mp hiA
    exact (unmarked ⟨i,ri⟩ left right) ((mx ⟨i,ri⟩).mp (by simpa [get_at] using edge))
  · intro i hiA
    obtain ⟨left,right⟩ := mem_Ico.mp hiA
    let j : Fin p.support.length := ⟨i,right.trans_le bound⟩
    obtain ⟨w,hx,edge⟩ := via j left right
    exact ⟨w,hx,by simpa only [get_at] using edge⟩

end Graph189ProtectedExchange
#print axioms Graph189ProtectedExchange.terminal_contradiction

#print axioms Graph189ProtectedExchange.contradiction_of_uniform_marks
