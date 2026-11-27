import Graph189Order14Layout

namespace Graph189Order14Relabel
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
  {G : SimpleGraph V}

/-- The four blocks are the misses of the first anchor, the misses of the
second anchor, the shared middle vertices, and the remote vertices. -/
noncomputable def blocks (G : SimpleGraph V) [DecidableRel G.Adj] (z a b : V) :
    Finset V × Finset V × Finset V × Finset V :=
  let W := Finset.univ.filter (fun v => G.dist z v = 2)
  (W.filter (fun v => ¬ G.Adj a v), W.filter (fun v => ¬ G.Adj b v),
    W.filter (fun v => G.Adj a v ∧ G.Adj b v),
    Finset.univ.filter (fun v => G.dist z v = 3))

omit [Nontrivial V] in
/-- Ordering each finite block arbitrarily produces one ordered, duplicate-free
listing, with the two missed sets in consecutive initial middle blocks. -/
theorem orderedList [DecidableRel G.Adj] (h : G.Connected) (hd : G.diam ≤ 3)
    (z a b : V) (hne : a ≠ b) (hz : G.neighborFinset z = {a,b}) :
    let ⟨A,B,S,R⟩ := blocks G z a b
    let L := [z,a,b] ++ A.toList ++ B.toList ++ S.toList ++ R.toList
    L.Nodup ∧ ∀ x : V, x ∈ L := by
  classical
  have := h.nonempty
  let W := Finset.univ.filter (fun v => G.dist z v = 2)
  let A := W.filter (fun v => ¬ G.Adj a v)
  let B := W.filter (fun v => ¬ G.Adj b v)
  let S := W.filter (fun v => G.Adj a v ∧ G.Adj b v)
  let R := Finset.univ.filter (fun v => G.dist z v = 3)
  let L := [z,a,b] ++ A.toList ++ B.toList ++ S.toList ++ R.toList
  change L.Nodup ∧ ∀ x, x ∈ L
  have az : G.Adj z a := (G.mem_neighborFinset z a).mp (by simp [hz])
  have bz : G.Adj z b := (G.mem_neighborFinset z b).mp (by simp [hz])
  have da := dist_eq_one_iff_adj.mpr az
  have db := dist_eq_one_iff_adj.mpr bz
  have reached (x : V) (hx : G.dist z x = 2) : G.Adj a x ∨ G.Adj b x := by
    obtain ⟨u,hu,hux⟩ := Graph189LowDegreeTwo.split_two h hx
    have hm : u = a ∨ u = b := by simpa [hz] using (G.mem_neighborFinset z u).mpr hu
    rcases hm with e | e
    · exact Or.inl (e ▸ hux)
    · exact Or.inr (e ▸ hux)
  constructor
  · simp [L,List.nodup_append,Finset.nodup_toList,A,B,S,R,W,da,db,G.ne_of_adj az,G.ne_of_adj bz,hne]
    grind
  · intro x
    have hle := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp h) (u := z) (v := x)).trans hd
    have casesDist : G.dist z x = 0 ∨ G.dist z x = 1 ∨ G.dist z x = 2 ∨ G.dist z x = 3 := by omega
    rcases casesDist with h0 | h1 | h2 | h3
    · have e := ((h.preconnected z x).dist_eq_zero_iff.mp h0).symm
      simp [L,e]
    · have he : x = a ∨ x = b := by
        simpa [hz] using (G.mem_neighborFinset z x).mpr (dist_eq_one_iff_adj.mp h1)
      rcases he with e | e <;> simp [L,e]
    · by_cases ha : G.Adj a x <;> by_cases hb : G.Adj b x <;>
        simp [L,A,B,S,W,h2,ha,hb]
    · simp [L,R,h3]


omit [Nontrivial V] in
/-- Turn the ordered partition into concrete labels from zero to thirteen. -/
theorem labels [DecidableRel G.Adj] (h : G.Connected) (hd : G.diam ≤ 3)
    (hn : Fintype.card V = 14) (z a b : V) (hne : a ≠ b)
    (hz : G.neighborFinset z = {a,b}) :
    let ⟨A,B,S,R⟩ := blocks G z a b
    let L := [z,a,b] ++ A.toList ++ B.toList ++ S.toList ++ R.toList
    ∃ hL : L.length = 14, ∃ e : Fin 14 ≃ V,
      ∀ i : Fin 14, e i = L.get (Fin.cast hL.symm i) := by
  have hl := orderedList h hd z a b hne hz
  rcases he : blocks G z a b with ⟨A,B,S,R⟩
  simp only [he] at hl ⊢
  let L := [z,a,b] ++ A.toList ++ B.toList ++ S.toList ++ R.toList
  change ∃ hL : L.length = 14, ∃ e : Fin 14 ≃ V,
    ∀ i : Fin 14, e i = L.get (Fin.cast hL.symm i)
  obtain ⟨hnd,hall⟩ : L.Nodup ∧ ∀ x, x ∈ L := hl
  have hu : L.toFinset = Finset.univ := by ext x; simp [hall]
  have hL : L.length = 14 := by rw [← List.toFinset_card_of_nodup hnd,hu,Finset.card_univ,hn]
  let e₀ (i : Fin 14) := L.get (Fin.cast hL.symm i)
  have hbij : Function.Bijective e₀ := by
    constructor
    · intro i j hij
      apply Fin.ext
      exact hnd.getElem_inj_iff.mp hij
    · intro x
      obtain ⟨i,hi⟩ := List.get_of_mem (hall x)
      exact ⟨Fin.cast hL i, by simpa [e₀] using hi⟩
  exact ⟨hL,Equiv.ofBijective e₀ hbij, fun _ => rfl⟩

/-- The two missed-set block sizes in the ordered layout satisfy the checked
order-fourteen shape alternatives. -/
theorem blockShapes [DecidableRel G.Adj] (h : G.Connected) (hd : G.diam ≤ 3)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree)
    (hs : G.secondSmallestDegree = 5) (hn : Fintype.card V = 14)
    (z a b : V) (hne : a ≠ b) (hz : G.neighborFinset z = {a,b}) :
    let ⟨A,B,_,_⟩ := blocks G z a b
    let W := Finset.univ.filter (fun v => G.dist z v = 2)
    (W.card = 4 ∧ G.Adj a b ∧ A.card = 1 ∧ B.card = 1) ∨
      (W.card = 5 ∧ ¬ G.Adj a b ∧ A.card = 1 ∧ B.card = 1) ∨
      (W.card = 5 ∧ G.Adj a b ∧ 1 ≤ A.card ∧ A.card ≤ 2 ∧ 1 ≤ B.card ∧ B.card ≤ 2) :=
  Graph189Order14Layout.shapes h hd hσ hs hn z a b hne hz


private theorem memBlock {α : Type*} (front block back : List α) {n : ℕ}
    (hn : n < (front ++ block ++ back).length) (hl : front.length ≤ n)
    (hh : n < front.length + block.length) :
    (front ++ block ++ back)[n] ∈ block := by
  rw [List.getElem_append_left (by simpa using hh), List.getElem_append_right hl]
  exact List.getElem_mem _

omit [Nontrivial V] in
/-- The labels in each half-open interval belong to the corresponding finite block. -/
theorem positions [DecidableRel G.Adj] (h : G.Connected) (hd : G.diam ≤ 3)
    (hn : Fintype.card V = 14) (z a b : V) (hne : a ≠ b)
    (hz : G.neighborFinset z = {a,b}) :
    let ⟨A,B,S,R⟩ := blocks G z a b
    ∃ e : Fin 14 ≃ V, e 0 = z ∧ e 1 = a ∧ e 2 = b ∧
      (∀ i : Fin 14, 3 ≤ i.val → i.val < 3 + A.card → e i ∈ A) ∧
      (∀ i : Fin 14, 3 + A.card ≤ i.val → i.val < 3 + A.card + B.card → e i ∈ B) ∧
      (∀ i : Fin 14, 3 + A.card + B.card ≤ i.val →
        i.val < 3 + A.card + B.card + S.card → e i ∈ S) ∧
      (∀ i : Fin 14, 3 + A.card + B.card + S.card ≤ i.val → e i ∈ R) ∧
      3 + A.card + B.card + S.card + R.card = 14 := by
  have he := labels h hd hn z a b hne hz
  generalize hb : blocks G z a b = bs at he ⊢
  rcases bs with ⟨A,B,S,R⟩
  dsimp at he ⊢
  let base : List V := [z,a,b]
  let L := base ++ A.toList ++ B.toList ++ S.toList ++ R.toList
  obtain ⟨hl,e,he⟩ : ∃ hl : L.length = 14, ∃ e : Fin 14 ≃ V,
      ∀ i : Fin 14, e i = L.get (Fin.cast hl.symm i) := he
  have hlen : 3 + A.card + B.card + S.card + R.card = 14 := by
    simp [L,base] at hl; omega
  have get (i : Fin 14) : e i = L[i.val]'(by rw [hl]; exact i.isLt) := he i
  refine ⟨e, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hlen⟩
  · rw [get]; simp [L,base]
  · rw [get]; simp [L,base]
  · rw [get]; simp [L,base]
  · intro i h₁ h₂
    apply Finset.mem_toList.mp
    rw [get]
    have hm := memBlock base A.toList (B.toList ++ S.toList ++ R.toList)
      (n := i.val) (by simpa [List.append_assoc,L] using (show i.val < L.length from by rw [hl]; exact i.isLt))
      (by simp [base]; omega) (by simp [base]; omega)
    simpa [L,List.append_assoc] using hm
  · intro i h₁ h₂
    apply Finset.mem_toList.mp
    rw [get]
    have hm := memBlock (base ++ A.toList) B.toList (S.toList ++ R.toList)
      (n := i.val) (by simpa [List.append_assoc,L] using (show i.val < L.length from by rw [hl]; exact i.isLt))
      (by simp [base]; omega) (by simp [base]; omega)
    simpa [L,List.append_assoc] using hm
  · intro i h₁ h₂
    apply Finset.mem_toList.mp
    rw [get]
    exact memBlock (base ++ A.toList ++ B.toList) S.toList R.toList
      (by change i.val < L.length; simpa only [hl] using i.isLt) (by simp [base]; omega) (by simp [base]; omega)
  · intro i h₁
    apply Finset.mem_toList.mp
    rw [get]
    have heq : i.val < 3 + A.card + B.card + S.card + R.card := by rw [hlen]; exact i.isLt
    have hm := memBlock (base ++ A.toList ++ B.toList ++ S.toList) R.toList []
      (n := i.val) (by
        have hLi : i.val < L.length := by simpa only [hl] using i.isLt
        simpa [L] using hLi)
      (by simp [base]; omega) (by simp [base]; omega)
    simpa [L] using hm


omit [Nontrivial V] in
theorem middleCard [DecidableRel G.Adj] (h : G.Connected)
    (z a b : V) (hz : G.neighborFinset z = {a,b}) :
    let ⟨A,B,S,_⟩ := blocks G z a b
    (Finset.univ.filter (fun v => G.dist z v = 2)).card = A.card + B.card + S.card := by
  classical
  let W := Finset.univ.filter (fun v => G.dist z v = 2)
  let A := W.filter (fun v => ¬ G.Adj a v)
  let B := W.filter (fun v => ¬ G.Adj b v)
  let S := W.filter (fun v => G.Adj a v ∧ G.Adj b v)
  change W.card = A.card + B.card + S.card
  have reaches (x : V) (hx : x ∈ W) : G.Adj a x ∨ G.Adj b x := by
    obtain ⟨u,hu,hux⟩ := Graph189LowDegreeTwo.split_two h (Finset.mem_filter.mp hx).2
    have hm : u = a ∨ u = b := by simpa [hz] using (G.mem_neighborFinset z u).mpr hu
    rcases hm with e | e
    · exact Or.inl (e ▸ hux)
    · exact Or.inr (e ▸ hux)
  have hW : W = A ∪ B ∪ S := by
    ext x
    by_cases ha : G.Adj a x <;> by_cases hb : G.Adj b x <;> simp [A,B,S,ha,hb]
  have hAB : Disjoint A B := by
    refine Finset.disjoint_left.mpr ?_
    intro x ha hb
    exact (reaches x (Finset.mem_filter.mp ha).1).elim
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  have hAS : Disjoint (A ∪ B) S := by
    refine Finset.disjoint_left.mpr ?_
    intro x hm hs
    rcases Finset.mem_union.mp hm with ha | hb
    · exact (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hs).2.1
    · exact (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp hs).2.2
  rw [hW,Finset.card_union_of_disjoint hAS,Finset.card_union_of_disjoint hAB]

#print axioms orderedList
#print axioms labels
#print axioms blockShapes
#print axioms positions
#print axioms middleCard
end Graph189Order14Relabel
