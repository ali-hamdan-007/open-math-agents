import Graph189CrossPort
open SimpleGraph Finset
namespace Graph189CrossPort
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- In a cut, when sources and targets are at most four steps apart, their
product of populations is bounded in terms of one population and the cut size.
The witnesses can be low vertices absent from both counted populations. -/
theorem cut_product (hc : G.Connected) (A B S : Finset V)
    (separate : Disjoint A B) (source : Disjoint A S) (target : Disjoint B S)
    (diam : ∀ x ∈ A, ∀ y ∈ B, G.dist x y ≤ 4)
    (cut : ∀ x ∈ A, ∀ y ∈ B, ∀ p : G.Walk x y, ∃ i ∈ S, i ∈ p.support)
    (wa : ∀ i ∈ S, ∃ w, G.Adj w i ∧ w ∉ A ∧ ∀ v ∈ A, ¬G.Adj w v)
    (wb : ∀ i ∈ S, ∃ w, G.Adj w i ∧ w ∉ B ∧ ∀ v ∈ B, ¬G.Adj w v)
    (k : ℕ) (cap : ∀ u, G.distEven u ≤ k+1) :
    A.card * B.card ≤ A.card * k + S.card * (k*k) := by
  classical
  let E (w : V) := (univ.filter (fun v => Even (G.dist w v))).erase w
  have quota (w : V) : (E w).card ≤ k := by
    have mem : w ∈ univ.filter (fun v => Even (G.dist w v)) := by simp
    have h := cap w
    change (univ.filter (fun v => Even (G.dist w v))).card ≤ k+1 at h
    unfold E
    rw [card_erase_of_mem mem]
    omega
  have pairQuota (i : V) (T : Finset V)
      (witness : ∃ w, G.Adj w i ∧ w ∉ T ∧ ∀ v ∈ T, ¬G.Adj w v) :
      (T.filter (fun v => G.dist i v = 1)).card ≤ k := by
    obtain ⟨w,hwi,hw,hn⟩ := witness
    apply (card_le_card (t := E w) ?_).trans (quota w)
    intro v hv
    obtain ⟨hm,hiv⟩ := mem_filter.mp hv
    have bound := hc.dist_triangle (u:=w) (v:=i) (w:=v)
    rw [dist_eq_one_iff_adj.mpr hwi, hiv] at bound
    have distinct : v ≠ w := fun e => hw (e ▸ hm)
    have nz : G.dist w v ≠ 0 := fun e => distinct (hc.dist_eq_zero_iff.mp e).symm
    have noedge : G.dist w v ≠ 1 := fun e => hn v hm (dist_eq_one_iff_adj.mp e)
    have hd : G.dist w v = 2 := by omega
    exact mem_erase.mpr ⟨distinct, mem_filter.mpr ⟨mem_univ _, by simp [hd]⟩⟩
  have through (x : V) (hx : x ∈ A) (y : V) (hy : y ∈ B) :
      ∃ i ∈ S, G.dist x y = G.dist x i + G.dist i y := by
    obtain ⟨p,hp⟩ := (hc x y).exists_walk_length_eq_dist
    obtain ⟨i,hi,hm⟩ := cut x hx y hy p
    refine ⟨i,hi,?_⟩
    have eq := congrArg SimpleGraph.Walk.length (Walk.take_spec p hm)
    rw [Walk.length_append] at eq
    have h₁ := G.dist_le (p.takeUntil i hm)
    have h₂ := G.dist_le (p.dropUntil i hm)
    have h₃ := hc.dist_triangle (u:=x) (v:=i) (w:=y)
    omega
  apply (pair_bound hc A B S separate source target diam through k cap).trans
  apply Nat.add_le_add_left
  calc _ ≤ ∑ _ ∈ S, k*k := by
          apply Finset.sum_le_sum
          intro i hi
          let U := A.filter (fun x => G.dist x i = 2)
          let W := B.filter (fun y => G.dist i y = 2)
          have dis : Disjoint U W :=
            separate.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
          have both : U.card+W.card ≤ k := by
            rw [← card_union_of_disjoint dis]
            apply (card_le_card (t := E i) ?_).trans (quota i)
            intro z hz
            rcases mem_union.mp hz with a | b
            · obtain ⟨hzA,h⟩ := mem_filter.mp a
              have hd : G.dist i z = 2 := dist_comm.trans h
              have hne : z ≠ i := fun e => disjoint_left.mp source (e ▸ hzA) hi
              exact mem_erase.mpr ⟨hne, mem_filter.mpr ⟨mem_univ _, by simp [hd]⟩⟩
            · obtain ⟨hzB,h⟩ := mem_filter.mp b
              have hne : z ≠ i := fun e => disjoint_left.mp target (e ▸ hzB) hi
              exact mem_erase.mpr ⟨hne, mem_filter.mpr ⟨mem_univ _, by simp [h]⟩⟩
          have a₁ : (A.filter (fun x => G.dist x i = 1)).card ≤ k := by
            simpa only [dist_comm (u:=i)] using pairQuota i A (wa i hi)
          have b₁ := pairQuota i B (wb i hi)
          calc _ ≤ k * W.card + U.card * k :=
                  Nat.add_le_add (Nat.mul_le_mul_right _ a₁) (Nat.mul_le_mul_left _ b₁)
               _ = (U.card + W.card)*k := by rw [Nat.add_mul, Nat.mul_comm k W.card, Nat.add_comm]
               _ ≤ k*k := Nat.mul_le_mul_right k both
       _ = _ := by simp
#print axioms cut_product
end Graph189CrossPort
