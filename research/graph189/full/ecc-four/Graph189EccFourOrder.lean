import Graph189EccFour
import Graph189EccFourLayout

namespace Graph189EccFour
open SimpleGraph Graph189LowDegreeTwo Graph189DegreeTwoOuter
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The sharp order bound for a degree-two root of eccentricity four. -/
theorem order_le_three_sigma_sub_one (z : V) (h : G.Connected)
    (hz : G.degree z = 2)
    (hecc : ∀ x, G.dist z x ≤ 4) (hfar : ∃ f, G.dist z f = 4)
    (hs : 4 ≤ G.secondSmallestDegree)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree) :
    Fintype.card V ≤ 3*G.secondSmallestDegree-1 := by
  classical
  by_contra! hlarge
  let s := G.secondSmallestDegree
  change 3*s-1 < Fintype.card V at hlarge
  change 4 ≤ s at hs
  have hn : 2*s+3 < Fintype.card V := by omega
  obtain ⟨a,b,hab,hZ⟩ := Finset.card_eq_two.mp (show (G.neighborFinset z).card = 2 from hz)
  let B := Finset.univ.filter (fun x => G.dist z x = 2)
  let C := Finset.univ.filter (fun x => G.dist z x = 3)
  let D := Finset.univ.filter (fun x => G.dist z x = 4)
  obtain ⟨hab',hB,hD,hN,p,hp,q,hq,hpq,hap,hbq⟩ :=
    layout_of_order_large z a b h hZ hab hecc hfar (by omega) hσ hn
  change B.card = s-1 at hB
  change D.card = 1 at hD
  change B.card+C.card+D.card+3 = Fintype.card V at hN
  change p ∈ B at hp
  change q ∈ B at hq
  change ∀ x ∈ B, G.Adj a x ↔ x ≠ p at hap
  change ∀ x ∈ B, G.Adj b x ↔ x ≠ q at hbq
  obtain ⟨f,hf⟩ := Finset.card_eq_one.mp hD
  have hzf : G.dist z f = 4 := (Finset.mem_filter.mp (show f ∈ D by simp [hf])).2
  have hza : G.Adj z a := (G.mem_neighborFinset z a).mp (by simp [hZ])
  have hzb : G.Adj z b := (G.mem_neighborFinset z b).mp (by simp [hZ])
  have da := dist_eq_one_iff_adj.mpr hza
  have db := dist_eq_one_iff_adj.mpr hzb
  have dp : G.dist z p = 2 := (Finset.mem_filter.mp hp).2
  have dq : G.dist z q = 2 := (Finset.mem_filter.mp hq).2
  have high (x : V) (hx : x ≠ z) : s ≤ G.degree x :=
    (Graph189Bipartite.degree_pair x z hx).resolve_right (by rw [hz]; omega)
  have adj_layer {x y : V} (hxy : G.Adj x y) :
      G.dist z x ≤ G.dist z y+1 ∧ G.dist z y ≤ G.dist z x+1 := by
    have h₁ := h.dist_triangle (u := z) (v := y) (w := x)
    have h₂ := h.dist_triangle (u := z) (v := x) (w := y)
    rw [dist_eq_one_iff_adj.mpr hxy.symm] at h₁
    rw [dist_eq_one_iff_adj.mpr hxy] at h₂
    exact ⟨h₁,h₂⟩
  have layer_one {x : V} (hx : G.dist z x = 1) : x = a ∨ x = b := by
    simpa [hZ] using (G.mem_neighborFinset z x).mpr (dist_eq_one_iff_adj.mp hx)
  have dist_anchor_remote {u x : V} (hu : G.dist z u = 1) (hx : x ∈ C)
      {w : V} (huw : G.Adj u w) (hwx : G.Adj w x) : G.dist u x = 2 := by
    have dx : G.dist z x = 3 := (Finset.mem_filter.mp hx).2
    apply two_edges huw hwx
    · intro e
      rw [e,dx] at hu
      contradiction
    · intro had
      have hh := (adj_layer had).2
      omega
  let U := C.filter (fun x => G.dist b x = 2)
  let W := C.filter (fun x => G.dist a x = 2)
  let P := U \ W
  let Q := W \ U
  let T := U ∩ W
  have layerC : C = P ∪ Q ∪ T := by
    ext x
    by_cases hx : x ∈ C
    · obtain ⟨w,hw,hwx⟩ := split_three h (Finset.mem_filter.mp hx).2
      have hwB : w ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩
      have huv : G.dist b x = 2 ∨ G.dist a x = 2 := by
        by_cases hwp : w = p
        · exact Or.inl (dist_anchor_remote db hx ((hbq w hwB).2 (hwp.symm ▸ hpq)) hwx)
        · exact Or.inr (dist_anchor_remote da hx ((hap w hwB).2 hwp) hwx)
      simp only [P,Q,T,U,W,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff,
        Finset.mem_filter,hx,true_and,true_iff]
      tauto
    · simp [P,Q,T,U,W,hx]
  have hPQ : Disjoint P Q := by
    refine Finset.disjoint_left.mpr (fun x hx hy => ?_)
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  have hPT : Disjoint P T := by
    refine Finset.disjoint_left.mpr (fun x hx hy => ?_)
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_inter.mp hy).2
  have hQT : Disjoint Q T := by
    refine Finset.disjoint_left.mpr (fun x hx hy => ?_)
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_inter.mp hy).1
  have pC : P ⊆ C := fun x hx => (Finset.mem_filter.mp (Finset.mem_sdiff.mp hx).1).1
  have qC : Q ⊆ C := fun x hx => (Finset.mem_filter.mp (Finset.mem_sdiff.mp hx).1).1
  have a_p : G.dist p a = 2 := two_edges ((hbq p hp).2 hpq).symm hab'.symm
    (by intro e; rw [e,da] at dp; contradiction) (fun he => (hap p hp).1 he.symm rfl)
  have b_q : G.dist q b = 2 := two_edges ((hap q hq).2 hpq.symm).symm hab'
    (by intro e; rw [e,db] at dq; contradiction) (fun he => (hbq q hq).1 he.symm rfl)
  have vis_cap (u v : V) (hv : G.dist z v = 2) (hd : G.dist u v = 2) :
      (C.filter (fun x => G.dist u x = 2)).card + 1 ≤ s := by
    let M := C.filter (fun x => G.dist u x = 2)
    have hnot : v ∉ M := by simp [M,C,hv]
    have hsub : insert v M ⊆ Finset.univ.filter (fun x => G.dist u x = 2) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · simpa using hd
      · simpa using (Finset.mem_filter.mp hx).2
    have ht := (Finset.card_le_card hsub).trans (distance_two_cap s hσ u)
    rwa [Finset.card_insert_of_notMem hnot] at ht
  have hPU : P.card+T.card = U.card := Finset.card_sdiff_add_card_inter U W
  have hQW : Q.card+T.card = W.card := by
    simpa only [P,Q,T,Finset.inter_comm U W] using (Finset.card_sdiff_add_card_inter W U)
  have split_cap_P : P.card+T.card+1 ≤ s := by
    rw [hPU]
    exact vis_cap b q dq (by rw [G.dist_comm]; exact b_q)
  have split_cap_Q : Q.card+T.card+1 ≤ s := by
    rw [hQW]
    exact vis_cap a p dp (by rw [G.dist_comm]; exact a_p)
  have hcount : C.card = P.card+Q.card+T.card := by
    have h := Finset.disjoint_union_left.mpr ⟨hPT,hQT⟩
    rw [layerC,Finset.card_union_of_disjoint h,Finset.card_union_of_disjoint hPQ]
  let S := (B.erase p).erase q
  have hS : S.card = s-3 := by
    dsimp [S]
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hpq.symm,hq⟩),
      Finset.card_erase_of_mem hp,hB]
    omega
  obtain ⟨c,hc⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  have hcB := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).2
  have dc : G.dist z c = 2 := (Finset.mem_filter.mp hcB).2
  have hcp := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
  have hcq := (Finset.mem_erase.mp hc).1
  let E := insert a (insert b (S.erase c))
  have hE : E.card + 2 ≤ s := by
    change (insert a (insert b (S.erase c))).card + 2 ≤ s
    have hh := Finset.card_insert_le a (insert b (S.erase c))
    have hh' := Finset.card_insert_le b (S.erase c)
    rw [Finset.card_erase_of_mem hc,hS] at hh'
    omega
  have excl (u m x : V) (du : G.dist z u = 1) (hx : x ∈ C)
      (hout : G.dist u x ≠ 2) (miss : ∀ w ∈ B, G.Adj u w ↔ w ≠ m)
      (hcNe : c ≠ m) :
      G.Adj m x ∧ ¬ G.Adj c x ∧ ∀ w ∈ B, G.Adj w x → w = m := by
    have onlyw : ∀ w ∈ B, G.Adj w x → w = m := by
      intro w hw hwa
      by_contra hne
      exact hout (dist_anchor_remote du hx ((miss w hw).2 hne) hwa)
    obtain ⟨w,hw,had⟩ := split_three h (Finset.mem_filter.mp hx).2
    have he := onlyw w (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩) had
    exact ⟨he ▸ had,fun hc' => hcNe (onlyw c hcB hc'),onlyw⟩
  have ep (x : V) (hx : x ∈ P) :=
    excl a p x da (pC hx) (fun h =>
      (Finset.mem_sdiff.mp hx).2 (Finset.mem_filter.mpr ⟨pC hx,h⟩)) hap hcp
  have eq (x : V) (hx : x ∈ Q) :=
    excl b q x db (qC hx) (fun h =>
      (Finset.mem_sdiff.mp hx).2 (Finset.mem_filter.mpr ⟨qC hx,h⟩)) hbq hcq
  have nbr_excl (m x : V) (hx : x ∈ C) (he : ∀ w ∈ B, G.Adj w x → w = m) :
      G.neighborFinset x ⊆ insert m (insert f (T ∪ (P ∪ Q))) := by
    intro y hy
    have hxy := (G.mem_neighborFinset x y).mp hy
    have hd := (Finset.mem_filter.mp hx).2
    have hstep := adj_layer hxy
    have hy' : G.dist z y = 2 ∨ G.dist z y = 3 ∨ G.dist z y = 4 := by omega
    rcases hy' with h2 | h3 | h4
    · exact Finset.mem_insert.mpr (Or.inl (he y (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h2⟩) hxy.symm))
    · have he : y ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h3⟩
      rw [layerC] at he
      simpa only [Finset.mem_insert,Finset.mem_union] using
        (Or.inr (Or.inr ((Finset.mem_union.mp he).elim Or.inr Or.inl)) :
          y = m ∨ y = f ∨ y ∈ T ∨ y ∈ P ∪ Q)
    · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl
        (Finset.mem_singleton.mp (hf ▸ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h4⟩ : y ∈ D)))))
  have nbr_f : G.neighborFinset f ⊆ T ∪ (P ∪ Q) := by
    intro y hy
    have had := (G.mem_neighborFinset f y).mp hy
    have hstep := (adj_layer had).1
    have hu := hecc y
    by_cases h3 : G.dist z y = 3
    · have he : y ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h3⟩
      rw [layerC] at he
      exact Finset.mem_union.mpr ((Finset.mem_union.mp he).elim Or.inr Or.inl)
    · have h4 : G.dist z y = 4 := by omega
      have hey : y ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h4⟩
      exact ((G.ne_of_adj had) (Finset.mem_singleton.mp (hf ▸ hey)).symm).elim
  have nbr_c : G.neighborFinset c ⊆ insert p (insert q (E ∪ T)) := by
    intro y hy
    have had := (G.mem_neighborFinset c y).mp hy
    have hstep := adj_layer had
    have hd : G.dist z y = 1 ∨ G.dist z y = 2 ∨ G.dist z y = 3 := by omega
    rcases hd with h1 | h2 | h3
    · have he := layer_one h1
      simp [E]
      tauto
    · by_cases hyp : y = p
      · simp [hyp]
      by_cases hyq : y = q
      · simp [hyq]
      have he : y ∈ S.erase c := Finset.mem_erase.mpr ⟨(G.ne_of_adj had).symm,
        Finset.mem_erase.mpr ⟨hyq,Finset.mem_erase.mpr ⟨hyp,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,h2⟩⟩⟩⟩
      simp [E,he]
    · have he : y ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h3⟩
      rw [layerC] at he
      rcases Finset.mem_union.mp he with hpq' | ht
      · rcases Finset.mem_union.mp hpq' with hp' | hq'
        · exact ((ep y hp').2.1 had).elim
        · exact ((eq y hq').2.1 had).elim
      · simp [ht]
  have layer_not (x : V) (hd : G.dist z x ≠ 3) : x ∉ P ∧ x ∉ Q :=
    ⟨fun h => hd (Finset.mem_filter.mp (pC h)).2,fun h => hd (Finset.mem_filter.mp (qC h)).2⟩
  have nz := layer_not z (by simp)
  have na := layer_not a (by omega)
  have nb := layer_not b (by omega)
  have nf := layer_not f (by omega)
  have nc := layer_not c (by omega)
  have np := layer_not p (by omega)
  have nq := layer_not q (by omega)
  have nroot (x : V) (hh : 0 < G.dist z x) : x ≠ z := by
    intro e
    simp [e] at hh
  have nefar (x : V) (hh : G.dist z x ≠ 4) : x ≠ f := by
    intro e
    exact hh (e ▸ hzf)
  have zdist (x : V) (hh : G.dist z x = 2) : G.dist x z = 2 :=
    by rw [G.dist_comm]; exact hh
  have sP (x : V) (hx : x ∈ P) : G.Adj p x ∧ ¬ G.Adj c x ∧ ¬ G.Adj q x :=
    ⟨(ep x hx).1,(ep x hx).2.1,fun ha => hpq.symm ((ep x hx).2.2 q hq ha)⟩
  have sQ (x : V) (hx : x ∈ Q) : G.Adj q x ∧ ¬ G.Adj c x ∧ ¬ G.Adj p x :=
    ⟨(eq x hx).1,(eq x hx).2.1,fun ha => hpq ((eq x hx).2.2 p hp ha)⟩
  exact large_remote_layer_impossible s hs (distance_two_cap s hσ) P Q T E
    split_cap_P split_cap_Q (by omega) hE hPQ hPT hQT z a b c p q f
    nz.1 nz.2 na.2 nb.1 nf.1 nf.2 nc.1 nc.2 np.2 nq.1
    (nroot p (by omega)) (nroot q (by omega)) (nroot a (by omega)) (nroot b (by omega))
    (nroot f (by omega)) (nefar a (by omega)).symm (nefar b (by omega)).symm
    hcp hcq (nefar p (by omega)) (nefar q (by omega))
    (zdist c dc) (zdist p dp) (zdist q dq) a_p b_q
    ⟨b,((hbq c hcB).2 hcq).symm,(hbq p hp).2 hpq⟩
    ⟨a,((hap c hcB).2 hcp).symm,(hap q hq).2 hpq.symm⟩
    (fun had => by have hh := (adj_layer had).2; omega)
    (fun had => by have hh := (adj_layer had).2; omega)
    sP sQ (high c (nroot c (by omega))) nbr_c
    (fun x hx => high x (nroot x (by have hh := (Finset.mem_filter.mp (pC hx)).2; omega)))
    (fun x hx => high x (nroot x (by have hh := (Finset.mem_filter.mp (qC hx)).2; omega)))
    (fun x hx => nbr_excl p x (pC hx) (ep x hx).2.2)
    (fun x hx => nbr_excl q x (qC hx) (eq x hx).2.2)
    (high f (nroot f (by omega))) nbr_f

#print axioms order_le_three_sigma_sub_one
end Graph189EccFour
