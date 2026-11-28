import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Unbundled.Basic

namespace Graph189ThirdLayer

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V]

noncomputable def layer (G : SimpleGraph V) (z : V) (n : ℕ) : Finset V := by
  classical
  exact univ.filter (fun v => G.dist z v = n)

@[simp] theorem in_layer {G : SimpleGraph V} {z y : V} {n : ℕ} :
    y ∈ layer G z n ↔ G.dist z y = n := by classical simp [layer]

private theorem minimal_cover (A B : Finset V) (R : V → V → Prop)
    (hc : ∀ b ∈ B, ∃ a ∈ A, R a b) :
    ∃ T ⊆ A, (∀ b ∈ B, ∃ a ∈ T, R a b) ∧
      ∀ a ∈ T, ∃ b ∈ B, R a b ∧ ∀ a' ∈ T, a' ≠ a → ¬ R a' b := by
  classical
  let covers (S : Finset V) := ∀ b ∈ B, ∃ a ∈ S, R a b
  let family := A.powerset.filter covers
  have ha : A ∈ family := mem_filter.mpr ⟨mem_powerset.mpr (fun _ h => h), hc⟩
  obtain ⟨T,hT,hmin⟩ := family.exists_min_image Finset.card ⟨A,ha⟩
  obtain ⟨hsub,hcovers⟩ := mem_filter.mp hT
  have hsub' := mem_powerset.mp hsub
  refine ⟨T,hsub',hcovers,?_⟩
  intro a haT
  have missing : ¬ covers (T.erase a) := by
    intro h
    have hs : T.erase a ∈ family := mem_filter.mpr
      ⟨mem_powerset.mpr ((erase_subset a T).trans hsub'),h⟩
    exact (not_le_of_gt (card_erase_lt_of_mem haT)) (hmin _ hs)
  change ¬ (∀ b ∈ B, ∃ a' ∈ T.erase a, R a' b) at missing
  push Not at missing
  obtain ⟨b,hb,hprivate⟩ := missing
  obtain ⟨x,hx,hxb⟩ := hcovers b hb
  have hxa : x = a := by
    by_contra h
    exact hprivate x (mem_erase.mpr ⟨h,hx⟩) hxb
  exact ⟨b,hb,hxa ▸ hxb,fun a' ha' hdiff => hprivate a' (mem_erase.mpr ⟨hdiff,ha'⟩)⟩

omit [Fintype V] in
private theorem predecessor {G : SimpleGraph V} {z y : V} {d : ℕ}
    (h : G.dist z y = d+1) : ∃ p, G.dist z p = d ∧ G.Adj p y := by
  have hr : G.dist y z = d+1 := by rwa [dist_comm]
  have hpos : G.Reachable y z := Reachable.of_dist_ne_zero (by omega)
  obtain ⟨walk,hlen⟩ := hpos.exists_walk_length_eq_dist
  cases walk with
  | nil => simp at h
  | cons hy tail =>
    rename_i p
    have hlen' : tail.length = d := by rw [Walk.length_cons,hr] at hlen; omega
    have hle : G.dist z p ≤ d := by rw [dist_comm]; exact hlen' ▸ G.dist_le tail
    have ht := hy.diff_dist_adj (u := z)
    exact ⟨p,by omega,hy.symm⟩

omit [Fintype V] in
private theorem dist_two {G : SimpleGraph V} {x y q : V}
    (hne : x ≠ y) (hna : ¬G.Adj x y) (h1 : G.Adj x q) (h2 : G.Adj q y) :
    G.dist x y = 2 := by
  let w : G.Walk x y := .cons h1 (.cons h2 .nil)
  have hlo := w.reachable.one_lt_dist_of_ne_of_not_adj hne hna
  have hhi : G.dist x y ≤ 2 := G.dist_le w
  omega

/-- A minimal cover of the second layer produces a family of t anchors. Its
third-layer neighborhoods have at least t−1 disjoint extra witnesses each. -/
theorem third_layer_product (G : SimpleGraph V) (z : V) (k : ℕ)
    (cap : ∀ a ∈ layer G z 1, (layer G a 2).card ≤ k) :
    ∃ t ≤ (layer G z 1).card, t ≤ k+1 ∧
      (layer G z 3).card ≤ t * (k+1-t) := by
  classical
  have coverB : ∀ b ∈ layer G z 2, ∃ a ∈ layer G z 1, G.Adj a b := by
    intro b hb
    obtain ⟨a,ha,hab⟩ := predecessor (d := 1) (in_layer.mp hb)
    exact ⟨a,in_layer.mpr ha,hab⟩
  obtain ⟨T,hTA,hTc,hTp⟩ := minimal_cover (layer G z 1) (layer G z 2) G.Adj coverB
  let port (a : V) : V := if h : a ∈ T then (hTp a h).choose else z
  have hp (a : V) (h : a ∈ T) : G.dist z (port a) = 2 ∧ G.Adj a (port a) ∧
      ∀ a' ∈ T, a' ≠ a → ¬G.Adj a' (port a) := by
    simpa [port,h] using (hTp a h).choose_spec
  have hA (a : V) (h : a ∈ T) : G.dist z a = 1 := in_layer.mp (hTA h)
  let W (a : V) := (layer G z 3).filter (fun c => G.dist a c = 2)
  have cov : layer G z 3 ⊆ T.biUnion W := by
    intro c hc
    have hc' := in_layer.mp hc
    obtain ⟨b,hb,hbc⟩ := predecessor (d := 2) hc'
    obtain ⟨a,ha,hab⟩ := hTc b (in_layer.mpr hb)
    have hd := hA a ha
    have hne : a ≠ c := by rintro rfl; omega
    have hn : ¬G.Adj a c := by intro he; have := he.diff_dist_adj (u := z); omega
    exact mem_biUnion.mpr ⟨a,ha,mem_filter.mpr ⟨hc,dist_two hne hn hab hbc⟩⟩
  have row (a : V) (ha : a ∈ T) : (W a).card + T.card ≤ k+1 := by
    let f (j : V) := if G.Adj a j then port j else j
    have hzj (j : V) (hj : j ∈ T) : G.dist z (f j) ≤ 2 := by
      by_cases h : G.Adj a j <;> simp [f,h,(hp j hj).1,hA j hj]
    have finj : Set.InjOn f ↑(T.erase a) := by
      intro j hj l hl hEq
      obtain ⟨_,hjT⟩ := mem_erase.mp hj
      obtain ⟨_,hlT⟩ := mem_erase.mp hl
      by_cases hjA : G.Adj a j <;> by_cases hlA : G.Adj a l <;> simp [f,hjA,hlA] at hEq
      · by_contra hne
        exact (hp l hlT).2.2 j hjT hne (hEq ▸ (hp j hjT).2.1)
      · have h1 := (hp j hjT).1; have h2 := hA l hlT; rw [hEq] at h1; omega
      · have h1 := (hp l hlT).1; have h2 := hA j hjT; rw [hEq] at h2; omega
      · exact hEq
    let E := (T.erase a).image f
    have heq : E.card = (T.erase a).card := card_image_of_injOn finj
    have hdis : Disjoint (W a) E := by
      apply Finset.disjoint_left.mpr
      intro x hx hw
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hw
      have h1 := in_layer.mp (mem_filter.mp hx).1
      have h2 := hzj j (mem_erase.mp hj).2
      omega
    have incl : W a ∪ E ⊆ layer G a 2 := by
      intro x hx
      rcases mem_union.mp hx with hw|he
      · exact in_layer.mpr (mem_filter.mp hw).2
      · obtain ⟨j,hj,rfl⟩ := mem_image.mp he
        obtain ⟨hne,hj⟩ := mem_erase.mp hj
        apply in_layer.mpr
        by_cases haj : G.Adj a j
        · simp only [f,if_pos haj]
          have hza := hA a ha
          have hzj' := (hp j hj).1
          apply dist_two _ ((hp j hj).2.2 a ha hne.symm) haj (hp j hj).2.1
          rintro heq'; rw [heq'] at hza; omega
        · simp only [f,if_neg haj]
          exact dist_two hne.symm haj (dist_eq_one_iff_adj.mp (hA a ha)).symm
            (dist_eq_one_iff_adj.mp (hA j hj))
    have hcount := (card_le_card incl).trans (cap a (hTA ha))
    rw [card_union_of_disjoint hdis,heq] at hcount
    have he := card_erase_add_one ha
    omega
  have hsize : T.card ≤ k+1 := by
    rcases T.eq_empty_or_nonempty with he|⟨a,ha⟩
    · simp [he]
    · have := row a ha; omega
  refine ⟨T.card,card_le_card hTA,hsize,?_⟩
  calc (layer G z 3).card ≤ (T.biUnion W).card := card_le_card cov
       _ ≤ ∑ a ∈ T, (W a).card := card_biUnion_le
       _ ≤ ∑ _a ∈ T, (k+1-T.card) := sum_le_sum (fun a ha => by have := row a ha; omega)
       _ = T.card*(k+1-T.card) := by simp

theorem third_layer_quadratic (G : SimpleGraph V) (z : V) (k : ℕ)
    (cap : ∀ a ∈ layer G z 1, (layer G a 2).card ≤ k) :
    (layer G z 3).card ≤ (k+1)^2/4 := by
  obtain ⟨t,_,ht,hc⟩ := third_layer_product G z k cap
  apply hc.trans
  apply (Nat.le_div_iff_mul_le (by decide : 0<4)).mpr
  have h := four_mul_le_sq_add t (k+1-t)
  have hs : t+(k+1-t)=k+1 := by omega
  simpa [hs,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using h

/-- If the layer bounds at the root and its neighbors include the shared fourth-
distance charge of the far layer, they give a quadratic upper order bound. -/
theorem order_quadratic (G : SimpleGraph V) (connected : G.Connected) (z : V) (k : ℕ)
    (diam : ∀ v, G.dist z v ≤ 5)
    (rootCap : (layer G z 2).card+(layer G z 4).card ≤ k)
    (anchorCap : ∀ a ∈ layer G z 1, (layer G a 2).card+(layer G z 5).card ≤ k) :
    Fintype.card V ≤ 1+(layer G z 1).card+k+(k+1)^2/4 := by
  classical
  let A := layer G z 1
  let B := layer G z 2
  let C := layer G z 3
  let D := layer G z 4
  let F := layer G z 5
  have charged : C.card+F.card ≤ (k+1)^2/4 := by
    by_cases hf : F.card=0
    · rw [hf,Nat.add_zero]
      apply third_layer_quadratic
      intro a ha
      have h := anchorCap a ha
      change (layer G a 2).card+F.card≤k at h
      omega
    · obtain ⟨y,hy⟩ := card_pos.mp (Nat.pos_of_ne_zero hf)
      obtain ⟨d,hd,_⟩ := predecessor (d := 4) (in_layer.mp hy)
      obtain ⟨c,hc,_⟩ := predecessor (d := 3) hd
      obtain ⟨b,hb,_⟩ := predecessor (d := 2) hc
      obtain ⟨a,ha,_⟩ := predecessor (d := 1) hb
      have hac := anchorCap a (in_layer.mpr ha)
      change (layer G a 2).card+F.card≤k at hac
      have hk : F.card≤k := by omega
      obtain ⟨t,_,ht,hsize⟩ := third_layer_product G z (k-F.card) (by
        intro a ha
        have hp := anchorCap a ha
        change (layer G a 2).card+F.card≤k at hp
        omega)
      change C.card≤_ at hsize
      have hC : 0<C.card := card_pos.mpr ⟨c,in_layer.mpr hc⟩
      have htpos : 0<t := by
        by_contra! h
        have hz : t=0 := by omega
        rw [hz,Nat.zero_mul] at hsize
        omega
      have hsum : k+1-t=(k-F.card+1-t)+F.card := by omega
      have hmul := Nat.le_mul_of_pos_left F.card htpos
      have cp : C.card+F.card≤t*(k+1-t) := by rw [hsum,Nat.mul_add]; omega
      apply cp.trans
      apply (Nat.le_div_iff_mul_le (by decide : 0<4)).mpr
      have h := four_mul_le_sq_add t (k+1-t)
      have hs : t+(k+1-t)=k+1 := by omega
      simpa [hs,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using h
  have cov : (univ : Finset V) ⊆ insert z (A ∪ B ∪ C ∪ D ∪ F) := by
    intro v _
    have hd := diam v
    have cases : G.dist z v=0 ∨ G.dist z v=1 ∨ G.dist z v=2 ∨
      G.dist z v=3 ∨ G.dist z v=4 ∨ G.dist z v=5 := by omega
    rcases cases with h|h|h|h|h|h
    · have he := connected.dist_eq_zero_iff.mp h; simp [he]
    all_goals simp [A,B,C,D,F,h]
  have cb := card_le_card cov
  rw [card_univ] at cb
  have h0 := card_insert_le z (A∪B∪C∪D∪F)
  have h1 := card_union_le A B
  have h2 := card_union_le (A∪B) C
  have h3 := card_union_le (A∪B∪C) D
  have h4 := card_union_le (A∪B∪C∪D) F
  change B.card+D.card≤k at rootCap
  change Fintype.card V ≤ 1+A.card+k+(k+1)^2/4
  omega

end Graph189ThirdLayer

#print axioms Graph189ThirdLayer.third_layer_product
#print axioms Graph189ThirdLayer.third_layer_quadratic

#print axioms Graph189ThirdLayer.order_quadratic
