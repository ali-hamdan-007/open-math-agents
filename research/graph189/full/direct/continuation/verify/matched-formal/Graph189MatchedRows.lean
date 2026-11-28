import Graph189MatchedCharging
import Graph189WedgeOrder

open Finset SimpleGraph
open scoped BigOperators

namespace Graph189MatchedRows

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def evenSet (v : V) : Finset V := Finset.univ.filter (fun w => Even (G.dist v w))

def credit (y z : V) (p : V × V) : ℕ :=
  (if G.Adj p.1 y then 1 else 0) + (if G.Adj p.1 z then 1 else 0)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem nonadj_of_layers {x u v : V} (hu : G.dist x u = 1) (hv : G.dist x v = 3) :
    ¬G.Adj u v := by
  intro h
  have hh := h.diff_dist_adj (u:=x)
  omega

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem evenSet_of_two_edges (hc : G.Connected) {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hac : ¬G.Adj a c) : c ∈ evenSet G a := by
  have h := hc.dist_triangle (u:=a) (v:=b) (w:=c)
  rw [dist_eq_one_iff_adj.mpr hab,dist_eq_one_iff_adj.mpr hbc] at h
  have hne : G.dist a c ≠ 1 := fun hh => hac (dist_eq_one_iff_adj.mp hh)
  exact Finset.mem_filter.mpr ⟨mem_univ _,by rw [Nat.even_iff]; omega⟩

/-- The first-, second- and third-layer witnesses pay for every other matched row. -/
theorem matched_rows_le (hc : G.Connected) {x y z : V} (hxy : G.Adj x y)
    (hxz : G.Adj x z) (hyz : y ≠ z) {k : ℕ} (cap : ∀ v, G.distEven v ≤ k+1)
    (targets : Finset V) (column : V → V) (M : Finset (V × V))
    (group : V → V × V) (rep : V × V → V)
    (htarget : ∀ v ∈ targets, G.dist x v = 3 ∧ G.Adj (column v) v)
    (hM : ∀ p ∈ M, G.dist x p.1 = 1 ∧ G.dist x p.2 = 2 ∧ G.Adj p.1 p.2 ∧
      ¬G.Adj y p.2 ∧ ¬G.Adj z p.2)
    (hfst : Set.InjOn Prod.fst (M : Set (V × V)))
    (hsnd : Set.InjOn Prod.snd (M : Set (V × V)))
    (hgroup : ∀ v ∈ targets, group v ∈ M ∧ G.Adj (group v).1 (column v))
    (hrep : ∀ p ∈ M, rep p ∈ targets ∧ column (rep p) = p.2 ∧ group (rep p) = p) :
    targets.card + M.card * (M.card + 1) ≤ M.card * k + ∑ p ∈ M, credit G y z p := by
  classical
  let fixed (p : V × V) := insert p.1 (({y,z} : Finset V).filter fun v => ¬G.Adj p.1 v)
  let witness (p q : V × V) := if G.Adj p.1 q.2 then rep q
    else if G.Adj p.1 q.1 then q.2 else q.1
  have ep (p : V × V) (hp : p ∈ M) : p.1 ≠ y ∧ p.1 ≠ z := by
    have hh := hM p hp
    exact ⟨fun he => hh.2.2.2.1 (he ▸ hh.2.2.1),fun he => hh.2.2.2.2 (he ▸ hh.2.2.1)⟩
  have dy : G.dist x y = 1 := dist_eq_one_iff_adj.mpr hxy
  have dz : G.dist x z = 1 := dist_eq_one_iff_adj.mpr hxz
  have fixed_layer (p : V × V) (hp : p ∈ M) (a : V) (ha : a ∈ fixed p) : G.dist x a = 1 := by
    rcases mem_insert.mp ha with h | h
    · rw [h]; exact (hM p hp).1
    · have hv := (mem_filter.mp h).1
      simp only [mem_insert,mem_singleton] at hv
      rcases hv with rfl|rfl
      · exact dy
      · exact dz
  have rep_layer (p : V × V) (hp : p ∈ M) : G.dist x (rep p) = 3 :=
    (htarget _ (hrep p hp).1).1
  refine Graph189MatchedCharging.card_targets_le M targets group
    (fun p => evenSet G p.1) fixed witness (credit G y z)
    (fun v hv => (hgroup v hv).1) (fun p _ => cap p.1) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hey,hez⟩ := ep p hp
    have h₁ : p.1 ∉ ({y,z} : Finset V) := by simp [hey,hez]
    change (insert p.1 (({y,z} : Finset V).filter fun v => ¬G.Adj p.1 v)).card + _ = 3
    rw [card_insert_of_notMem (fun h => h₁ ((mem_filter.mp h).1))]
    by_cases hy : G.Adj p.1 y <;> by_cases hz : G.Adj p.1 z <;>
      simp [Finset.filter_insert,Finset.filter_singleton, credit, *]
  · intro p hp a ha
    rcases mem_insert.mp ha with rfl | hh
    · simp [evenSet]
    · obtain ⟨hset,hnadj⟩ := mem_filter.mp hh
      simp only [mem_insert,mem_singleton] at hset
      have hpx : G.Adj p.1 x := (dist_eq_one_iff_adj.mp (hM p hp).1).symm
      rcases hset with rfl | rfl
      · exact evenSet_of_two_edges G hc hpx hxy hnadj
      · exact evenSet_of_two_edges G hc hpx hxz hnadj
  · intro p hp v hv hgp
    obtain ⟨hvd,hav⟩ := htarget v hv
    have hpa := (hgroup v hv).2
    rw [hgp] at hpa
    exact ⟨evenSet_of_two_edges G hc hpa hav (nonadj_of_layers G (hM p hp).1 hvd),
      fun hf => by have hh := fixed_layer p hp v hf; omega⟩
  · intro p hp q hq hne
    by_cases hpa : G.Adj p.1 q.2
    · have hav : G.Adj q.2 (rep q) := by
        simpa [(hrep q hq).2.1] using (htarget _ (hrep q hq).1).2
      simp only [witness,if_pos hpa]
      exact ⟨evenSet_of_two_edges G hc hpa hav (nonadj_of_layers G (hM p hp).1 (rep_layer q hq)),
        fun hf => by have hh := fixed_layer p hp _ hf; have hd := rep_layer q hq; omega,
        fun _ => by simpa [(hrep q hq).2.2] using hne⟩
    by_cases hpb : G.Adj p.1 q.1
    · simp only [witness,if_neg hpa,if_pos hpb]
      exact ⟨evenSet_of_two_edges G hc hpb (hM q hq).2.2.1 hpa,
        fun hf => by have hh := fixed_layer p hp _ hf; have hd := (hM q hq).2.1; omega,
        fun ht => by have hd₁ := (hM q hq).2.1; have hd₂ := (htarget _ ht).1; omega⟩
    · simp only [witness,if_neg hpa,if_neg hpb]
      have hpx : G.Adj p.1 x := (dist_eq_one_iff_adj.mp (hM p hp).1).symm
      have hxq : G.Adj x q.1 := dist_eq_one_iff_adj.mp (hM q hq).1
      refine ⟨evenSet_of_two_edges G hc hpx hxq hpb,?_,?_⟩
      · intro hf
        rcases mem_insert.mp hf with he | he
        · exact hne (hfst hq hp he)
        · have hset := (mem_filter.mp he).1
          simp [(ep q hq).1,(ep q hq).2] at hset
      · intro ht
        have hd₁ := (hM q hq).1
        have hd₂ := (htarget _ ht).1
        omega
  · intro p _ q hq r hr heq
    change q ∈ M.erase p at hq
    change r ∈ M.erase p at hr
    have hqm := (mem_erase.mp hq).2
    have hrm := (mem_erase.mp hr).2
    have auxiliary (q : V × V) (hq : q ∈ M) :
        (witness p q = rep q ∧ G.dist x (witness p q) = 3) ∨
        (witness p q = q.2 ∧ G.dist x (witness p q) = 2) ∨
        (witness p q = q.1 ∧ G.dist x (witness p q) = 1) := by
      by_cases hpa : G.Adj p.1 q.2
      · exact Or.inl (by simp [witness,hpa,rep_layer q hq])
      by_cases hpb : G.Adj p.1 q.1
      · exact Or.inr (Or.inl (by simp [witness,hpa,hpb,(hM q hq).2.1]))
      · exact Or.inr (Or.inr (by simp [witness,hpa,hpb,(hM q hq).1]))
    rcases auxiliary q hqm with ⟨hqv,hqd⟩ | ⟨hqv,hqd⟩ | ⟨hqv,hqd⟩ <;>
      rcases auxiliary r hrm with ⟨hrv,hrd⟩ | ⟨hrv,hrd⟩ | ⟨hrv,hrd⟩ <;>
      try (rw [heq,hrd] at hqd; omega)
    all_goals have heq' := hqv.symm.trans (heq.trans hrv)
    · exact (hrep q hqm).2.2.symm.trans ((congrArg group heq').trans (hrep r hrm).2.2)
    · exact hsnd hqm hrm heq'
    · exact hfst hqm hrm heq'

end Graph189MatchedRows
