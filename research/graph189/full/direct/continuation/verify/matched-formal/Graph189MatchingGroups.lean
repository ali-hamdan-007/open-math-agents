import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset

namespace Graph189MatchingGroups

/-- A maximum-cardinality matching in a finite bipartite edge relation is maximal. -/
theorem exists_maximal_pairs {B A : Type*} [DecidableEq B] [DecidableEq A]
    (left : Finset B) (right : Finset A) (linked : B → A → Prop) :
    ∃ M : Finset (B × A),
      (∀ p ∈ M, p.1 ∈ left ∧ p.2 ∈ right ∧ linked p.1 p.2) ∧
      Set.InjOn Prod.fst (M : Set (B × A)) ∧
      Set.InjOn Prod.snd (M : Set (B × A)) ∧
      ∀ b ∈ left, ∀ a ∈ right, linked b a →
        (∃ p ∈ M, p.1 = b) ∨ (∃ p ∈ M, p.2 = a) := by
  classical
  let edges := (left ×ˢ right).filter (fun p => linked p.1 p.2)
  let candidates := edges.powerset.filter (fun (M : Finset (B × A)) =>
    Set.InjOn Prod.fst (M : Set (B × A)) ∧ Set.InjOn Prod.snd (M : Set (B × A)))
  have hzero : (∅ : Finset (B × A)) ∈ candidates := by simp [candidates, Set.InjOn]
  obtain ⟨M,hM,hmax⟩ := exists_max_image candidates Finset.card ⟨∅,hzero⟩
  obtain ⟨hsub, hinjB, hinjA⟩ := mem_filter.mp hM
  have he : M ⊆ edges := mem_powerset.mp hsub
  refine ⟨M, ?_, hinjB, hinjA, ?_⟩
  · intro p hp
    obtain ⟨hprod, hlink⟩ := mem_filter.mp (he hp)
    exact ⟨(mem_product.mp hprod).1, (mem_product.mp hprod).2, hlink⟩
  · intro b hb a ha hlink
    by_cases hmissB : ∃ p ∈ M, p.1 = b
    · exact Or.inl hmissB
    by_cases hmissA : ∃ p ∈ M, p.2 = a
    · exact Or.inr hmissA
    exfalso
    let p : B × A := (b,a)
    have hp : p ∈ edges := mem_filter.mpr ⟨mem_product.mpr ⟨hb,ha⟩,hlink⟩
    have hnot : p ∉ M := fun hm => hmissB ⟨p,hm,rfl⟩
    have hIns : insert p M ∈ candidates := by
      refine mem_filter.mpr ⟨mem_powerset.mpr (insert_subset hp he), ?_, ?_⟩
      · intro q hq r hr heq
        change q ∈ insert p M at hq
        change r ∈ insert p M at hr
        rcases mem_insert.mp hq with rfl | hq <;> rcases mem_insert.mp hr with rfl | hr
        · rfl
        · exact (hmissB ⟨r,hr,heq.symm⟩).elim
        · exact (hmissB ⟨q,hq,heq⟩).elim
        · exact hinjB hq hr heq
      · intro q hq r hr heq
        change q ∈ insert p M at hq
        change r ∈ insert p M at hr
        rcases mem_insert.mp hq with rfl | hq <;> rcases mem_insert.mp hr with rfl | hr
        · rfl
        · exact (hmissA ⟨r,hr,heq.symm⟩).elim
        · exact (hmissA ⟨q,hq,heq⟩).elim
        · exact hinjA hq hr heq
    have h := hmax (insert p M) hIns
    rw [card_insert_of_notMem hnot] at h
    omega

/-- Assign every target to a matched edge with a suitable predecessor. Each matched edge
receives one distinct designated target from its own column. -/
theorem exists_matching_groups {B A T : Type*}
    [DecidableEq B] [DecidableEq A] [DecidableEq T] [Nonempty (B × A)] [Nonempty T]
    (left : Finset B) (targets : Finset T) (column : T → A) (linked : B → A → Prop)
    (accessible : ∀ x ∈ targets, ∃ b ∈ left, linked b (column x)) :
    ∃ (M : Finset (B × A)) (group : T → B × A) (rep : B × A → T),
      (∀ p ∈ M, p.1 ∈ left ∧ p.2 ∈ targets.image column ∧ linked p.1 p.2) ∧
      Set.InjOn Prod.fst (M : Set (B × A)) ∧
      Set.InjOn Prod.snd (M : Set (B × A)) ∧
      (∀ x ∈ targets, group x ∈ M ∧ linked (group x).1 (column x)) ∧
      ∀ p ∈ M, rep p ∈ targets ∧ column (rep p) = p.2 ∧ group (rep p) = p := by
  classical
  obtain ⟨M, hM, hfst, hsnd, hmax⟩ := exists_maximal_pairs left (targets.image column) linked
  have eligible (x : T) (hx : x ∈ targets) : ∃ p ∈ M,
      linked p.1 (column x) ∧ (∀ q ∈ M, q.2 = column x → p = q) := by
    by_cases hcol : ∃ q ∈ M, q.2 = column x
    · obtain ⟨q,hq,heq⟩ := hcol
      refine ⟨q,hq,heq ▸ (hM q hq).2.2,?_⟩
      intro p hp hep
      exact hsnd hq hp (heq.trans hep.symm)
    · obtain ⟨b,hb,hlink⟩ := accessible x hx
      rcases hmax b hb (column x) (mem_image_of_mem column hx) hlink with h | h
      · obtain ⟨p,hp,heq⟩ := h
        exact ⟨p,hp,heq.symm ▸ hlink,fun q hq hqeq => (hcol ⟨q,hq,hqeq⟩).elim⟩
      · exact (hcol h).elim
  let group (x : T) : B × A := if hx : x ∈ targets then (eligible x hx).choose else Classical.arbitrary _
  have hg (x : T) (hx : x ∈ targets) : group x ∈ M ∧ linked (group x).1 (column x) ∧
      ∀ q ∈ M, q.2 = column x → group x = q := by simpa only [group,dif_pos hx] using (eligible x hx).choose_spec
  have hre (p : B × A) (hp : p ∈ M) : ∃ x ∈ targets, column x = p.2 :=
    mem_image.mp (hM p hp).2.1
  let rep (p : B × A) : T := if hp : p ∈ M then (hre p hp).choose else Classical.arbitrary _
  refine ⟨M,group,rep,hM,hfst,hsnd,fun x hx => ⟨(hg x hx).1,(hg x hx).2.1⟩,?_⟩
  intro p hp
  have ht : rep p ∈ targets ∧ column (rep p) = p.2 := by
    simpa only [rep,dif_pos hp] using (hre p hp).choose_spec
  exact ⟨ht.1,ht.2,(hg (rep p) ht.1).2.2 p hp ht.2.symm⟩

end Graph189MatchingGroups
