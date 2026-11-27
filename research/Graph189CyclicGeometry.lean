import Graph189ShortestOdd
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic.Ring

namespace Graph189CyclicGeometry
open SimpleGraph
open scoped Fin.CommRing Fin.NatCast
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [Nontrivial V] [DecidableRel G.Adj] in
/-- Adjacent two-edge endpoints with no shortcut have distance two. -/
private theorem dist_two_of_triangle_free
    (htri : ∀ {a b c}, G.Adj a b → G.Adj b c → ¬ G.Adj a c)
    {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hac : a ≠ c) :
    G.dist a c = 2 := by
  let p : G.Walk a c := .cons hab (.cons hbc .nil)
  have hl : G.dist a c ≤ 2 := by simpa [p] using G.dist_le p
  have hp : 0 < G.dist a c :=
    Nat.pos_of_ne_zero (fun h => hac (p.reachable.dist_eq_zero_iff.mp h))
  have hn : G.dist a c ≠ 1 := fun h => htri hab hbc (dist_eq_one_iff_adj.mp h)
  omega

/-- Index geometry for a shortest odd cycle suffices for the incidence argument. -/
theorem traceable_of_geometry (h : G.Connected)
    (htri : ∀ {a b c}, G.Adj a b → G.Adj b c → ¬ G.Adj a c)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree)
    {m : ℕ} [NeZero m] (hm : 5 ≤ m) (hodd : m % 2 = 1) (f : Fin m ↪ V)
    (hcyc : ∀ i : Fin m, G.Adj (f i) (f (i+1)))
    (h1 : ∀ i j : Fin m, G.Adj (f i) (f j) → j = i+1 ∨ i = j+1)
    (h2 : ∀ i j : Fin m, i ≠ j → (∃ x, G.Adj (f i) x ∧ G.Adj x (f j)) →
      j = i+2 ∨ i = j+2) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  let C := Finset.univ.map f
  have hc : C.card = m := by simp [C]
  have shift_ne (k : ℕ) (hk : 0 < k) (hk' : k < m) : (k : Fin m) ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    rw [Fin.val_natCast, Nat.mod_eq_of_lt hk', Fin.val_zero] at hv
    omega
  have hn₂ : (2 : Fin m) ≠ 0 := shift_ne 2 (by omega) (by omega)
  have hn₄ : (4 : Fin m) ≠ 0 := shift_ne 4 (by omega) (by omega)
  have hn₆ : (6 : Fin m) ≠ 0 := by
    by_cases he : m = 5
    · intro heq
      have hv := congrArg Fin.val heq
      have hv' : 6 % m = 0 := by simpa [Fin.val_natCast] using hv
      rw [he] at hv'
      omega
    · exact shift_ne 6 (by omega) (by omega)
  have triple_ne (i : Fin m) : i-1 ≠ i+1 ∧ i-1 ≠ i+3 ∧ i+1 ≠ i+3 := by
    constructor
    · intro e
      apply hn₂
      apply add_left_cancel (a := i)
      calc
        i + 2 = (i+1)+1 := by ring
        _ = (i-1)+1 := congrArg (fun t => t+1) e.symm
        _ = i+0 := by ring
    · constructor
      · intro e
        apply hn₄
        apply add_left_cancel (a := i)
        calc
          i + 4 = (i+3)+1 := by ring
          _ = (i-1)+1 := congrArg (fun t => t+1) e.symm
          _ = i+0 := by ring
      · intro e
        apply hn₂
        apply add_left_cancel (a := i+1)
        calc
          (i+1)+2 = i+3 := by ring
          _ = (i+1)+0 := by simpa using e.symm
  have even_ne (i : Fin m) : i ≠ i+2 ∧ i ≠ i-2 ∧ i+2 ≠ i-2 := by
    refine ⟨fun e => hn₂ (add_left_cancel (a := i) (by simpa using e.symm)),?_,?_⟩
    · intro e
      apply hn₂
      apply add_left_cancel (a := i)
      calc
        i + 2 = (i-2)+2 := congrArg (fun t => t+2) e
        _ = i+0 := by ring
    · intro e
      apply hn₄
      apply add_left_cancel (a := i)
      calc
        i + 4 = (i+2)+2 := by ring
        _ = (i-2)+2 := congrArg (fun t => t+2) e
        _ = i+0 := by ring
  have backwards (i : Fin m) : G.Adj (f i) (f (i-1)) := by
    have hh := (hcyc (i-1)).symm
    rwa [sub_add_cancel] at hh
  have internal_neighbors (v : V) (hv : v ∈ C) : (C.filter (G.Adj v)).card ≤ 2 := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hv
    rw [Finset.filter_map, Finset.card_map]
    have hs : (Finset.univ.filter (G.Adj (f i) ∘ f)) ⊆ ({i+1,i-1} : Finset (Fin m)) := by
      intro j hj
      rcases h1 i j (Finset.mem_filter.mp hj).2 with e | e
      · simp [e]
      · have he : j = i-1 := eq_sub_of_add_eq e.symm
        simp [he]
    have hle := Finset.card_le_card hs
    exact hle.trans Finset.card_le_two
  have internal_even (v : V) (hv : v ∈ C) :
      3 ≤ (C.filter (fun x => Even (G.dist v x))).card := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hv
    rw [Finset.filter_map, Finset.card_map]
    have hp : G.dist (f i) (f (i+2)) = 2 :=
      dist_two_of_triangle_free htri (hcyc i)
        (by convert hcyc (i+1) using 2; ring)
        (fun e => (even_ne i).1 (f.injective e))
    have hm' : G.dist (f i) (f (i-2)) = 2 :=
      dist_two_of_triangle_free htri (backwards i)
        (by convert backwards (i-1) using 2; ring)
        (fun e => (even_ne i).2.1 (f.injective e))
    have hsub : ({i,i+2,i-2} : Finset (Fin m)) ⊆
        Finset.univ.filter ((fun x => Even (G.dist (f i) x)) ∘ f) := by
      intro j hj
      rcases (show j = i ∨ j = i+2 ∨ j = i-2 from by simpa using hj) with e | e | e
      · subst j; simp
      · subst j; simp [hp]
      · subst j; simp [hm']
    have hle := Finset.card_le_card hsub
    have hn := even_ne i
    simpa [Finset.card_insert_of_notMem, hn.1, hn.2.1, hn.2.2] using hle
  have external (x : V) (hx : x ∉ C) : 3 * (C.filter (fun v => G.Adj v x)).card ≤
      2 * (C.filter (fun v => G.dist v x = 2)).card := by
    let T := Finset.univ.filter (fun i : Fin m => G.Adj (f i) x)
    let D := Finset.univ.filter (fun i : Fin m => G.dist (f i) x = 2)
    rw [Finset.filter_map, Finset.filter_map, Finset.card_map, Finset.card_map]
    change 3 * T.card ≤ 2 * D.card
    have htouch {i : Fin m} (hi : i ∈ T) : G.Adj (f i) x := (Finset.mem_filter.mp hi).2
    have force {i j : Fin m} (hi : i ∈ T) (hj : j ∈ T) (hne : i ≠ j) :
        j = i+2 ∨ i = j+2 := h2 i j hne ⟨x,htouch hi,(htouch hj).symm⟩
    have hvertex (i : Fin m) : f i ≠ x := fun he =>
      hx (Finset.mem_map.mpr ⟨i,Finset.mem_univ _,he⟩)
    have dist_at {i j : Fin m} (hi : i ∈ T) (ha : G.Adj (f j) (f i)) : j ∈ D :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        dist_two_of_triangle_free htri ha (htouch hi) (hvertex j)⟩
    by_cases hlarge : 1 < T.card
    · obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hlarge
      obtain ⟨i,hi,hj⟩ : ∃ i : Fin m, i ∈ T ∧ i+2 ∈ T := by
        rcases force ha hb hab with e | e
        · exact ⟨a,ha,e ▸ hb⟩
        · exact ⟨b,hb,e ▸ ha⟩
      have hnot : i-2 ∉ T := by
        intro hn
        have hneq := (even_ne i).2.2
        rcases force hj hn hneq with he | he
        · apply hn₆
          apply add_left_cancel (a := i)
          calc
            i + 6 = ((i+2)+2)+2 := by ring
            _ = (i-2)+2 := congrArg (fun t => t+2) he.symm
            _ = i+0 := by ring
        · have he' : i+2 = i := by simpa using he
          exact (even_ne i).1 he'.symm
      have hs : T ⊆ ({i,i+2} : Finset (Fin m)) := by
        intro j hj'
        by_cases he : j = i
        · simp [he]
        · rcases force hi hj' (Ne.symm he) with e | e
          · simp [e]
          · have he' : j = i-2 := eq_sub_of_add_eq e.symm
            exact (hnot (he' ▸ hj')).elim
      have hTcard : T.card ≤ 2 := (Finset.card_le_card hs).trans Finset.card_le_two
      have htriD : ({i-1,i+1,i+3} : Finset (Fin m)) ⊆ D := by
        intro j hmj
        rcases (show j = i-1 ∨ j = i+1 ∨ j = i+3 from by simpa using hmj) with e | e | e
        · subst j; exact dist_at hi (backwards i).symm
        · subst j; exact dist_at hi (hcyc i).symm
        · subst j
          apply dist_at hj
          convert (hcyc (i+2)).symm using 2; ring
      have hDcard := Finset.card_le_card htriD
      have hne := triple_ne i
      simp [Finset.card_insert_of_notMem,hne.1,hne.2.1,hne.2.2] at hDcard
      omega
    · by_cases hempty : T.Nonempty
      · obtain ⟨i,hi⟩ := hempty
        have hpairD : ({i-1,i+1} : Finset (Fin m)) ⊆ D := by
          intro j hmj
          rcases (show j = i-1 ∨ j = i+1 from by simpa using hmj) with e | e
          · subst j; exact dist_at hi (backwards i).symm
          · subst j; exact dist_at hi (hcyc i).symm
        have hl := Finset.card_le_card hpairD
        rw [Finset.card_pair (triple_ne i).1] at hl
        omega
      · have he := Finset.not_nonempty_iff_eq_empty.mp hempty
        simp [he]
  have hspans : C = Finset.univ :=
    Graph189OddCycleCount.odd_cycle_core_spans h C (hc ▸ hm) hσ
      internal_neighbors internal_even external
  let L := (List.finRange m).map f
  have hcard : Fintype.card V = m := by rw [← Finset.card_univ,← hspans,hc]
  have hnodup : L.Nodup := (List.nodup_finRange m).map f.injective
  have hlen : L.length = m := by simp [L]
  have hne : L ≠ [] := by intro hnil; simp [hnil] at hlen; omega
  have hchain : L.IsChain G.Adj := by
    dsimp [L]
    rw [List.isChain_map,List.isChain_iff_getElem]
    intro i hi
    have hi' : i+1 < m := by simpa using hi
    have he : (List.finRange m)[i+1] = (List.finRange m)[i] + (1 : Fin m) := by
      apply Fin.ext
      simp only [List.getElem_finRange,Fin.val_add,Fin.val_one',Fin.val_cast]
      rw [Nat.mod_eq_of_lt (by omega : 1 < m), Nat.mod_eq_of_lt hi']
    rw [he]
    exact hcyc _
  exact Graph189Bipartite.hamiltonian_of_chain L hne hchain hnodup (hlen.trans hcard.symm)

#print axioms traceable_of_geometry
end Graph189CyclicGeometry
