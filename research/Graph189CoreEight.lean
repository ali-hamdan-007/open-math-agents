import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Data.Fintype.Basic

namespace Graph189CoreEight

abbrev Label := Fin 8
/-- The labels are z,a,b,p,q and the three common middle vertices, in that order. -/
def middleDegree {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : Label → V) (i : Label) : Nat :=
  (([3,4,5,6,7] : List Label).map (fun j => decide (G.Adj (f i) (f j)))).count true

/-- A duplicate-free path on all eight labels, beginning at the requested label. -/
def Route {V : Type*} (G : SimpleGraph V) (f : Label → V) (i : Label) : Prop :=
  ∃ tail : List Label, (i :: tail).Nodup ∧ (∀ j, j ∈ i :: tail) ∧
    (i :: tail).IsChain (fun a b => G.Adj (f a) (f b))

/-- The counted middle degree is the cardinality of the actual middle neighbors
under an injective labeling. -/
theorem middleDegree_eq_card {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (f : Label → V) (hf : Function.Injective f) (i : Label) :
    middleDegree G f i =
      ((([3,4,5,6,7] : List Label).map f).toFinset.filter (G.Adj (f i))).card := by
  let l := ([3,4,5,6,7] : List Label).map f
  have hn : l.Nodup := List.Nodup.map hf (by decide : ([3,4,5,6,7] : List Label).Nodup)
  let p := fun x => decide (G.Adj (f i) x)
  change (l.map p).count true = (l.toFinset.filter (G.Adj (f i))).card
  have hcount : (l.map p).count true = (l.filter p).length := by
    rw [List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
    simp [Function.comp_def]
  rw [hcount, ← List.toFinset_card_of_nodup (hn.filter p), List.toFinset_filter]
  simp [p]

-- Each clause returned by this certificate is the three middle edges of a
-- concrete path. The other four edges of that path are fixed anchor edges.
set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem middle_cases : ∀
    (e34 e35 e36 e37 e45 e46 e47 e56 e57 e67 : Bool),
    (0 < [false, e34, e35, e36, e37].count true ∨ 0 < [e34, false, e45, e46, e47].count true) →
    2 ≤ [e35, e45, false, e56, e57].count true →
    2 ≤ [e36, e46, e56, false, e67].count true →
    2 ≤ [e37, e47, e57, e67, false].count true →
    ((e46 = true ∧ e57 = true ∧ e67 = true) ∨
     (e45 = true ∧ e47 = true ∧ e56 = true) ∨
     (e37 = true ∧ e56 = true ∧ e57 = true) ∨
     (e35 = true ∧ e56 = true ∧ e67 = true) ∨
     (e36 = true ∧ e45 = true ∧ e67 = true) ∨
     (e36 = true ∧ e47 = true ∧ e57 = true) ∨
     (e35 = true ∧ e46 = true ∧ e47 = true) ∨
     (e37 = true ∧ e45 = true ∧ e46 = true) ∨
     (e36 = true ∧ e57 = true ∧ e67 = true) ∨
     (e45 = true ∧ e56 = true ∧ e67 = true) ∨
     (e47 = true ∧ e56 = true ∧ e57 = true) ∨
     (e37 = true ∧ e46 = true ∧ e57 = true) ∨
     (e37 = true ∧ e47 = true ∧ e56 = true) ∨
     (e34 = true ∧ e57 = true ∧ e67 = true)) ∧
    ((e46 = true ∧ e57 = true ∧ e67 = true) ∨
     (e36 = true ∧ e47 = true ∧ e56 = true) ∨
     (e37 = true ∧ e56 = true ∧ e67 = true) ∨
     (e36 = true ∧ e45 = true ∧ e57 = true) ∨
     (e35 = true ∧ e47 = true ∧ e67 = true) ∨
     (e46 = true ∧ e56 = true ∧ e57 = true) ∨
     (e35 = true ∧ e36 = true ∧ e57 = true) ∨
     (e45 = true ∧ e56 = true ∧ e67 = true) ∨
     (e35 = true ∧ e37 = true ∧ e46 = true) ∨
     (e34 = true ∧ e56 = true ∧ e57 = true) ∨
     (e37 = true ∧ e45 = true ∧ e67 = true) ∨
     (e36 = true ∧ e56 = true ∧ e57 = true) ∨
     (e37 = true ∧ e47 = true ∧ e56 = true) ∨
     (e35 = true ∧ e57 = true ∧ e67 = true) ∨
     (e47 = true ∧ e56 = true ∧ e67 = true)) := by
  decide +kernel

/-- Both private vertices are possible initial endpoints. Extra ambient edges
are unrestricted, including edges among the anchors. -/
theorem routes {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (f : Label → V)
    (h01 : G.Adj (f 0) (f 1))
    (h02 : G.Adj (f 0) (f 2))
    (h14 : G.Adj (f 1) (f 4))
    (h15 : G.Adj (f 1) (f 5))
    (h16 : G.Adj (f 1) (f 6))
    (h17 : G.Adj (f 1) (f 7))
    (h23 : G.Adj (f 2) (f 3))
    (h25 : G.Adj (f 2) (f 5))
    (h26 : G.Adj (f 2) (f 6))
    (h27 : G.Adj (f 2) (f 7))
    (hp : 0 < middleDegree G f 3 ∨ 0 < middleDegree G f 4)
    (h5 : 2 ≤ middleDegree G f 5) (h6 : 2 ≤ middleDegree G f 6)
    (h7 : 2 ≤ middleDegree G f 7) : Route G f 3 ∧ Route G f 4 := by
  have cert := middle_cases
    (decide (G.Adj (f 3) (f 4))) (decide (G.Adj (f 3) (f 5))) (decide (G.Adj (f 3) (f 6)))
    (decide (G.Adj (f 3) (f 7))) (decide (G.Adj (f 4) (f 5))) (decide (G.Adj (f 4) (f 6)))
    (decide (G.Adj (f 4) (f 7))) (decide (G.Adj (f 5) (f 6))) (decide (G.Adj (f 5) (f 7)))
    (decide (G.Adj (f 6) (f 7)))
  simp only [decide_eq_true_eq] at cert
  have ⟨left, right⟩ := cert
    (by simpa [middleDegree, G.adj_comm (f 4) (f 3)] using hp)
    (by simpa [middleDegree, G.adj_comm (f 5) (f 3), G.adj_comm (f 5) (f 4)] using h5)
    (by simpa [middleDegree, G.adj_comm (f 6) (f 3), G.adj_comm (f 6) (f 4), G.adj_comm (f 6) (f 5)] using h6)
    (by simpa [middleDegree, G.adj_comm (f 7) (f 3), G.adj_comm (f 7) (f 4), G.adj_comm (f 7) (f 5), G.adj_comm (f 7) (f 6)] using h7)
  constructor
  · rcases left with
      ⟨e46, e57, e67⟩ |
      ⟨e45, e47, e56⟩ |
      ⟨e37, e56, e57⟩ |
      ⟨e35, e56, e67⟩ |
      ⟨e36, e45, e67⟩ |
      ⟨e36, e47, e57⟩ |
      ⟨e35, e46, e47⟩ |
      ⟨e37, e45, e46⟩ |
      ⟨e36, e57, e67⟩ |
      ⟨e45, e56, e67⟩ |
      ⟨e47, e56, e57⟩ |
      ⟨e37, e46, e57⟩ |
      ⟨e37, e47, e56⟩ |
      ⟨e34, e57, e67⟩
    · refine ⟨[2, 0, 1, 4, 6, 7, 5], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro h23.symm ⟨h02.symm, h01, h14, e46, e67, e57.symm⟩
    · refine ⟨[2, 0, 1, 6, 5, 4, 7], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro h23.symm ⟨h02.symm, h01, h16, e56.symm, e45.symm, e47⟩
    · refine ⟨[7, 5, 6, 2, 0, 1, 4], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro e37 ⟨e57.symm, e56, h26.symm, h02.symm, h01, h14⟩
    · refine ⟨[5, 6, 7, 2, 0, 1, 4], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro e35 ⟨e56, e67, h27.symm, h02.symm, h01, h14⟩
    · refine ⟨[6, 7, 1, 0, 2, 5, 4], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro e36 ⟨e67, h17.symm, h01.symm, h02, h25, e45.symm⟩
    · refine ⟨[6, 1, 0, 2, 5, 7, 4], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro e36 ⟨h16.symm, h01.symm, h02, h25, e57, e47.symm⟩
    · refine ⟨[5, 1, 0, 2, 6, 4, 7], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro e35 ⟨h15.symm, h01.symm, h02, h26, e46.symm, e47⟩
    · refine ⟨[7, 1, 0, 2, 5, 4, 6], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro e37 ⟨h17.symm, h01.symm, h02, h25, e45.symm, e46⟩
    · refine ⟨[6, 7, 5, 2, 0, 1, 4], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro e36 ⟨e67, e57.symm, h25.symm, h02.symm, h01, h14⟩
    · refine ⟨[2, 0, 1, 4, 5, 6, 7], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro h23.symm ⟨h02.symm, h01, h14, e45, e56, e67⟩
    · refine ⟨[2, 0, 1, 4, 7, 5, 6], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro h23.symm ⟨h02.symm, h01, h14, e47, e57.symm, e56⟩
    · refine ⟨[7, 5, 1, 0, 2, 6, 4], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro e37 ⟨e57.symm, h15.symm, h01.symm, h02, h26, e46.symm⟩
    · refine ⟨[7, 4, 1, 0, 2, 5, 6], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro e37 ⟨e47.symm, h14.symm, h01.symm, h02, h25, e56⟩
    · refine ⟨[4, 1, 0, 2, 5, 7, 6], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro e34 ⟨h14.symm, h01.symm, h02, h25, e57, e67.symm⟩
  · rcases right with
      ⟨e46, e57, e67⟩ |
      ⟨e36, e47, e56⟩ |
      ⟨e37, e56, e67⟩ |
      ⟨e36, e45, e57⟩ |
      ⟨e35, e47, e67⟩ |
      ⟨e46, e56, e57⟩ |
      ⟨e35, e36, e57⟩ |
      ⟨e45, e56, e67⟩ |
      ⟨e35, e37, e46⟩ |
      ⟨e34, e56, e57⟩ |
      ⟨e37, e45, e67⟩ |
      ⟨e36, e56, e57⟩ |
      ⟨e37, e47, e56⟩ |
      ⟨e35, e57, e67⟩ |
      ⟨e47, e56, e67⟩
    · refine ⟨[6, 7, 5, 1, 0, 2, 3], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro e46 ⟨e67, e57.symm, h15.symm, h01.symm, h02, h23⟩
    · refine ⟨[7, 1, 0, 2, 3, 6, 5], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro e47 ⟨h17.symm, h01.symm, h02, h23, e36, e56.symm⟩
    · refine ⟨[1, 0, 2, 3, 7, 6, 5], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro h14.symm ⟨h01.symm, h02, h23, e37, e67.symm, e56.symm⟩
    · refine ⟨[5, 7, 1, 0, 2, 3, 6], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro e45 ⟨e57, h17.symm, h01.symm, h02, h23, e36⟩
    · refine ⟨[7, 6, 1, 0, 2, 3, 5], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro e47 ⟨e67.symm, h16.symm, h01.symm, h02, h23, e35⟩
    · refine ⟨[6, 5, 7, 1, 0, 2, 3], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro e46 ⟨e56.symm, e57, h17.symm, h01.symm, h02, h23⟩
    · refine ⟨[1, 0, 2, 6, 3, 5, 7], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro h14.symm ⟨h01.symm, h02, h26, e36.symm, e35, e57⟩
    · refine ⟨[5, 6, 7, 1, 0, 2, 3], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro e45 ⟨e56, e67, h17.symm, h01.symm, h02, h23⟩
    · refine ⟨[6, 1, 0, 2, 5, 3, 7], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro e46 ⟨h16.symm, h01.symm, h02, h25, e35.symm, e37⟩
    · refine ⟨[3, 2, 0, 1, 6, 5, 7], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro e34.symm ⟨h23.symm, h02.symm, h01, h16, e56.symm, e57⟩
    · refine ⟨[5, 1, 0, 2, 3, 7, 6], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro e45 ⟨h15.symm, h01.symm, h02, h23, e37, e67.symm⟩
    · refine ⟨[1, 0, 2, 3, 6, 5, 7], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro h14.symm ⟨h01.symm, h02, h23, e36, e56.symm, e57⟩
    · refine ⟨[7, 3, 2, 0, 1, 5, 6], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro e47 ⟨e37.symm, h23.symm, h02.symm, h01, h15, e56⟩
    · refine ⟨[1, 0, 2, 3, 5, 7, 6], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro h14.symm ⟨h01.symm, h02, h23, e35, e57, e67.symm⟩
    · refine ⟨[7, 6, 5, 1, 0, 2, 3], by decide, by decide, ?_⟩
      simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using
        And.intro e47 ⟨e67.symm, e56.symm, h15.symm, h01.symm, h02, h23⟩


/-- Convert the labelled route to an ambient simple path with exactly the
eight labelled vertices as its support. -/
theorem Route.toWalk {V : Type*} {G : SimpleGraph V} {f : Label → V} {i : Label}
    (h : Route G f i) (hf : Function.Injective f) :
    ∃ t, ∃ p : G.Walk (f i) t, p.IsPath ∧ ∀ x, x ∈ p.support ↔ x ∈ Set.range f := by
  obtain ⟨tail, hn, hc, he⟩ := h
  let l := (i :: tail).map f
  have hne : l ≠ [] := by simp [l]
  have hadj : l.IsChain G.Adj := (List.isChain_map f).2 he
  change ∃ t, ∃ p : G.Walk (l.head hne) t, p.IsPath ∧ ∀ x, x ∈ p.support ↔ x ∈ Set.range f
  refine ⟨l.getLast hne, SimpleGraph.Walk.ofSupport l hne hadj, ?_, ?_⟩
  · apply SimpleGraph.Walk.IsPath.mk'
    rw [SimpleGraph.Walk.support_ofSupport]
    exact hn.map hf
  · intro x
    rw [SimpleGraph.Walk.support_ofSupport]
    change x ∈ (i :: tail).map f ↔ _
    exact ⟨fun hx => (List.mem_map.mp hx).elim fun j hj => ⟨j, hj.2⟩,
      fun ⟨j, hj⟩ => List.mem_map.mpr ⟨j, hc j, hj⟩⟩

#print axioms Route.toWalk
#print axioms routes
end Graph189CoreEight
