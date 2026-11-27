import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Lattice.Basic

namespace Graph199

open SimpleGraph Finset

/-- A geodesic can be indexed by an embedding, with edges exactly at
consecutive indices. -/
theorem shortest_indexed_connector {U : Type*} {K : SimpleGraph U} {a b : U}
    (hr : K.Reachable a b) :
    ∃ d, ∃ center : Fin (d + 1) ↪ U, d = K.dist a b ∧
      center 0 = a ∧ center (Fin.last d) = b ∧
      (∀ i : Fin d, K.Adj (center i.castSucc) (center i.succ)) ∧
      (∀ i j : Fin (d+1), i.val + 1 < j.val → ¬ K.Adj (center i) (center j)) := by
  obtain ⟨p, _, hp⟩ := hr.exists_path_of_dist
  let d := p.length
  have hdist (i : Fin (d + 1)) : K.dist a (p.getVert i.val) = i.val := by
    have hsub := SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_take i.val)
    have hi : i.val ≤ p.length := Nat.le_of_lt_succ i.isLt
    simpa [Walk.take_length, min_eq_left hi] using hsub.symm
  let center : Fin (d+1) ↪ U := ⟨fun i => p.getVert i.val, by
    intro i j he
    apply Fin.ext
    exact (hdist i).symm.trans <| (congrArg (K.dist a) he).trans (hdist j)⟩
  refine ⟨d, center, hp, ?_, ?_, ?_, ?_⟩
  · exact p.getVert_zero
  · exact p.getVert_length
  · intro i
    exact p.adj_getVert_succ i.isLt
  · intro i j hij he
    have hstep := he.diff_dist_adj (u := a)
    change K.Adj (p.getVert i.val) (p.getVert j.val) at he
    change K.dist a (p.getVert j.val) = K.dist a (p.getVert i.val) ∨
      K.dist a (p.getVert j.val) = K.dist a (p.getVert i.val) + 1 ∨
      K.dist a (p.getVert j.val) = K.dist a (p.getVert i.val) - 1 at hstep
    rw [hdist j, hdist i] at hstep
    omega

/-- Two reachable vertices with no edge and no common neighbor have a
geodesic of length at least three. -/
theorem connector_dist_ge_three {U : Type*} {K : SimpleGraph U} {a b : U}
    (hr : K.Reachable a b) (hne : a ≠ b) (hn : ¬ K.Adj a b)
    (hcommon : ∀ x, ¬ (K.Adj a x ∧ K.Adj x b)) : 3 ≤ K.dist a b := by
  by_contra! h
  rcases (show K.dist a b = 0 ∨ K.dist a b = 1 ∨ K.dist a b = 2 by omega) with hz | ho | ht
  · exact hne (hr.dist_eq_zero_iff.mp hz)
  · exact hn (dist_eq_one_iff_adj.mp ho)
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
    have hlen : p.length = 2 := hp.trans ht
    have ha := p.adj_getVert_succ (i := 0) (by omega)
    have hb := p.adj_getVert_succ (i := 1) (by omega)
    have he := p.getVert_length
    rw [hlen] at he
    exact hcommon (p.getVert 1) ⟨by simpa using ha, by simpa [he] using hb⟩

/-- Distinct separator rows are compatible if their vertices are adjacent
or the rows name a common outside component. -/
def separatorCompatibility {U C : Type*} [DecidableEq C]
    (K : SimpleGraph U) (R : U → Finset C) : SimpleGraph U where
  Adj u v := u ≠ v ∧ (K.Adj u v ∨ (R u ∩ R v).Nonempty)
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with he | hi
    · exact Or.inl he.symm
    · exact Or.inr (by simpa only [inter_comm] using hi)⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

@[simp]
theorem separatorCompatibility_adj {U C : Type*} [DecidableEq C]
    (K : SimpleGraph U) (R : U → Finset C) (u v : U) :
    (separatorCompatibility K R).Adj u v ↔
      u ≠ v ∧ (K.Adj u v ∨ (R u ∩ R v).Nonempty) := Iff.rfl

/-- Nonconsecutive centers in a shortest compatibility path have no edge
and no common component label. -/
theorem separator_shortest_connector {U C : Type*} [DecidableEq C]
    (K : SimpleGraph U) (R : U → Finset C) {a b : U}
    (hr : (separatorCompatibility K R).Reachable a b) :
    ∃ d, ∃ center : Fin (d+1) ↪ U, d = (separatorCompatibility K R).dist a b ∧
      center 0 = a ∧ center (Fin.last d) = b ∧
      (∀ i : Fin d, K.Adj (center i.castSucc) (center i.succ) ∨
        (R (center i.castSucc) ∩ R (center i.succ)).Nonempty) ∧
      (∀ i j : Fin (d+1), i.val + 1 < j.val →
        ¬ K.Adj (center i) (center j) ∧ Disjoint (R (center i)) (R (center j))) := by
  obtain ⟨d, center, hd, ha, hb, hstep, hno⟩ := shortest_indexed_connector hr
  refine ⟨d,center,hd,ha,hb,fun i => (hstep i).2, ?_⟩
  intro i j hij
  have hne : center i ≠ center j := fun h => by
    have hv : i.val = j.val := congrArg Fin.val (center.injective h)
    omega
  refine ⟨fun h => hno i j hij ⟨hne,Or.inl h⟩, ?_⟩
  apply Finset.disjoint_left.mpr
  intro c hc h'c
  exact hno i j hij ⟨hne,Or.inr ⟨c, Finset.mem_inter.mpr ⟨hc,h'c⟩⟩⟩

/-- A component label shared by the ends of one connector edge occurs in
no other center's row. -/
theorem connector_label_absent_other_center {U C : Type*} {d : ℕ}
    (center : Fin (d+1) → U) (R : U → Finset C)
    (hdisj : ∀ i j : Fin (d+1), i.val + 1 < j.val →
      Disjoint (R (center i)) (R (center j)))
    {i : Fin d} {j : Fin (d+1)} {c : C}
    (hL : c ∈ R (center i.castSucc)) (hR : c ∈ R (center i.succ))
    (hLj : j ≠ i.castSucc) (hRj : j ≠ i.succ) : c ∉ R (center j) := by
  intro hj
  have hLne : j.val ≠ i.val := fun h => hLj (Fin.ext h)
  have hRne : j.val ≠ i.val+1 := fun h => hRj (Fin.ext h)
  by_cases h : j.val < i.val
  · exact Finset.disjoint_left.mp (hdisj j i.succ (by change j.val+1 < i.val+1; omega)) hj hR
  · exact Finset.disjoint_left.mp (hdisj i.castSucc j (by change i.val+1 < j.val; omega)) hL hj

/-- The shared component labels used on different consecutive edges must
be distinct, regardless of how the labels were chosen. -/
theorem connector_labels_distinct {U C : Type*} {d : ℕ}
    (center : Fin (d+1) → U) (R : U → Finset C)
    (hdisj : ∀ i j : Fin (d+1), i.val + 1 < j.val →
      Disjoint (R (center i)) (R (center j)))
    {i j : Fin d} (hij : i ≠ j) {c : C}
    (hiL : c ∈ R (center i.castSucc)) (hiR : c ∈ R (center i.succ))
    (hjL : c ∈ R (center j.castSucc)) (hjR : c ∈ R (center j.succ)) : False := by
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · exact Finset.disjoint_left.mp (hdisj i.castSucc j.succ (by change i.val+1 < j.val+1; omega))
      hiL hjR
  · exact Finset.disjoint_left.mp (hdisj j.castSucc i.succ (by change j.val+1 < i.val+1; omega))
      hjL hiR

#print axioms shortest_indexed_connector
#print axioms connector_dist_ge_three
#print axioms separator_shortest_connector
#print axioms connector_label_absent_other_center
#print axioms connector_labels_distinct

end Graph199
