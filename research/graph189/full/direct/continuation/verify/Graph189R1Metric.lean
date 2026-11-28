import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Degrees
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
open SimpleGraph
open scoped BigOperators
namespace OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma degree_pair [DecidableRel G.Adj] [Nontrivial V] (x y : V) (hne : x ≠ y) :
    secondSmallestDegree G ≤ G.degree x ∨ secondSmallestDegree G ≤ G.degree y := by
  classical
  let ds := degreeSequence G
  have hlen : 2 ≤ ds.length := by
    simpa [ds, degreeSequence] using Nat.succ_le_of_lt (Fintype.one_lt_card (α := V))
  obtain ⟨a,b,l,heq⟩ : ∃ a b l, ds = a :: b :: l := by
    cases h : ds with
    | nil => simp [h] at hlen
    | cons a tail =>
      cases hh : tail with
      | nil => simp [h, hh] at hlen
      | cons b l => exact ⟨a,b,l,rfl⟩
  have hs : ds.Pairwise (· ≤ ·) := by simp [ds, degreeSequence]
  rw [heq] at hs
  have hlow : ∀ t ∈ l, b ≤ t := (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1
  have hnil : l.filter (fun t => decide (t < b)) = [] := by
    simpa [List.filter_eq_nil_iff] using hlow
  have hct : (ds.filter (fun t => decide (t < b))).length ≤ 1 := by
    rw [heq]
    by_cases h : a < b <;> simp [h,hnil]
  have hcoeds : (↑ds : Multiset ℕ) = Finset.univ.val.map (fun v : V => G.degree v) := by
    simp [ds, degreeSequence]
  let low := Finset.univ.filter (fun v : V => G.degree v < b)
  have hl : low.card ≤ 1 := by
    change (Multiset.filter (fun t => G.degree t < b) Finset.univ.val).card ≤ 1
    have hct' : (Multiset.filter (fun t => t < b) (↑ds : Multiset ℕ)).card ≤ 1 := hct
    rw [hcoeds, Multiset.filter_map, Multiset.card_map] at hct'
    exact hct'
  have hb : secondSmallestDegree G = b := by
    change ds.getD 1 0 = b
    simp [heq] 
  rw [hb]
  by_contra! h
  exact hne (Finset.card_le_one.mp hl x (by simpa [low] using h.1) y (by simpa [low] using h.2))

lemma geodesic (hc : G.Connected) {a b : V} (p : G.Walk a b) (hp : p.length = G.dist a b)
    (i j : ℕ) (hle : i ≤ j) (hj : j ≤ p.length) :
    G.dist (p.getVert i) (p.getVert j) = j - i := by
  have hseg := dist_le ((p.drop i).take (j-i))
  rw [Walk.take_length, Walk.drop_length, Walk.drop_getVert, Nat.add_sub_of_le hle] at hseg
  have hfirst := dist_le (p.take i)
  have hlast := dist_le (p.drop j)
  rw [Walk.take_length] at hfirst
  rw [Walk.drop_length] at hlast
  have ht1 := hc.dist_triangle (u := a) (v := p.getVert i) (w := p.getVert j)
  have ht2 := hc.dist_triangle (u := a) (v := p.getVert j) (w := b)
  omega

lemma order_bound [Nonempty V] [DecidableRel G.Adj] (hc : G.Connected)
    (hb : ∀ x, distEven G x ≤ 1 + G.secondSmallestDegree) :
    Fintype.card V ≤ (G.minDegree + 1) * (G.secondSmallestDegree + 1) := by
  classical
  obtain ⟨r,hr⟩ := G.exists_minimal_degree_vertex
  let B := insert r (G.neighborFinset r)
  let E (x : V) := Finset.univ.filter (fun y => Even (G.dist x y))
  have hcover : Finset.univ ⊆ B.biUnion E := by
    intro x _
    apply Finset.mem_biUnion.mpr
    by_cases h : Even (G.dist r x)
    · exact ⟨r, Finset.mem_insert_self _ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
    · obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist r x
      rw [Nat.even_iff] at h
      have hl : 1 ≤ p.length := by omega
      have ha := geodesic hc p hp 0 1 (by decide) hl
      rw [p.getVert_zero] at ha
      have hx := geodesic hc p hp 1 p.length hl (le_refl _)
      rw [p.getVert_length] at hx
      refine ⟨p.getVert 1, Finset.mem_insert_of_mem ((G.mem_neighborFinset _ _).mpr
        (dist_eq_one_iff_adj.mp ha)), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      rw [Nat.even_iff]
      omega
  have hsize : B.card = G.minDegree + 1 := by
    simp only [B, Finset.card_insert_of_notMem (G.notMem_neighborFinset_self _),
      card_neighborFinset_eq_degree, hr]
  calc
    Fintype.card V = (Finset.univ : Finset V).card := Finset.card_univ.symm
    _ ≤ (B.biUnion E).card := Finset.card_le_card hcover
    _ ≤ B.card * (G.secondSmallestDegree + 1) := Finset.card_biUnion_le_card_mul _ _ _ fun x _ =>
      by simpa only [E,distEven,Nat.add_comm 1] using hb x
    _ = _ := by rw [hsize]

private def closedIndicator (n : ℕ) : ℕ := if n ≤ 1 then 1 else 0

private def evenIndicator (n : ℕ) : ℕ := if n % 2 = 0 then 1 else 0

lemma dist_le_one_count [DecidableRel G.Adj] (hc : G.Connected) (x : V) :
    (∑ y : V, (if G.dist x y ≤ 1 then 1 else 0 : ℕ)) = G.degree x + 1 := by
  classical
  rw [← Finset.card_filter]
  have he : Finset.univ.filter (fun y => G.dist x y ≤ 1) = insert x (G.neighborFinset x) := by
    ext y
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,mem_neighborFinset]
    constructor
    · intro hd
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with h | h
      · exact Or.inl ((hc.dist_eq_zero_iff.mp h).symm)
      · exact Or.inr (dist_eq_one_iff_adj.mp h)
    · rintro (rfl | h)
      · simp
      · exact (dist_eq_one_iff_adj.mpr h).le
  rw [he,Finset.card_insert_of_notMem (G.notMem_neighborFinset_self _), card_neighborFinset_eq_degree]

section Five
variable (hc : G.Connected) (v : ℕ → V)
variable (hg : ∀ i j : ℕ, i ≤ j → j ≤ 5 → G.dist (v i) (v j) = j-i)

include hc hg in
lemma profile_bounds (y : V) (i j : ℕ) (hi : i ≤ j) (hj : j ≤ 5) :
    G.dist (v i) y ≤ G.dist (v j) y + (j-i) ∧
    G.dist (v j) y ≤ G.dist (v i) y + (j-i) ∧ j-i ≤ G.dist (v i) y + G.dist (v j) y := by
  have h₁ := hc.dist_triangle (u := v i) (v := v j) (w := y)
  have h₂ := hc.dist_triangle (u := v j) (v := v i) (w := y)
  have h₃ := hc.dist_triangle (u := v i) (v := y) (w := v j)
  rw [SimpleGraph.dist_comm (u := v j) (v := v i)] at h₂
  rw [SimpleGraph.dist_comm (u := y) (v := v j)] at h₃
  rw [hg i j hi hj] at h₁ h₂ h₃
  omega

private lemma sum_evenIndicator [DecidableRel G.Adj] (hb : ∀ x, distEven G x ≤ G.secondSmallestDegree + 1) (x : V) :
    ∑ y : V, evenIndicator (G.dist x y) ≤ G.secondSmallestDegree + 1 := by
  classical
  simpa only [evenIndicator,distEven,Finset.card_filter,Nat.even_iff] using hb x

-- A vertex x near the left endpoint and at distance three from both middle vertices
-- has low degree. Its closed neighborhood and those of v₃ and v₅ require more total
-- incidences than the even-distance sets of v₀, v₁ and v₂ can supply.
include hc hg in
lemma low_bad_left [DecidableRel G.Adj]
    (hb : ∀ x, distEven G x ≤ G.secondSmallestDegree + 1)
    (hs3 : G.secondSmallestDegree ≤ G.degree (v 3))
    (hs5 : G.secondSmallestDegree ≤ G.degree (v 5))
    (x : V) (hx0 : G.dist (v 0) x ≤ 1)
    (hx2 : G.dist (v 2) x = 3) (hx3 : G.dist (v 3) x = 3) : G.degree x < G.secondSmallestDegree := by
  classical
  have h5x := profile_bounds hc v hg x 0 5 (by decide) (by decide)
  norm_num1 at h5x
  let B (a y : V) := closedIndicator (G.dist a y)
  let E (i : ℕ) (y : V) := evenIndicator (G.dist (v i) y)
  have hpoint (y : V) : B x y + B (v 3) y + B (v 5) y ≤ E 0 y + E 1 y + E 2 y := by
    have h01 := profile_bounds hc v hg y 0 1 (by decide) (by decide)
    have h12 := profile_bounds hc v hg y 1 2 (by decide) (by decide)
    have h03 := profile_bounds hc v hg y 0 3 (by decide) (by decide)
    have h05 := profile_bounds hc v hg y 0 5 (by decide) (by decide)
    have h23 := profile_bounds hc v hg y 2 3 (by decide) (by decide)
    have h25 := profile_bounds hc v hg y 2 5 (by decide) (by decide)
    have h35 := profile_bounds hc v hg y 3 5 (by decide) (by decide)
    norm_num1 at h01 h12 h03 h05 h23 h25 h35
    have h0 := hc.dist_triangle (u := v 0) (v := x) (w := y)
    have h2 := hc.dist_triangle (u := v 2) (v := y) (w := x)
    have h3 := hc.dist_triangle (u := v 3) (v := y) (w := x)
    have h5 := hc.dist_triangle (u := v 5) (v := y) (w := x)
    rw [SimpleGraph.dist_comm (u := y) (v := x)] at h2 h3 h5
    dsimp only [B,E,closedIndicator,evenIndicator]
    split_ifs <;> omega
  have hstrict : B x (v 0) + B (v 3) (v 0) + B (v 5) (v 0) <
      E 0 (v 0) + E 1 (v 0) + E 2 (v 0) := by
    rw [SimpleGraph.dist_comm] at hx0
    have h1 := hg 0 1 (by decide) (by decide)
    have h2 := hg 0 2 (by decide) (by decide)
    have h3 := hg 0 3 (by decide) (by decide)
    have h5 := hg 0 5 (by decide) (by decide)
    rw [SimpleGraph.dist_comm] at h1 h2 h3 h5
    norm_num [B,E,closedIndicator,evenIndicator,hx0,h1,h2,h3,h5]
  have ht := Finset.sum_lt_sum (s := (Finset.univ : Finset V))
    (f := fun y => B x y + B (v 3) y + B (v 5) y) (g := fun y => E 0 y + E 1 y + E 2 y)
    (fun y _ => hpoint y) ⟨v 0,Finset.mem_univ _,hstrict⟩
  have hB (a : V) : ∑ y : V, B a y = G.degree a + 1 := dist_le_one_count hc a
  have he (i : ℕ) : ∑ y : V, E i y ≤ G.secondSmallestDegree + 1 := sum_evenIndicator hb (v i)
  simp only [Finset.sum_add_distrib,hB] at ht
  have he0 := he 0
  have he1 := he 1
  have he2 := he 2
  omega

include hc hg in
lemma exists_bad [DecidableRel G.Adj] (hb : ∀ x, distEven G x ≤ G.secondSmallestDegree + 1)
    (hs0 : G.secondSmallestDegree ≤ G.degree (v 0)) (hs5 : G.secondSmallestDegree ≤ G.degree (v 5)) :
    ∃ x, (G.dist (v 0) x ≤ 1 ∨ G.dist (v 5) x ≤ 1) ∧
      G.dist (v 2) x = 3 ∧ G.dist (v 3) x = 3 := by
  classical
  let B (i : ℕ) (y : V) := closedIndicator (G.dist (v i) y)
  let E (i : ℕ) (y : V) := evenIndicator (G.dist (v i) y)
  by_contra hno
  have hpoint (y : V) : B 0 y + B 5 y ≤ E 2 y + E 3 y := by
    have hneg : ¬((G.dist (v 0) y ≤ 1 ∨ G.dist (v 5) y ≤ 1) ∧
        G.dist (v 2) y = 3 ∧ G.dist (v 3) y = 3) := fun h => hno ⟨y,h⟩
    have h02 := profile_bounds hc v hg y 0 2 (by decide) (by decide)
    have h03 := profile_bounds hc v hg y 0 3 (by decide) (by decide)
    have h05 := profile_bounds hc v hg y 0 5 (by decide) (by decide)
    have h23 := profile_bounds hc v hg y 2 3 (by decide) (by decide)
    have h25 := profile_bounds hc v hg y 2 5 (by decide) (by decide)
    have h35 := profile_bounds hc v hg y 3 5 (by decide) (by decide)
    norm_num1 at h02 h03 h05 h23 h25 h35
    dsimp only [B,E,closedIndicator,evenIndicator]
    split_ifs <;> omega
  have hstrict : B 0 (v 2) + B 5 (v 2) < E 2 (v 2) + E 3 (v 2) := by
    have h0 := hg 0 2 (by decide) (by decide)
    have h3 := hg 2 3 (by decide) (by decide)
    have h5 := hg 2 5 (by decide) (by decide)
    rw [SimpleGraph.dist_comm] at h3 h5
    norm_num [B,E,closedIndicator,evenIndicator,h0,h3,h5]
  have ht := Finset.sum_lt_sum (s := (Finset.univ : Finset V))
    (f := fun y => B 0 y + B 5 y) (g := fun y => E 2 y + E 3 y)
    (fun y _ => hpoint y) ⟨v 2,Finset.mem_univ _,hstrict⟩
  have hB (i : ℕ) : ∑ y : V, B i y = G.degree (v i) + 1 := dist_le_one_count hc (v i)
  have he (i : ℕ) : ∑ y : V, E i y ≤ G.secondSmallestDegree + 1 := sum_evenIndicator hb (v i)
  simp only [Finset.sum_add_distrib,hB] at ht
  have he2 := he 2
  have he3 := he 3
  omega

-- With four high-degree path vertices, a closed endpoint neighborhood contains a
-- vertex at distance three from both middle vertices. Otherwise the two even-distance
-- sets at v₂ and v₃ cover both closed endpoint neighborhoods with strict excess.
include hc hg in
lemma five_low [DecidableRel G.Adj] (hb : ∀ x, distEven G x ≤ G.secondSmallestDegree + 1)
    (hs : ∀ i ∈ ([0,2,3,5] : List ℕ), G.secondSmallestDegree ≤ G.degree (v i)) :
    ∃ x, G.degree x < G.secondSmallestDegree ∧ G.dist (v 2) x = 3 ∧ G.dist (v 3) x = 3 := by
  obtain ⟨x,hnear,hx2,hx3⟩ := exists_bad hc v hg hb (hs 0 (by decide)) (hs 5 (by decide))
  refine ⟨x,?_,hx2,hx3⟩
  rcases hnear with hn | hn
  · exact low_bad_left hc v hg hb (hs 3 (by decide)) (hs 5 (by decide)) x hn hx2 hx3
  · let w (i : ℕ) := v (5-i)
    have hw (i j : ℕ) (hij : i ≤ j) (hj : j ≤ 5) : G.dist (w i) (w j) = j-i := by
      dsimp only [w]
      rw [SimpleGraph.dist_comm, hg _ _ (by omega) (by omega)]
      omega
    exact low_bad_left hc w hw hb (hs 2 (by decide)) (hs 0 (by decide)) x hn hx3 hx2

end Five

-- Every geodesic of length five meets the unique low-degree vertex at an endpoint
-- or in one of its two middle positions. The strict excess at both middle vertices
-- cannot be offset by a single low-degree vertex elsewhere.
lemma five_hits_low [Nontrivial V] [DecidableRel G.Adj] (hc : G.Connected)
    (hb : ∀ x, distEven G x ≤ G.secondSmallestDegree + 1) (v : ℕ → V)
    (hg : ∀ i j : ℕ, i ≤ j → j ≤ 5 → G.dist (v i) (v j) = j-i) :
    ∃ i ∈ ([0,2,3,5] : List ℕ), G.degree (v i) < G.secondSmallestDegree := by
  classical
  by_contra! hs
  obtain ⟨x,hx,_,_⟩ := five_low hc v hg hb hs
  have bad (y : V) (hn : G.dist (v 0) y ≤ 1 ∨ G.dist (v 5) y ≤ 1)
      (hy2 : G.dist (v 2) y = 3) (hy3 : G.dist (v 3) y = 3) : y = x := by
    have hy : G.degree y < G.secondSmallestDegree := by
      rcases hn with hn | hn
      · exact low_bad_left hc v hg hb (hs 3 (by decide)) (hs 5 (by decide)) y hn hy2 hy3
      · let w (i : ℕ) := v (5-i)
        have hw (i j : ℕ) (hi : i ≤ j) (hj : j ≤ 5) : G.dist (w i) (w j) = j-i := by
          dsimp only [w]
          rw [SimpleGraph.dist_comm, hg _ _ (by omega) (by omega)]
          omega
        exact low_bad_left hc w hw hb (hs 2 (by decide)) (hs 0 (by decide)) y hn hy3 hy2
    by_contra h
    have h' := degree_pair (G := G) y x h
    omega
  let B (i : ℕ) (y : V) := closedIndicator (G.dist (v i) y)
  let E (i : ℕ) (y : V) := evenIndicator (G.dist (v i) y)
  let I (a y : V) : ℕ := if a = y then 1 else 0
  have hp (y : V) : B 0 y + B 5 y + I (v 2) y + I (v 3) y ≤ E 2 y + E 3 y + I x y := by
    have h02 := profile_bounds hc v hg y 0 2 (by decide) (by decide)
    have h03 := profile_bounds hc v hg y 0 3 (by decide) (by decide)
    have h05 := profile_bounds hc v hg y 0 5 (by decide) (by decide)
    have h23 := profile_bounds hc v hg y 2 3 (by decide) (by decide)
    have h25 := profile_bounds hc v hg y 2 5 (by decide) (by decide)
    have h35 := profile_bounds hc v hg y 3 5 (by decide) (by decide)
    norm_num1 at h02 h03 h05 h23 h25 h35
    by_cases hy2 : v 2 = y
    · have hdist : G.dist (v 2) y = 0 := by rw [hy2]; simp
      have hne : v 3 ≠ y := by
        intro h
        have h' : G.dist (v 3) y = 0 := by rw [h]; simp
        omega
      dsimp only [B,E,I,closedIndicator,evenIndicator]
      split_ifs <;> omega
    by_cases hy3 : v 3 = y
    · have hdist : G.dist (v 3) y = 0 := by rw [hy3]; simp
      dsimp only [B,E,I,closedIndicator,evenIndicator]
      split_ifs <;> omega
    by_cases hyx : x = y
    · dsimp only [B,E,I,closedIndicator,evenIndicator]
      split_ifs <;> omega
    have hno : ¬((G.dist (v 0) y ≤ 1 ∨ G.dist (v 5) y ≤ 1) ∧
        G.dist (v 2) y = 3 ∧ G.dist (v 3) y = 3) := by
      rintro ⟨hn,h2,h3⟩
      exact hyx (bad y hn h2 h3).symm
    dsimp only [B,E,I,closedIndicator,evenIndicator]
    split_ifs <;> omega
  have ht := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun y _ => hp y)
  have hB (i : ℕ) : ∑ y : V, B i y = G.degree (v i) + 1 := dist_le_one_count hc (v i)
  have he (i : ℕ) : ∑ y : V, E i y ≤ G.secondSmallestDegree + 1 := sum_evenIndicator hb (v i)
  have hI (a : V) : ∑ y : V, I a y = 1 := by simp [I]
  simp only [Finset.sum_add_distrib,hB,hI] at ht
  have he2 := he 2
  have he3 := he 3
  have hs0 := hs 0 (by decide)
  have hs5 := hs 5 (by decide)
  omega

section FiveEndpoint

variable [Nontrivial V] [DecidableRel G.Adj] (hc : G.Connected)
    (hb : ∀ x, distEven G x ≤ G.secondSmallestDegree + 1) (v : ℕ → V)
    (hg : ∀ i j : ℕ, i ≤ j → j ≤ 5 → G.dist (v i) (v j) = j-i)

include hc hb hg in
lemma no_triangle_at_low_middle (hs : G.degree (v 2) < G.secondSmallestDegree) (z : V) :
    ¬(G.dist (v 1) z = 1 ∧ G.dist (v 2) z = 1 ∧ G.dist (v 3) z = 1) := by
  rintro ⟨h1,h2,h3⟩
  let w (i : ℕ) := if i = 2 then z else v i
  have hz (i : ℕ) (hi : i ≤ 5) (hi2 : i ≠ 2) :
      G.dist (v i) z = if i ≤ 2 then 2-i else i-2 := by
    have h01 := profile_bounds hc v hg z 0 1 (by decide) (by decide)
    have h03 := profile_bounds hc v hg z 0 3 (by decide) (by decide)
    have h14 := profile_bounds hc v hg z 1 4 (by decide) (by decide)
    have h34 := profile_bounds hc v hg z 3 4 (by decide) (by decide)
    have h15 := profile_bounds hc v hg z 1 5 (by decide) (by decide)
    have h35 := profile_bounds hc v hg z 3 5 (by decide) (by decide)
    norm_num1 at h01 h03 h14 h34 h15 h35
    interval_cases i <;> norm_num1 <;> simp only [if_true,if_false] <;> omega
  have hw (i j : ℕ) (hij : i ≤ j) (hj : j ≤ 5) : G.dist (w i) (w j) = j-i := by
    by_cases hi2 : i = 2
    · subst i
      by_cases hj2 : j = 2
      · subst j
        simp
      · have h := hz j hj hj2
        rw [SimpleGraph.dist_comm] at h
        simp only [w,if_pos rfl,if_neg hj2]
        rw [h,if_neg (by omega)]
    · by_cases hj2 : j = 2
      · subst j
        simpa only [w,if_pos rfl,if_neg hi2,if_pos hij] using hz i (by omega) hi2
      · simpa only [w,if_neg hi2,if_neg hj2] using hg i j hij hj
  obtain ⟨i,hi,hl⟩ := five_hits_low hc hb w hw
  have hne : v 2 ≠ w i := by
    by_cases hi2 : i = 2
    · subst i
      simp only [w,if_pos rfl]
      intro he
      rw [he,SimpleGraph.dist_self] at h2
      omega
    · have hi5 : i ≤ 5 := by simp at hi; omega
      simp only [w,if_neg hi2]
      intro he
      rcases lt_or_gt_of_ne hi2 with h | h
      · have hh := hg i 2 h.le (by decide)
        rw [he,SimpleGraph.dist_self] at hh
        omega
      · have hh := hg 2 i h.le hi5
        rw [he,SimpleGraph.dist_self] at hh
        omega
  have h := degree_pair (G := G) _ _ hne
  omega

private lemma right_cost (d0 d1 d2 d3 d4 d5 t : ℕ)
    (h01 : d0 ≤ d1+1 ∧ d1 ≤ d0+1) (h12 : d1 ≤ d2+1 ∧ d2 ≤ d1+1)
    (h23 : d2 ≤ d3+1 ∧ d3 ≤ d2+1) (h34 : d3 ≤ d4+1 ∧ d4 ≤ d3+1)
    (h45 : d4 ≤ d5+1 ∧ d5 ≤ d4+1) (h05 : 5 ≤ d0+d5)
    (ht : ¬(d1 = 1 ∧ d2 = 1 ∧ d3 = 1)) (h3 : 3 ≤ d3+t) (h5 : d5 ≤ t+1) :
    closedIndicator d0 + closedIndicator d1 + closedIndicator d3 + closedIndicator t ≤
      evenIndicator d2 + evenIndicator d3 + evenIndicator d4 + evenIndicator d5 := by
  unfold closedIndicator evenIndicator
  split_ifs <;> omega

include hc hg hb in
lemma bad_right_middle (hs2 : G.degree (v 2) < G.secondSmallestDegree)
    (hs : ∀ i ∈ ([0,1,3] : List ℕ), G.secondSmallestDegree ≤ G.degree (v i))
    (x : V) (hx5 : G.dist (v 5) x ≤ 1) (hx3 : G.dist (v 3) x = 3) :
    G.degree x < G.secondSmallestDegree := by
  classical
  let B (a y : V) := closedIndicator (G.dist a y)
  let E (i : ℕ) (y : V) := evenIndicator (G.dist (v i) y)
  have hp (y : V) : B (v 0) y + B (v 1) y + B (v 3) y + B x y ≤
      E 2 y + E 3 y + E 4 y + E 5 y := by
    have h01 := profile_bounds hc v hg y 0 1 (by decide) (by decide)
    have h12 := profile_bounds hc v hg y 1 2 (by decide) (by decide)
    have h23 := profile_bounds hc v hg y 2 3 (by decide) (by decide)
    have h34 := profile_bounds hc v hg y 3 4 (by decide) (by decide)
    have h45 := profile_bounds hc v hg y 4 5 (by decide) (by decide)
    have h05 := profile_bounds hc v hg y 0 5 (by decide) (by decide)
    norm_num1 at h01 h12 h23 h34 h45 h05
    have h3 := hc.dist_triangle (u := v 3) (v := y) (w := x)
    rw [SimpleGraph.dist_comm (u := y) (v := x)] at h3
    have h5 := hc.dist_triangle (u := v 5) (v := x) (w := y)
    exact right_cost _ _ _ _ _ _ _ ⟨h01.1,h01.2.1⟩ ⟨h12.1,h12.2.1⟩
      ⟨h23.1,h23.2.1⟩ ⟨h34.1,h34.2.1⟩ ⟨h45.1,h45.2.1⟩ h05.2.2
      (no_triangle_at_low_middle hc hb v hg hs2 y) (by omega) (by omega)
  have hstrict : B (v 0) (v 5) + B (v 1) (v 5) + B (v 3) (v 5) + B x (v 5) <
      E 2 (v 5) + E 3 (v 5) + E 4 (v 5) + E 5 (v 5) := by
    have h0 := hg 0 5 (by decide) (by decide)
    have h1 := hg 1 5 (by decide) (by decide)
    have h2 := hg 2 5 (by decide) (by decide)
    have h3 := hg 3 5 (by decide) (by decide)
    have h4 := hg 4 5 (by decide) (by decide)
    rw [SimpleGraph.dist_comm] at hx5
    norm_num [B,E,closedIndicator,evenIndicator,h0,h1,h2,h3,h4,hx5]
  have ht := Finset.sum_lt_sum (s := (Finset.univ : Finset V))
    (f := fun y => B (v 0) y + B (v 1) y + B (v 3) y + B x y)
    (g := fun y => E 2 y + E 3 y + E 4 y + E 5 y)
    (fun y _ => hp y) ⟨v 5,Finset.mem_univ _,hstrict⟩
  have hB (a : V) : ∑ y : V, B a y = G.degree a + 1 := dist_le_one_count hc a
  have he (i : ℕ) : ∑ y : V, E i y ≤ G.secondSmallestDegree + 1 := sum_evenIndicator hb (v i)
  simp only [Finset.sum_add_distrib,hB] at ht
  have he2 := he 2
  have he3 := he 3
  have he4 := he 4
  have he5 := he 5
  have hs0 := hs 0 (by decide)
  have hs1 := hs 1 (by decide)
  have hs3 := hs 3 (by decide)
  omega

include hc hg hb in
lemma middle_cannot_be_low (hs2 : G.degree (v 2) < G.secondSmallestDegree) : False := by
  have hs (i : ℕ) (hi : i ≤ 5) (hi2 : i ≠ 2) : G.secondSmallestDegree ≤ G.degree (v i) := by
    have hne : v 2 ≠ v i := by
      intro he
      rcases lt_or_gt_of_ne hi2 with h | h
      · have hh := hg i 2 h.le (by decide)
        rw [he,SimpleGraph.dist_self] at hh
        omega
      · have hh := hg 2 i h.le hi
        rw [he,SimpleGraph.dist_self] at hh
        omega
    exact (degree_pair _ _ hne).resolve_left (by omega)
  obtain ⟨x,hn,h2,h3⟩ := exists_bad hc v hg hb (hs 0 (by decide) (by decide)) (hs 5 (by decide) (by decide))
  have hx : G.degree x < G.secondSmallestDegree := by
    rcases hn with h | h
    · exact low_bad_left hc v hg hb (hs 3 (by decide) (by decide)) (hs 5 (by decide) (by decide)) x h h2 h3
    · refine bad_right_middle hc hb v hg hs2 ?_ x h h3
      intro i hi
      simp at hi
      exact hs i (by omega) (by omega)
  have hne : v 2 ≠ x := by
    intro he
    rw [he,SimpleGraph.dist_self] at h2
    omega
  have h := degree_pair (G := G) _ _ hne
  omega

include hc hg hb in
lemma geodesic_five_endpoints :
    G.degree (v 0) < G.secondSmallestDegree ∨ G.degree (v 5) < G.secondSmallestDegree := by
  obtain ⟨i,hi,hl⟩ := five_hits_low hc hb v hg
  simp at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact Or.inl hl
  · exact (middle_cannot_be_low hc hb v hg hl).elim
  · let w (i : ℕ) := v (5-i)
    have hw (i j : ℕ) (hi : i ≤ j) (hj : j ≤ 5) : G.dist (w i) (w j) = j-i := by
      dsimp only [w]
      rw [SimpleGraph.dist_comm, hg _ _ (by omega) (by omega)]
      omega
    exact (middle_cannot_be_low hc hb w hw hl).elim
  · exact Or.inr hl

end FiveEndpoint

lemma five_endpoints [Nontrivial V] [DecidableRel G.Adj] (hc : G.Connected)
    (hb : ∀ x, distEven G x ≤ G.secondSmallestDegree + 1) (a b : V) (hd : G.dist a b = 5) :
    G.degree a < G.secondSmallestDegree ∨ G.degree b < G.secondSmallestDegree := by
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist a b
  have hg (i j : ℕ) (hi : i ≤ j) (hj : j ≤ 5) :
      G.dist (p.getVert i) (p.getVert j) = j-i := geodesic hc p hp _ _ hi (by omega)
  have h := geodesic_five_endpoints hc hb p.getVert hg
  rw [p.getVert_zero,p.getVert_of_length_le (by omega : p.length ≤ 5)] at h
  exact h

lemma diameter_le_five [Nontrivial V] [DecidableRel G.Adj] (hc : G.Connected)
    (hb : ∀ x, distEven G x ≤ 1 + G.secondSmallestDegree) : G.diam ≤ 5 := by
  have hb' : ∀ x, distEven G x ≤ G.secondSmallestDegree + 1 := by
    simpa only [Nat.add_comm 1] using hb
  by_contra! h
  obtain ⟨a,b,hab⟩ := G.exists_dist_eq_diam
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist a b
  let v := p.getVert
  have hg (i j : ℕ) (hi : i ≤ j) (hj : j ≤ 6) :
      G.dist (v i) (v j) = j-i := geodesic hc p hp _ _ hi (by omega)
  have vne (i j : ℕ) (hi : i < j) (hj : j ≤ 6) : v i ≠ v j := by
    intro he
    have h := hg i j hi.le hj
    rw [he,SimpleGraph.dist_self] at h
    omega
  have h05 := five_endpoints hc hb' _ _ (hg 0 5 (by decide) (by decide))
  have h16 := five_endpoints hc hb' _ _ (hg 1 6 (by decide) (by decide))
  have h01 := degree_pair (G := G) _ _ (vne 0 1 (by decide) (by decide))
  have h06 := degree_pair (G := G) _ _ (vne 0 6 (by decide) (by decide))
  have h15 := degree_pair (G := G) _ _ (vne 1 5 (by decide) (by decide))
  have h56 := degree_pair (G := G) _ _ (vne 5 6 (by decide) (by decide))
  omega

end OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
