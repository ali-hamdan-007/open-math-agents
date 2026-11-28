import Graph189MatchedMetric
import Graph189MatchedPack
import Graph189RootedTrace

namespace Graph189MatchedRooted
open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

private theorem score_bound {k e t ε : ℕ} (hsmall : 2*e+1 ≤ k) (hfit : t+ε ≤ e) :
    Graph189MatchedPack.score k t + ε ≤ Graph189MatchedPack.score k e := by
  by_cases he : t = e
  · have hz : ε = 0 := by omega
    simp [he,hz]
  · have hm := mul_nonneg (show 0 ≤ (e : ℤ)-t by omega)
      (show 0 ≤ (k : ℤ)-e-t-2 by omega)
    have hε : (ε : ℤ) ≤ (e : ℤ)-t := by omega
    unfold Graph189MatchedPack.score
    nlinarith only [hm,hε]

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Nontrivial V] in
private theorem rooted_local_ore_distinct (hc : G.Connected) (z : V)
    (ore : ∀ {u w v : V}, u ≠ z → v ≠ z → u ≠ v → G.Adj u w → G.Adj w v → ¬G.Adj u v →
      (G.neighborFinset u ∪ G.neighborFinset w ∪ G.neighborFinset v).card ≤
        G.degree u + G.degree v) :
    ∃ v, ∃ p : G.Walk z v, p.IsHamiltonian := by
  obtain ⟨v,P,hp,longest⟩ := Graph189RootedPath.exists_rooted_longest G z
  refine ⟨v,P,hp.isHamiltonian_iff.mpr ?_⟩
  intro x
  by_contra hx
  obtain ⟨u,hu,hcP⟩ := Graph189RootedPath.exists_exterior_contact P hc ⟨x,hx⟩
  obtain ⟨W,succ,hn,hi,ht,hm,ha,hc',hs,huz⟩ :=
    Graph189RootedPath.successors_of_rooted_longest P hp longest hu hcP
  obtain ⟨w,hw,hbad⟩ := Graph189RootedOreCount.bad_wedge_of_successors u W succ hn hi ht hm ha hc'
  have hne : u ≠ succ w := (hm _ hw).1.symm
  exact (not_lt_of_ge (ore huz (hs _ hw).2 hne (ht _ hw) (hs _ hw).1 (hm _ hw).2)) hbad

private theorem of_score_bound (hc : G.Connected)
    (hcap : (univ.image (distEven G)).max' (by simp) ≤ 1 + G.secondSmallestDegree)
    (bound : ℤ)
    (hscore : ∀ t ε : ℕ, t+ε ≤ G.maxDegree-G.secondSmallestDegree →
      Graph189MatchedPack.score G.secondSmallestDegree t + ε ≤ bound)
    (horder : 3*(G.secondSmallestDegree : ℤ)+1+bound < Fintype.card V) :
    ∃ z, G.degree z = G.minDegree ∧ ∃ v, ∃ p : G.Walk z v, p.IsHamiltonian := by
  classical
  let k := G.secondSmallestDegree
  let e := G.maxDegree-k
  let n := Fintype.card V
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  have high (u : V) (hu : u ≠ z) : k ≤ G.degree u := by
    rcases degree_pair (G := G) u z hu with h|h
    · exact h
    · exact h.trans (hz ▸ G.minDegree_le_degree u)
  have cap (v : V) : G.distEven v ≤ 1+k :=
    (le_max' _ _ (mem_image_of_mem (distEven G) (mem_univ v))).trans hcap
  refine ⟨z,hz.symm,rooted_local_ore_distinct hc z ?_⟩
  intro u w v hu hv hneq huw hwv _
  let U := (G.neighborFinset w ∪ (G.neighborFinset u ∪ G.neighborFinset v)).card
  by_contra hlocal
  have bad : G.degree u + G.degree v + 1 ≤ U := by
    have hp := Nat.lt_of_not_ge hlocal
    have hp' : G.degree u + G.degree v < U := by
      dsimp only [U]
      simpa only [Finset.union_assoc,Finset.union_left_comm,Finset.union_comm] using hp
    omega
  obtain ⟨t,ε,_,hbudget,hbound⟩ :=
    Graph189MatchedWedge.wedge_order_graph189 hc huw.symm hwv hneq cap
  change t+ε+U ≤ G.degree w+G.distEven w at hbudget
  change n+U+t*(t+1) ≤ 3*k+2+G.degree u+G.degree v+t*k+ε at hbound
  have hw := G.degree_le_maxDegree w
  have hku := high u hu
  have hkv := high v hv
  have hkmax := hku.trans (G.degree_le_maxDegree u)
  have hcw := cap w
  have hfit : t+ε ≤ e := by dsimp only [e]; omega
  have hs := hscore t ε hfit
  have hboundI : (n : ℤ)+U+(t : ℤ)*((t : ℤ)+1) ≤
      3*k+2+G.degree u+G.degree v+(t : ℤ)*k+ε := by exact_mod_cast hbound
  have hbadI : (G.degree u : ℤ)+G.degree v+1 ≤ U := by exact_mod_cast bad
  change (3*(k : ℤ)+1+bound) < n at horder
  unfold Graph189MatchedPack.score at hs
  nlinarith only [hboundI,hbadI,horder,hs]

/-- The matched rooted order cutoff for the small degree excess tested in the finite replay. -/
theorem of_matched_order (hc : G.Connected)
    (hcap : (univ.image (distEven G)).max' (by simp) ≤ 1 + G.secondSmallestDegree)
    (hsmall : 2*(G.maxDegree-G.secondSmallestDegree)+1 ≤ G.secondSmallestDegree)
    (horder : 3*(G.secondSmallestDegree : ℤ)+1+
      Graph189MatchedPack.score G.secondSmallestDegree (G.maxDegree-G.secondSmallestDegree) < Fintype.card V) :
    ∃ z, G.degree z = G.minDegree ∧ ∃ v, ∃ p : G.Walk z v, p.IsHamiltonian :=
  of_score_bound hc hcap _ (fun _ _ hfit => score_bound hsmall hfit) horder

private theorem score_le_linear {k e t ε : ℕ} (hk : 3 ≤ k) (hfit : t+ε ≤ e) :
    Graph189MatchedPack.score k t + ε ≤ ((k : ℤ)-2)*e := by
  have ht : 0 ≤ (t : ℤ)*((t : ℤ)-1) := by
    by_cases h : t = 0
    · simp [h]
    · exact mul_nonneg (by omega) (by omega)
  have he := mul_nonneg (show 0 ≤ (ε : ℤ) by omega) (show 0 ≤ (k : ℤ)-3 by omega)
  have hs := mul_nonneg (show 0 ≤ (k : ℤ)-2 by omega) (show 0 ≤ (e : ℤ)-t-ε by omega)
  unfold Graph189MatchedPack.score
  nlinarith only [ht,he,hs]

/-- The linear order cutoff with coefficient k−2 at arbitrary degree excess. -/
theorem of_linear_order (hc : G.Connected)
    (hcap : (univ.image (distEven G)).max' (by simp) ≤ 1 + G.secondSmallestDegree)
    (hk : 3 ≤ G.secondSmallestDegree)
    (horder : 3*(G.secondSmallestDegree : ℤ)+1+((G.secondSmallestDegree : ℤ)-2)*
      ((G.maxDegree-G.secondSmallestDegree : ℕ) : ℤ) < Fintype.card V) :
    ∃ z, G.degree z = G.minDegree ∧ ∃ v, ∃ p : G.Walk z v, p.IsHamiltonian :=
  of_score_bound hc hcap _ (fun _ _ hfit => score_le_linear hk hfit) horder

#print axioms of_matched_order
#print axioms of_linear_order
end Graph189MatchedRooted
