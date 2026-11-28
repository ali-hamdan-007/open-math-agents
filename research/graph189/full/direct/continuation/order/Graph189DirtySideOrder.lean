import Graph189PrivateSideSize
import Graph189CleanSideCounts
import Graph189FarPrivatePort
import Graph189SoleNearestData

open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189DirtySideOrder
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

/-- When one side has only private contacts, failure of its clean-side
conditions forces the opposite side to have at most 2k−1 vertices. -/
theorem order (hc : G.Connected) (cap : ∀v,G.distEven v≤G.secondSmallestDegree+1)
    (sides : Graph189CutSides.CutSides G A B S) (pair : S={p,q}) (ne : p≠q)
    (sc : S.card≤G.vertexConnectivity) (con : (G.induce (A:Set V)).Connected)
    (privateA : ∀x∈A,¬(G.Adj x p ∧ G.Adj x q))
    (dirty : ¬Graph189CleanSideCounts.Clean G A p q) : B.card+1≤2*G.secondSmallestDegree := by
  classical
  by_contra tooMany
  apply dirty
  have ps : p∈S := by simp [pair]
  have qs : q∈S := by simp [pair]
  have sz : S.card=2 := by simp [pair,ne]
  have contact (i : V) (si : i∈S) := (sides.contacts_of_minimum (fun T h =>
    Graph189CutSides.connected_after_smaller_deletion (G:=G) T (h.trans_le sc)) si).1
  have farPort {i j : V} (pair' : S={i,j}) (ij : i≠j)
      (free : ∀x∈A,¬(G.Adj x i ∧ G.Adj x j))
      {x : V} (xa : x∈A) (high : G.secondSmallestDegree≤G.degree x) (xi : G.Adj x i) :
      G.dist j x=2 := by
    have js : j∈S := by simp [pair']
    have noZero : G.dist j x≠0 := fun h => Finset.disjoint_left.mp sides.left_cut xa
      ((hc.dist_eq_zero_iff.mp h) ▸ js)
    have noOne : G.dist j x≠1 := fun h => free x xa ⟨xi,(dist_eq_one_iff_adj.mp h).symm⟩
    by_contra nt
    obtain ⟨v,va,vj⟩ := contact j js
    exact tooMany (Graph189FarPrivatePort.order hc sides con pair' ij sc cap xa xi (by
      rw [G.dist_comm (u:=x) (v:=j)]; omega) high ⟨v,va,fun iv => free v va ⟨iv.symm,vj⟩⟩)
  have nonport {x : V} (xa : x∈A) (high : G.secondSmallestDegree≤G.degree x)
      (xp : G.dist p x≠1) (xq : G.dist q x≠1) : G.dist p x=2 ∧ G.dist q x=2 := by
    have pos (i : V) (si : i∈S) : G.dist i x≠0 := fun h => Finset.disjoint_left.mp sides.left_cut xa
      ((hc.dist_eq_zero_iff.mp h) ▸ si)
    have dp := pos p ps
    have dq := pos q qs
    have meet : G.dist p x=2 ∨ G.dist q x=2 := by
      by_contra! miss
      have low := Graph189PrivateSideSize.far_low_of_size hc cap sides.swap pair ne sc (by omega) xa (by omega) (by omega)
      omega
    have sole {i : V} (w : Graph189SoleNearestSides.Witness G A S x i) : False := by
      obtain ⟨ports,remote⟩ := Graph189SoleNearestSides.debit hc sides sc cap w
      rw [sz] at ports remote
      let H := B.filter (fun y => G.secondSmallestDegree≤G.degree y)
      have pop := card_filter_add_card_filter_not (s:=H) (p:=G.Adj i)
      have marked := card_le_card (filter_subset_filter (G.Adj i) (show H⊆B from filter_subset _ _))
      have lowCount : (B\H).card≤1 := by
        apply card_le_one.mpr
        intro u hu v hv
        by_contra diff
        exact (degree_pair (G:=G) u v diff).elim
          (fun uh => (mem_sdiff.mp hu).2 (mem_filter.mpr ⟨(mem_sdiff.mp hu).1,uh⟩))
          (fun vh => (mem_sdiff.mp hv).2 (mem_filter.mpr ⟨(mem_sdiff.mp hv).1,vh⟩))
      have total := card_sdiff_add_card_eq_card (show H⊆B from filter_subset _ _)
      change (H.filter (fun t => ¬G.Adj i t)).card+2≤G.secondSmallestDegree at remote
      omega
    have noport (i : V) (si : i∈S) (e : G.Adj i x) : False := by
      have h := dist_eq_one_iff_adj.mpr e
      rcases (show i=p ∨ i=q by simpa [pair] using si) with ip|iq
      · exact xp (ip ▸ h)
      · exact xq (iq ▸ h)
    by_contra fail
    rcases meet with hp|hq
    · apply sole (i:=p) ⟨xa,ps,high,noport,hp,?_⟩
      intro j js metric
      rcases (show j=p ∨ j=q by simpa [pair] using js) with e|e
      · exact e.symm
      · exact (fail ⟨hp,e ▸ metric⟩).elim
    · apply sole (i:=q) ⟨xa,qs,high,noport,hq,?_⟩
      intro j js metric
      rcases (show j=p ∨ j=q by simpa [pair] using js) with e|e
      · exact (fail ⟨e ▸ metric,hq⟩).elim
      · exact e.symm
  refine ⟨privateA,?_,fun x xa hi xp xq => nonport xa hi xp xq⟩
  intro x xa hi
  by_cases xp : G.Adj p x
  · exact Or.inr (farPort pair ne privateA xa hi xp.symm)
  by_cases xq : G.Adj q x
  · exact Or.inl (farPort (i:=q) (j:=p) (by simpa [Finset.pair_comm] using pair) ne.symm
      (fun y ya h => privateA y ya h.symm) xa hi xq.symm)
  exact Or.inl (nonport xa hi (fun e => xp (dist_eq_one_iff_adj.mp e))
    (fun e => xq (dist_eq_one_iff_adj.mp e))).1

#print axioms order
end Graph189DirtySideOrder
