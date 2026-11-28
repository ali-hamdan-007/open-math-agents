import Graph189FiveCycleSixData
import Graph189MidpointExchange
import Graph189DoubleExteriorShift

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189FiveCycleIsolated
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- If the sixth omission has no neighbor outside the path, the path
can exchange a midpoint for this unique low vertex. The same six-omission
classification on the resulting longest path yields a second low vertex. -/
theorem excluded (hcG : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (degree : G.secondSmallestDegree=6) (conn : 2≤G.vertexConnectivity) (minimum : ∀ v, 3≤G.degree v)
    {a b r : V} (p : G.Walk a b) (hp : p.IsPath) (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (C : G.Walk r r) (hc : C.IsCycle) (five : C.length=5) (off : ∀ v∈C.support,v∉p.support)
    (size : p.support.toFinsetᶜ.card=6) {w : V} (wp : w∉p.support) (wc : w∉C.support)
    (high : 4≤G.degree w) (low : G.degree w<6) (isolated : G.neighborFinset w\p.support.toFinset=∅)
    (quota : (univ.filter (fun v => G.dist w v=2)).card≤6) : False := by
  classical
  have count := card_sdiff_add_card_inter (G.neighborFinset w) p.support.toFinset
  rw [isolated,card_empty,zero_add,G.card_neighborFinset_eq_degree,←contact_card_neighbors p hp] at count
  have pair : ∃ i, i∈contactPositions p w ∧ i+2∈contactPositions p w := by
    by_contra! none
    have disjoint (i : ℕ) (im : i∈contactPositions p w) (j : ℕ) (jm : j∈contactPositions p w)
        (lt : i<j) : i+3≤j := by
      obtain ⟨ii,ci⟩ := (mem_contactPositions p w i).mp im
      obtain ⟨jj,cj⟩ := (mem_contactPositions p w j).mp jm
      have step := omitted_contact_spacing p hp mx wp ⟨i,ii⟩ ⟨j,jj⟩ (show (⟨i,ii⟩:Fin p.support.length)<⟨j,jj⟩ from lt)
        (by simpa only [get_at] using ci) (by simpa only [get_at] using cj)
      change i+2≤j at step
      have ne : i+2≠j := fun eq => none i im (eq ▸ jm)
      omega
    have bound := double_positions_le_path_shell p hp mx wp disjoint
    have inc : p.support.toFinset.filter (fun v => G.dist w v=2)⊆univ.filter (fun v => G.dist w v=2) := by
      intro v hv
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv).2⟩
    have n := (card_le_card inc).trans quota
    omega
  obtain ⟨i,im,jm⟩ := pair
  obtain ⟨_,ci⟩ := (mem_contactPositions p w i).mp im
  obtain ⟨jj,cj⟩ := (mem_contactPositions p w (i+2)).mp jm
  obtain ⟨u,v,q,hq,eq,supp⟩ := swap_contact_midpoint p hp wp i jj ci cj
  have contains : w∈q.support := List.mem_toFinset.mp (supp ▸ mem_insert_self _ _)
  have outside (v : V) (cv : v∈C.support) : v∉q.support := by
    intro h
    have mem := List.mem_toFinset.mpr h
    rw [supp] at mem
    rcases mem_insert.mp mem with rfl|e
    · exact wc cv
    · exact off _ cv (List.mem_toFinset.mp (mem_erase.mp e).2)
  have pn := card_add_card_compl p.support.toFinset
  have qn := card_add_card_compl q.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at pn
  rw [List.toFinset_card_of_nodup hq.support_nodup] at qn
  have ps := p.length_support
  have qs := q.length_support
  obtain ⟨v,vq,_,_,small,_⟩ := Graph189FiveCycleSixData.data hcG cap degree conn minimum q hq
    (fun t ht => eq ▸ mx t ht) C hc five outside (by omega)
  have distinct : v≠w := fun e => vq (e ▸ contains)
  have high := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) v w distinct
  omega

#print axioms excluded
end Graph189FiveCycleIsolated
