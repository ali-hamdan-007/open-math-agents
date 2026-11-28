import Graph189FiveCycleRing
import Graph189FiveCycleSpanning

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189FiveCycleSixData
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b r : V}

omit [Fintype V] [Nontrivial V] [DecidableRel G.Adj] in
theorem two_marks (p : G.Walk a b) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (C : G.Walk r r) (hc : C.IsCycle) (off : ∀ v∈C.support,v∉p.support)
    {u v : V} (uv : s(u,v)∈C.edges) {i j : ℕ}
    (im : i∈contactPositions p u) (jm : j∈contactPositions p v) (ne : i≠j) :
    (C.length≤ i ∧ i+1+C.length≤j ∧ j+1+C.length≤p.support.length) ∨
    (C.length≤j ∧ j+1+C.length≤ i ∧ i+1+C.length≤p.support.length) := by
  obtain ⟨li,ci⟩ := (mem_contactPositions _ _ _).mp im
  obtain ⟨lj,cj⟩ := (mem_contactPositions _ _ _).mp jm
  let I : Fin p.support.length := ⟨i,li⟩
  let K : Fin p.support.length := ⟨j,lj⟩
  have l : G.Adj p.support[I.val] u := by simpa only [I,get_at] using ci
  have h : G.Adj p.support[K.val] v := by simpa only [K,get_at] using cj
  rcases lt_or_gt_of_ne ne with before|after
  · exact Or.inl (Graph189CycleEdgeMarks.positions p hp mx C hc off uv (show I<K from before) l h)
  · exact Or.inr (Graph189CycleEdgeMarks.positions p hp mx C hc off (Sym2.eq_swap ▸ uv) (show K<I from after) h l)

theorem data (hcG : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (degree : G.secondSmallestDegree=6) (conn : 2≤G.vertexConnectivity) (minimum : ∀ v, 3≤G.degree v)
    (p : G.Walk a b) (hp : p.IsPath) (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (C : G.Walk r r) (hc : C.IsCycle) (five : C.length=5) (off : ∀ v∈C.support,v∉p.support)
    (size : p.support.toFinsetᶜ.card=6) :
    ∃ w, w∉p.support ∧ w∉C.support ∧ insert w C.support.toFinset=p.support.toFinsetᶜ ∧
      G.degree w<6 ∧ (∀ v∈C.support, 6≤G.degree v) ∧
      (G.neighborFinset w\p.support.toFinset)=(G.neighborFinset w∩C.support.toFinset) ∧
      (G.neighborFinset w\p.support.toFinset).card≤2 ∧
      (∀ v∈C.support, 1≤(contactPositions p v).card) ∧
      (∀ v∈C.support, ¬G.Adj w v → 2≤(contactPositions p v).card) ∧
      17≤p.support.length ∧ 23≤Fintype.card V ∧ 4≤G.degree w ∧
      (univ.filter (fun v => G.dist w v=2)).card≤6 := by
  classical
  let E := p.support.toFinsetᶜ
  let W := C.support.toFinset
  have inc : W⊆E := fun v hv => mem_compl.mpr fun h => off v (List.mem_toFinset.mp hv) (List.mem_toFinset.mp h)
  have wc : W.card=5 := (Graph189SixCycleExtra.cycle_card C hc).trans five
  change E.card=6 at size
  obtain ⟨w,hw⟩ := card_pos.mp (show 0<(E\W).card by rw [card_sdiff_of_subset inc,size,wc]; decide)
  obtain ⟨we,wc'⟩ := mem_sdiff.mp hw
  have wp : w∉p.support := fun h => (mem_compl.mp we) (List.mem_toFinset.mpr h)
  have wC : w∉C.support := fun h => wc' (List.mem_toFinset.mpr h)
  have cover : insert w W=E := eq_of_subset_of_card_le (insert_subset we inc)
    (by rw [card_insert_of_notMem wc',wc,size])
  have our : G.neighborFinset w\p.support.toFinset=G.neighborFinset w∩W := by
    ext v
    constructor
    · intro hv
      obtain ⟨nb,np⟩ := mem_sdiff.mp hv
      have ve : v∈E := mem_compl.mpr np
      rw [←cover] at ve
      exact mem_inter.mpr ⟨nb,(mem_insert.mp ve).resolve_left ((G.mem_neighborFinset _ _).mp nb).ne.symm⟩
    · intro hv
      obtain ⟨nb,vc⟩ := mem_inter.mp hv
      exact mem_sdiff.mpr ⟨nb,mem_compl.mp (inc vc)⟩
  obtain ⟨two,u,v,uv,wu,wv⟩ := Graph189FiveCycleRing.outside_neighbors hcG cap degree conn p hp mx C hc five off wp wC
  have tw : (G.neighborFinset w\p.support.toFinset).card≤2 := by rw [our]; exact two
  have point (v : V) : G.distEven v≤7 := by
    have n := (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
    omega
  have quota : (univ.filter (fun v => G.dist w v=2)).card≤6 := by
    let S := univ.filter (fun v => G.dist w v=2)
    have inc : insert w S⊆univ.filter (fun v => Even (G.dist w v)) := by
      intro v h
      rcases mem_insert.mp h with rfl|h
      · simp
      · exact mem_filter.mpr ⟨mem_univ _,by simp [(mem_filter.mp h).2]⟩
    have n := card_le_card inc
    rw [card_insert_of_notMem (by simp [S])] at n
    change S.card+1≤G.distEven w at n
    exact Nat.le_of_succ_le_succ (n.trans (point w))
  have low : G.degree w<6 := by
    by_contra! high
    have half := (high_exterior_half p hp mx wp quota high minimum
      (fun a b la lb => by
        by_contra ne
        have pair := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) a b ne
        omega)).2
    omega
  have high (v : V) (cv : v∈C.support) : 6≤G.degree v := by
    have ne : v≠w := fun e => wC (e ▸ cv)
    have pair := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) v w ne
    omega
  have count (v : V) : (G.neighborFinset v\p.support.toFinset).card+(contactPositions p v).card=G.degree v := by
    rw [contact_card_neighbors p hp,←G.card_neighborFinset_eq_degree]
    exact card_sdiff_add_card_inter _ _
  have neighborhood (v : V) (cv : v∈C.support) : G.neighborFinset v\p.support.toFinset⊆E.erase v := by
    intro x hx
    obtain ⟨vx,np⟩ := mem_sdiff.mp hx
    exact mem_erase.mpr ⟨((G.mem_neighborFinset _ _).mp vx).ne.symm,mem_compl.mpr np⟩
  have positive (v : V) (cv : v∈C.support) : 1≤(contactPositions p v).card := by
    have n := card_le_card (neighborhood v cv)
    rw [card_erase_of_mem (inc (List.mem_toFinset.mpr cv)),size] at n
    have := high v cv
    have := count v
    omega
  have rich (v : V) (cv : v∈C.support) (notw : ¬G.Adj w v) : 2≤(contactPositions p v).card := by
    have sub : G.neighborFinset v\p.support.toFinset⊆(E.erase v).erase w := by
      intro y hy
      have e := (G.mem_neighborFinset _ _).mp (mem_sdiff.mp hy).1
      exact mem_erase.mpr ⟨fun eq => notw (eq ▸ e).symm,neighborhood v cv hy⟩
    have dif : w≠v := fun e => wC (e ▸ cv)
    have n := card_le_card sub
    rw [card_erase_of_mem (mem_erase.mpr ⟨dif,we⟩),card_erase_of_mem (inc (List.mem_toFinset.mpr cv)),size] at n
    have := high v cv
    have := count v
    omega
  have ru := rich u (C.fst_mem_support_of_mem_edges uv) wu
  have rv := rich v (C.snd_mem_support_of_mem_edges uv) wv
  obtain ⟨i,im⟩ := card_pos.mp (show 0<(contactPositions p u).card by omega)
  obtain ⟨j,jm,ne⟩ := exists_mem_ne (show 1<(contactPositions p v).card by omega) i
  have spread := two_marks p hp mx C hc off uv im jm ne.symm
  have pop := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at pop
  change p.support.length+E.card=Fintype.card V at pop
  have n := Graph189QuadraticOrder.rooted hcG w 6 point
  exact ⟨w,wp,wC,cover,low,high,our,tw,positive,rich,by omega,by omega,by omega,quota⟩

#print axioms data
end Graph189FiveCycleSixData
