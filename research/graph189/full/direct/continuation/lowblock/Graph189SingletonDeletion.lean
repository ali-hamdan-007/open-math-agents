import Graph189IndependentExterior
import Graph189DoubleExteriorShift
import Graph189MidpointExchange

namespace Graph189ExteriorDegreeCycle
open Finset SimpleGraph Graph189ExteriorGap
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

/-- Inserting two omitted vertices across one actual path edge. -/
private theorem insert_two {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v a b : V}
    (p : G.Walk u v) (hp : p.IsPath) (i : ℕ) (valid : i+1 < p.support.length)
    (ha : a ∉ p.support) (hb : b ∉ p.support) (ab : G.Adj a b)
    (first : G.Adj (p.getVert i) a) (last : G.Adj b (p.getVert (i+1)))
    (covers : ∀ z, z=a ∨ z=b ∨ z ∈ p.support) :
    ∃ x y, ∃ q : G.Walk x y, q.IsHamiltonian := by
  let A := p.support.take (i+1)
  let B := p.support.drop (i+1)
  have pl : p.support=A++B := (List.take_append_drop _ _).symm
  have nd := hp.support_nodup
  have chain := p.isChain_adj_support
  rw [pl] at nd chain ha hb
  have front : i < p.support.length := by omega
  have la : A.getLast? = some p.support[i] :=
    (congrArg List.getLast? (List.take_succ_eq_append_getElem front)).trans List.getLast?_concat
  have fb : B.head? = some p.support[i+1] := by simp [B,List.head?_drop]
  have ca : (A++[a,b]).IsChain G.Adj := by
    apply chain.left_of_append.append (by simp [ab])
    intro z hz w hw
    rw [la] at hz
    have zz : p.support[i]=z := by simpa using hz
    have ww : a=w := by simpa using hw
    subst w
    exact zz ▸ (by simpa [get_at] using first)
  let L := (A++[a,b])++B
  have ch : L.IsChain G.Adj := by
    apply ca.append chain.right_of_append
    intro z hz w hw
    have zz : b=z := by simpa [List.getLast?_append] using hz
    rw [fb] at hw
    have ww : p.support[i+1]=w := by simpa using hw
    subst z
    exact ww ▸ (by simpa [get_at] using last)
  have new : L.Nodup := by
    refine List.Nodup.append ?_ nd.of_append_right ?_
    · apply List.Nodup.append nd.of_append_left (by simp [ab.ne])
      apply List.disjoint_left.mpr
      intro z hz hz'
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz'
      rcases hz' with rfl|rfl
      · exact ha (List.mem_append_left _ hz)
      · exact hb (List.mem_append_left _ hz)
    · apply List.disjoint_left.mpr
      intro z hz hzB
      rcases List.mem_append.mp hz with hzA|hz'
      · exact List.disjoint_left.mp nd.disjoint hzA hzB
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hz'
        rcases hz' with rfl|rfl
        · exact ha (List.mem_append_right _ hzB)
        · exact hb (List.mem_append_right _ hzB)
  have non : L≠[] := by simp [L]
  let q := Walk.ofSupport L non ch
  have qs : q.support=L := Walk.support_ofSupport non ch
  refine ⟨_,_,q,(Walk.IsPath.mk' (by rwa [qs] : q.support.Nodup)).isHamiltonian_of_mem ?_⟩
  intro z
  rw [qs]
  rcases covers z with rfl|rfl|old
  · simp [L]
  · simp [L]
  · rw [pl,List.mem_append] at old
    simp only [L,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    tauto

/-- If a longest path in the minimum-vertex deletion misses precisely one
vertex, swapping it with a shared midpoint supplies the two edges needed to
insert both omitted vertices across a single original path edge. -/
theorem singleton_minimum_deletion_traceable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (w : V) (minw : G.degree w=G.minDegree)
    {u v : {x : V | x ≠ w}} (p : (G.induce {x : V | x ≠ w}).Walk u v) (hp : p.IsPath)
    (longest : ∀ {i j}, ∀ q : (G.induce {x : V | x ≠ w}).Walk i j, q.IsPath → q.length≤p.length)
    (x : {z : V | z ≠ w}) (outside : x∉p.support) (sole : ∀ y, y ≠ x → y∈p.support)
    (large : 3 ≤ G.secondSmallestDegree) (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) :
    ∃ a b, ∃ q : G.Walk a b, q.IsHamiltonian := by
  classical
  let S := {v : V | v ≠ w}
  let H := G.induce S
  have high (z : S) : G.secondSmallestDegree ≤ G.degree z.val := by
    rcases degree_pair (G:=G) z.val w z.property with h|h
    · exact h
    · rw [minw] at h
      exact h.trans (G.minDegree_le_degree z.val)
  have iso (y : S) (adj : H.Adj x y) : y ∈ p.support := sole y adj.ne.symm
  obtain ⟨xw,full⟩ := high_isolated_saturation w p hp longest x outside iso (by omega) (high x) (cap x.val)
  have count : (contactPositions p x).card=H.degree x := by
    rw [contact_card_neighbors p hp x,inter_eq_left.mpr (fun y hy =>
      List.mem_toFinset.mpr (iso y ((H.mem_neighborFinset x y).mp hy))),H.card_neighborFinset_eq_degree]
  have lost := degree_le_deletion_add_one (G:=G) w x
  change G.degree x.val ≤ H.degree x+1 at lost
  obtain ⟨i,hi,hi₂⟩ : ∃ i∈contactPositions p x, i+2∈contactPositions p x := by
    by_contra! no
    have wide (i : ℕ) (hi : i∈contactPositions p x) (j : ℕ) (hj : j∈contactPositions p x)
        (lt : i<j) : i+3≤j := by
      obtain ⟨ir,ic⟩ := (mem_contactPositions p x i).mp hi
      obtain ⟨jr,jc⟩ := (mem_contactPositions p x j).mp hj
      have sep := omitted_contact_spacing p hp longest outside ⟨i,ir⟩ ⟨j,jr⟩ lt
        (by simpa [get_at] using ic) (by simpa [get_at] using jc)
      change i+2≤j at sep
      by_contra! bad
      exact no i hi ((show j=i+2 by omega) ▸ hj)
    have expensive := double_positions_le_path_shell p hp longest outside wide
    rw [full,count] at expensive
    have := high x
    omega
  obtain ⟨ir,ic⟩ := (mem_contactPositions p x i).mp hi
  obtain ⟨jr,jc⟩ := (mem_contactPositions p x (i+2)).mp hi₂
  let m := p.getVert (i+1)
  have mx : m≠x := fun h => outside (h ▸ p.getVert_mem_support (i+1))
  obtain ⟨b,c,q,hq,len,sup⟩ := swap_contact_midpoint p hp outside i jr ic jc
  have never : m∉q.support := by
    intro h
    have member := List.mem_toFinset.mpr h
    rw [sup] at member
    exact (mem_insert.mp member).elim mx (fun t => (mem_erase.mp t).1 rfl)
  have iso' (y : S) (adj : H.Adj m y) : y∈q.support := by
    apply List.mem_toFinset.mp
    rw [sup]
    by_cases same : y=x
    · exact mem_insert.mpr (Or.inl same)
    · exact mem_insert.mpr (Or.inr (mem_erase.mpr ⟨adj.ne.symm,List.mem_toFinset.mpr (sole y same)⟩))
  have qlong {a b} (r : H.Walk a b) (hr : r.IsPath) : r.length≤q.length := by
    rw [len]
    exact longest r hr
  obtain ⟨mw,_⟩ := high_isolated_saturation w q hq qlong m never iso' (by omega) (high m) (cap m.val)
  let f := (Embedding.induce (G:=G) S).toHom
  let P := p.map f
  have path : P.IsPath := (Walk.isPath_map_iff_of_injective (f:=f) Subtype.val_injective).mpr hp
  have members (z : V) : z∈P.support ↔ ∃ t : S, t∈p.support ∧ (t.val:V)=z := by
    rw [show P=p.map f from rfl,Walk.support_map]
    exact List.mem_map
  have PL := P.length_support
  have old := p.length_support
  have eqLen : P.length=p.length := Walk.length_map f p
  refine insert_two P path i (by omega) (a:=x.val) (b:=w) ?_ ?_ xw ?_ ?_ ?_
  · intro h
    obtain ⟨t,ht,te⟩ := (members _).mp h
    exact outside ((Subtype.ext te : t=x) ▸ ht)
  · intro h
    obtain ⟨t,_,te⟩ := (members _).mp h
    exact t.property te
  · change G.Adj ((p.map f).getVert i) x.val
    rw [Walk.getVert_map]
    exact ic
  · change G.Adj w ((p.map f).getVert (i+1))
    rw [Walk.getVert_map]
    exact mw.symm
  · intro z
    by_cases zw : z=w
    · exact Or.inr (Or.inl zw)
    · let t : S := ⟨z,zw⟩
      by_cases tx : t=x
      · exact Or.inl (congrArg Subtype.val tx)
      · exact Or.inr (Or.inr ((members z).mpr ⟨t,sole t tx,rfl⟩))

#print axioms singleton_minimum_deletion_traceable
end Graph189ExteriorDegreeCycle
