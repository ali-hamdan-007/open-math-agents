import BipartiteSplice

namespace BalancedBipartite

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}

theorem chain_drops_edge {l : List V} {x y : V}
    (h : l.IsChain (G ⊔ edge x y).Adj) (hmiss : x ∉ l ∨ y ∉ l) :
    l.IsChain G.Adj := by
  apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
  intro a b P Q he
  have ha : a ∈ l := by rw [he]; simp
  have hb : b ∈ l := by rw [he]; simp
  have hab := List.isChain_iff_forall_rel_of_append_cons_cons.mp h he
  rcases hab with hab | hab
  · exact hab
  · rcases ((edge_adj x y a b).mp hab).1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact (hmiss.elim (fun h => h ha) (fun h => h hb)).elim
    · exact (hmiss.elim (fun h => h hb) (fun h => h ha)).elim

theorem closing_not_internal {l : List V} {a b : V}
    (hsize : 3 ≤ l.length) (hn : l.Nodup)
    (ha : l.head? = some a) (hb : l.getLast? = some b)
    (j : ℕ) (hj : j+1 < l.length) :
    ¬ (edge l[j] l[j+1]).Adj b a := by
  intro h
  have hne : l ≠ [] := by intro e; simp [e] at ha
  have h0 : l[0]'(by omega) = a := by
    rw [← List.head_eq_getElem hne]
    exact List.head_of_head?_eq_some ha
  have hlast : l[l.length-1]'(by omega) = b := by
    rw [← List.getLast_eq_getElem hne]
    exact List.getLast_of_getLast?_eq_some hb
  rcases ((edge_adj _ _ _ _).mp h).1 with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · have ha' := hn.getElem_inj_iff.mp (h0.trans h₂)
    have hb' := hn.getElem_inj_iff.mp (hlast.trans h₁)
    omega
  · have ha' := hn.getElem_inj_iff.mp (h0.trans h₂)
    have hb' := hn.getElem_inj_iff.mp (hlast.trans h₁)
    omega

/-- A cross edge with the balanced bipartite degree-sum threshold can be
removed from a newly spanning cycle by an alternating-path splice. -/
theorem cycle_of_sup_edge [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {r : ℕ} (hr : 2 ≤ r) (hcard : Fintype.card V = 2*r)
    {col : V → Bool} (hcol : ∀ ⦃a b⦄, G.Adj a b → col a ≠ col b)
    {x y : V} (hxy : col x ≠ col y) (hdeg : r+1 ≤ G.degree x + G.degree y)
    (h : HasSpanningCycle (G ⊔ edge x y)) : HasSpanningCycle G := by
  classical
  obtain ⟨l,a,b,hn,hall,hchain,ha,hb,hclose⟩ := h
  have hlen : l.length = 2*r := by
    rw [← List.toFinset_card_of_nodup hn]
    have hf : l.toFinset = univ := by ext v; simp [hall]
    simpa [hf] using hcard
  by_cases hc : l.IsChain G.Adj
  · rcases hclose with hclose | hclose
    · exact ⟨l,a,b,hn,hall,hc,ha,hb,hclose⟩
    · rcases ((edge_adj x y b a).mp hclose).1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact cycle_of_spanning_path hcol hlen hn hall hc ha hb hxy.symm (by omega)
      · exact cycle_of_spanning_path hcol hlen hn hall hc ha hb hxy hdeg
  obtain ⟨j,hj,hbad⟩ := List.exists_not_getElem_of_not_isChain hc
  let u := l[j]'(by omega)
  let v := l[j+1]
  have huv : (edge x y).Adj u v := by
    have hup : (G ⊔ edge x y).Adj u v := List.isChain_iff_getElem.mp hchain j hj
    rcases hup with hup | hup
    · exact (hbad hup).elim
    · exact hup
  have hpair : (u=x ∧ v=y) ∨ (u=y ∧ v=x) := ((edge_adj x y u v).mp huv).1
  have hedges : edge x y = edge u v := by
    rcases hpair with ⟨hu,hv⟩ | ⟨hu,hv⟩
    · rw [hu,hv]
    · rw [hu,hv,edge_comm]
  have hd : r+1 ≤ G.degree v + G.degree u := by
    rcases hpair with ⟨hu,hv⟩ | ⟨hu,hv⟩ <;> rw [hu,hv] <;> omega
  have hcolors : col v ≠ col u := by
    rcases hpair with ⟨hu,hv⟩ | ⟨hu,hv⟩
    · rw [hu,hv]
      exact hxy.symm
    · rw [hu,hv]
      exact hxy
  rw [hedges] at hchain hclose
  have hcloseG : G.Adj b a := by
    rcases hclose with hc | hc
    · exact hc
    · exact (closing_not_internal (by omega) hn ha hb j hj hc).elim
  obtain ⟨P,Q,hsplit⟩ := pair_at l j hj
  change l = P ++ u :: v :: Q at hsplit
  let L := P ++ [u]
  let R := v :: Q
  have he : l = L ++ R := by simpa [L,R,List.append_assoc] using hsplit
  have hnod : (L ++ R).Nodup := he ▸ hn
  have hnu : u ∉ R := fun h =>
    (List.nodup_append.mp hnod).2.2 u (by simp [L]) u h rfl
  have hnv : v ∉ L := fun h =>
    (List.nodup_append.mp hnod).2.2 v h v (by simp [R]) rfl
  have hLc : L.IsChain G.Adj := chain_drops_edge (he ▸ hchain).left_of_append (Or.inr hnv)
  have hRc : R.IsChain G.Adj := chain_drops_edge (he ▸ hchain).right_of_append (Or.inl hnu)
  have hLne : L ≠ [] := by simp [L]
  have hRne : R ≠ [] := by simp [R]
  have hLa : L.head? = some a := by rwa [he,List.head?_append_of_ne_nil _ hLne] at ha
  have hRb : R.getLast? = some b := by rwa [he,List.getLast?_append_of_ne_nil _ hRne] at hb
  have hp : (R ++ L).Perm l := he.symm ▸ List.perm_append_comm
  have hhead : (R ++ L).head? = some v := by
    rw [List.head?_append_of_ne_nil _ hRne]
    rfl
  have hlast : (R ++ L).getLast? = some u := by
    rw [List.getLast?_append_of_ne_nil _ hLne]
    simp [L]
  exact cycle_of_spanning_path hcol (hp.length_eq.trans hlen) (hp.nodup_iff.mpr hn)
    (fun z => hp.mem_iff.mpr (hall z)) (join_chain hRc hLc hRb hLa hcloseG)
    hhead hlast hcolors hd

#print axioms cycle_of_sup_edge

end BalancedBipartite
