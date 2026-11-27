import Graph189DiameterFour
import Graph199Prefix

namespace Graph189CliqueLayers
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private theorem clique_from_to {S : Set V} {a b : V}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (hc : G.IsClique S) :
    ∃ L : List V, L.head? = some a ∧ L.getLast? = some b ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ v, v ∈ L ↔ v ∈ S := by
  let S' : Set V := S \ {a}
  have hb' : b ∈ S' := ⟨hb,by simpa using hab.symm⟩
  have hc' : G.IsClique S' := by intro x hx y hy hne; exact hc hx.1 hy.1 hne
  obtain ⟨L,hl,hn,hch,hm⟩ := Graph199.clique_list_ending hb' hc'
  have hne : L ≠ [] := by intro he; simp [he] at hl
  have hna : a ∉ L := by rw [hm]; simp [S']
  refine ⟨a :: L,rfl,?_,List.nodup_cons.mpr ⟨hna,hn⟩,hch.cons ?_,?_⟩
  · cases L with
    | nil => contradiction
    | cons y L => exact hl
  · intro x hx
    have hx' := (hm x).mp (List.mem_of_mem_head? hx)
    exact hc ha hx'.1 (fun he => hx'.2 (by simp [← he]))
  · intro x
    by_cases he : x = a
    · simp [he,ha]
    · simp [hm,S',he]

omit [Fintype V] [DecidableEq V] in
/-- A path avoiding a given layer vertex still crosses the layer frontier.
This supplies an exit distinct from the chosen entry. -/
theorem avoid_frontier (h : G.Connected) (root far : V) (hf : G.dist root far = 4)
    (avoid : ∀ x : V, (G.induce {v : V | v ≠ x}).Preconnected)
    (i : ℕ) (hi : 0 < i) (hi4 : i < 4) (x : V) (hx : G.dist root x = i) :
    ∃ a b : V, G.dist root a = i ∧ G.dist root b = i+1 ∧ a ≠ x ∧ G.Adj a b := by
  have hr : root ≠ x := by intro e; rw [← e,dist_self] at hx; omega
  have hf' : far ≠ x := by intro e; rw [← e,hf] at hx; omega
  let H := G.induce {v : V | v ≠ x}
  let u : {v : V // v ≠ x} := ⟨root,hr⟩
  let v : {v : V // v ≠ x} := ⟨far,hf'⟩
  have step {a b : V} (ha : G.Adj a b) : G.dist root b ≤ G.dist root a + 1 := by
    have ht := h.dist_triangle (u := root) (v := a) (w := b)
    rwa [dist_eq_one_iff_adj.mpr ha] at ht
  have cross {a b : {v : V // v ≠ x}} (p : H.Walk a b)
      (ha : G.dist root a.val ≤ i) (hb : i < G.dist root b.val) :
      ∃ a b : V, G.dist root a = i ∧ G.dist root b = i+1 ∧ a ≠ x ∧ G.Adj a b := by
    induction p with
    | nil => omega
    | @cons a w b haw p ih =>
      by_cases hw : G.dist root w.val ≤ i
      · exact ih hw hb
      · have hadj : G.Adj a.val w.val := haw
        have hs := step hadj
        exact ⟨a.val,w.val,by omega,by omega,a.property,hadj⟩
  obtain ⟨p⟩ := avoid x u v
  apply cross p
  · simp [u]
  · change i < G.dist root far
    omega

/-- If no single vertex disconnects the graph and the layers from a
diameter-four endpoint are cliques, a Hamiltonian path can traverse the layers in order. -/
theorem hamiltonian [Nontrivial V] (h : G.Connected) (hd : G.diam ≤ 4)
    (root far : V) (hf : G.dist root far = 4)
    (avoid : ∀ x : V, (G.induce {v : V | v ≠ x}).Preconnected)
    (cliques : ∀ i : ℕ, G.IsClique {v : V | G.dist root v = i}) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have := h.nonempty
  have bound (v : V) : G.dist root v ≤ 4 :=
    (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp h)).trans hd
  have tail (k : ℕ) (hk : k ≤ 3) (x : V) (hx : G.dist root x = 4-k) :
      ∃ L : List V, L.head? = some x ∧ L.Nodup ∧ L.IsChain G.Adj ∧
        ∀ v, v ∈ L ↔ 4-k ≤ G.dist root v := by
    induction k generalizing x with
    | zero =>
      obtain ⟨L,hh,hn,hc,hm⟩ := Graph199.clique_list_starting (S := {v : V | G.dist root v = 4}) (x := x) hx (cliques 4)
      exact ⟨L,hh,hn,hc,fun v => (hm v).trans (by
        change G.dist root v = 4 ↔ 4-0 ≤ G.dist root v
        have := bound v
        omega)⟩
    | succ k ih =>
      let i := 4-(k+1)
      have hi : 0 < i := by dsimp [i]; omega
      have hi4 : i < 4 := by dsimp [i]; omega
      obtain ⟨a,b,ha,hb,hax,hab⟩ := avoid_frontier h root far hf avoid i hi hi4 x hx
      obtain ⟨A,hAh,hAt,hAn,hAc,hAm⟩ :=
        clique_from_to (S := {v : V | G.dist root v = i}) hx ha hax.symm (cliques i)
      have hb' : G.dist root b = 4-k := by dsimp [i] at hb; omega
      obtain ⟨B,hBh,hBn,hBc,hBm⟩ := ih (by omega) b hb'
      have hAne : A ≠ [] := by intro he; simp [he] at hAh
      refine ⟨A ++ B, ?_, ?_, ?_, ?_⟩
      · rw [List.head?_append_of_ne_nil _ hAne,hAh]
      · refine List.nodup_append.mpr ⟨hAn,hBn,?_⟩
        intro u hu v hv he
        subst v
        have hu' : G.dist root u = i := (hAm u).mp hu
        have hv' := (hBm u).mp hv
        dsimp [i] at hu'
        omega
      · apply hAc.append hBc
        intro u hu v hv
        have hu' : a = u := by simpa [hAt] using hu
        have hv' : b = v := by simpa [hBh] using hv
        exact hu' ▸ hv' ▸ hab
      · intro u
        rw [List.mem_append,hAm,hBm]
        change G.dist root u = i ∨ 4-k ≤ G.dist root u ↔ 4-(k+1) ≤ G.dist root u
        dsimp [i]
        omega
  obtain ⟨x,hadj⟩ := h.preconnected.exists_adj_of_nontrivial root
  have hdx : G.dist root x = 4-3 := dist_eq_one_iff_adj.mpr hadj
  obtain ⟨L,hLh,hLn,hLc,hLm⟩ := tail 3 (by decide) x hdx
  have hrL : root ∉ L := by rw [hLm,SimpleGraph.dist_self]; decide
  have hc : (root :: L).IsChain G.Adj := hLc.cons (by simpa [hLh] using hadj)
  let p := Walk.ofSupport (root :: L) (by simp) hc
  have hs : p.support = root :: L := Walk.support_ofSupport _ _
  have hp : p.IsPath := Walk.IsPath.mk' (by rw [hs]; exact List.nodup_cons.mpr ⟨hrL,hLn⟩)
  refine ⟨_,_,p,hp.isHamiltonian_of_mem ?_⟩
  intro v
  rw [hs,List.mem_cons]
  by_cases he : v = root
  · exact Or.inl he
  · exact Or.inr ((hLm v).mpr (h.pos_dist_of_ne (Ne.symm he)))


/-- A two-connected diameter-four graph needs at least two vertices in the
middle layer and one in the far layer of a diameter endpoint. -/
theorem endpoint_budget [DecidableRel G.Adj] (h : G.Connected) (hd : G.diam ≤ 4)
    {root far : V} (hf : G.dist root far = 4)
    (avoid : ∀ x : V, (G.induce {v : V | v ≠ x}).Preconnected)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree) :
    2 ≤ (Graph189DiameterFour.layer G root 2).card ∧
      3 ≤ G.secondSmallestDegree ∧
      G.degree far + 3 ≤ G.secondSmallestDegree +
        ((G.neighborFinset far) ∩ Graph189DiameterFour.layer G root 3).card := by
  obtain ⟨p,hp⟩ := h.exists_walk_length_eq_dist root far
  rw [hf] at hp
  have h3 : G.dist root (p.getVert 3) = 3 := by
    have ht : G.dist root (p.getVert 3) ≤ 3 := (G.dist_le (p.take 3)).trans (by simp [Walk.take_length])
    have hl := p.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1 = p.length by omega,Walk.getVert_length] at hl
    have he := h.dist_triangle (u := root) (v := p.getVert 3) (w := far)
    rw [hf,dist_eq_one_iff_adj.mpr hl] at he
    omega
  obtain ⟨x,hx,_⟩ := Graph189LowDegreeTwo.split_three h h3
  obtain ⟨y,b,hy,_,hey,_⟩ := avoid_frontier h root far hf avoid 2 (by decide) (by decide) x hx
  have h₂ : 2 ≤ (Graph189DiameterFour.layer G root 2).card :=
    Finset.one_lt_card.mpr ⟨x,(Graph189DiameterFour.mem_layer root 2 x).mpr hx,
      y,(Graph189DiameterFour.mem_layer root 2 y).mpr hy,hey.symm⟩
  have h₄ : 0 < (Graph189DiameterFour.layer G root 4).card :=
    Finset.card_pos.mpr ⟨far,(Graph189DiameterFour.mem_layer root 4 far).mpr hf⟩
  have hb := hσ root
  rw [Graph189DiameterFour.even_layers_four h hd root] at hb
  have hpr := Graph189DiameterFour.opposite_predecessor_lower h hd hf hσ
  exact ⟨h₂,by omega,by omega⟩

#print axioms avoid_frontier
#print axioms hamiltonian
#print axioms endpoint_budget
end Graph189CliqueLayers
