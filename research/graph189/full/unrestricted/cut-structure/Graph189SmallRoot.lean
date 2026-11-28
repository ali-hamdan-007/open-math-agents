module

public import Graph189CutCore
public import Graph189TraceClosurePublic
public import Graph189Marked

public section

namespace Graph189SmallRoot
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Traceability can be tested after completing any high-degree set. -/
theorem trace_of_clique_extension {G : SimpleGraph V} [DecidableRel G.Adj]
    (high : V → Prop) (k : ℕ) (horder : Fintype.card V ≤ 2 * k + 1)
    (hdegree : ∀ x, high x → k ≤ G.degree x)
    (finish : ∀ K : SimpleGraph V, G ≤ K →
      (∀ x y, high x → high y → x ≠ y → K.Adj x y) →
      ∃ a b, ∃ p : K.Walk a b, p.IsHamiltonian) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let T (K : SimpleGraph V) := ∃ a b, ∃ p : K.Walk a b, p.IsHamiltonian
  change T G
  by_contra hn
  obtain ⟨K, hGK, hm⟩ := Finite.exists_le_maximal (p := fun K => ¬ T K) hn
  apply hm.prop
  apply finish K hGK
  intro x y hx hy hne
  have mono (v : V) : G.degree v ≤ K.degree v := by
    apply Finset.card_le_card
    intro u hu
    exact (K.mem_neighborFinset _ _).mpr (hGK ((G.mem_neighborFinset _ _).mp hu))
  have hsum : Fintype.card V ≤ K.degree x + K.degree y + 1 := by
    have := (hdegree x hx).trans (mono x)
    have := (hdegree y hy).trans (mono y)
    omega
  by_contra hxy
  have hnot : ¬ T (K ⊔ edge x y) := fun hp =>
    hm.prop (Graph189.traceable_of_sup_edge hne hxy hsum hp)
  exact hxy (hm.le_of_ge hnot le_sup_left
    (Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,hne⟩)))

#print axioms trace_of_clique_extension
omit [Fintype V] in
/-- A gate-rooted clique traversal lifts to a Hamilton path in a marked supergraph. -/
private theorem prefix_marker {G : SimpleGraph V} {c : V} {K : SimpleGraph (Option V)}
    (hGK : marked G c ≤ K) (L : List V) (hhead : L.head? = some c)
    (hnodup : L.Nodup) (hchain : L.IsChain (K.comap some).Adj)
    (hcover : ∀ v : V, v ∈ L) : ∃ a b, ∃ p : K.Walk a b, p.IsHamiltonian := by
  let W : List (Option V) := none :: L.map some
  have hWn : W.Nodup := List.nodup_cons.mpr ⟨by simp, hnodup.map (Option.some_injective V)⟩
  have hc : W.IsChain K.Adj := by
    apply List.isChain_cons.mpr
    refine ⟨?_, (List.isChain_map _).mpr hchain⟩
    intro y hy
    have he : some c = y := by simpa [List.head?_map,hhead] using hy
    subst y
    exact hGK (show (marked G c).Adj none (some c) from rfl)
  have hw (v : Option V) : v ∈ W := by
    cases v with
    | none => simp [W]
    | some x => simp [W,hcover x]
  let path := SimpleGraph.Walk.ofSupport W (by simp [W]) hc
  have hs : path.support = W := Walk.support_ofSupport _ hc
  exact ⟨_, _, path, (Walk.IsPath.mk' (hs.symm ▸ hWn)).isHamiltonian_of_mem
    (fun v => hs.symm ▸ hw v)⟩

/-- The clique completion argument on a finite side with prescribed gate. -/
theorem marked_trace_at_small_root_of_finish
    (finishClique : ∀ {Q : SimpleGraph V} (A : Finset V) {c : V}, c ∉ A →
      (∃ u ∈ A, Q.Adj c u) →
      ((∀ {u v}, u ∈ A → v ∈ A → u ≠ v → Q.Adj u v) ∨
        ∃ z ∈ A, ∀ {u v}, u ∈ A.erase z → v ∈ A.erase z → u ≠ v → Q.Adj u v) →
      (∀ u ∈ A, ∃ x ∈ insert c A, ∃ y ∈ insert c A, x ≠ y ∧ Q.Adj u x ∧ Q.Adj u y) →
      ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain Q.Adj ∧
        ∀ x, x ∈ L ↔ x = c ∨ x ∈ A)
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : V) (k : ℕ)
    (hsize : Fintype.card V ≤ 2*k) (hc : ∃ u, G.Adj c u)
    (hpair : ∀ u v, u ≠ c → v ≠ c → u ≠ v → k ≤ G.degree u ∨ k ≤ G.degree v)
    (htwo : ∀ u, u ≠ c → 2 ≤ G.degree u) :
    ∃ a b, ∃ p : (marked G c).Walk a b, p.IsHamiltonian := by
  classical
  let H (u : Option V) := ∃ v : V, u = some v ∧ k ≤ G.degree v
  apply trace_of_clique_extension H k
  · rw [Fintype.card_option]
    omega
  · intro u hu
    obtain ⟨v,rfl,hv⟩ := hu
    apply hv.trans
    rw [← G.card_neighborSet_eq_degree v, ← (marked G c).card_neighborSet_eq_degree _]
    let f (y : G.neighborSet v) : (marked G c).neighborSet (some v) :=
      ⟨some y.val, y.property⟩
    apply Fintype.card_le_of_injective f
    intro s t eq
    exact Subtype.ext (Option.some.inj (congrArg Subtype.val eq))
  · intro K hGK hK
    let Q := K.comap (some : V → Option V)
    have hGQ : G ≤ Q := by
      intro x y h
      exact hGK (show (marked G c).Adj (some x) (some y) from h)
    let A : Finset V := univ.erase c
    have hA (u : V) : u ∈ A ↔ u ≠ c := by simp [A]
    have hi (u : V) : u ∈ insert c A := by by_cases h : u = c <;> simp [A,h]
    have hhigh {u v : V} (hu : k ≤ G.degree u) (hv : k ≤ G.degree v) (hne : u ≠ v) :
        Q.Adj u v :=
      hK (some u) (some v) ⟨u,rfl,hu⟩ ⟨v,rfl,hv⟩ (fun e => hne (Option.some.inj e))
    apply Exists.elim (finishClique (Q := Q) A (c := c) (by simp [A]) _ _ _)
    · intro L hL
      exact prefix_marker hGK L hL.1 hL.2.1 hL.2.2.1 (fun x => (hL.2.2.2 x).mpr
        (by by_cases e : x = c; exact Or.inl e; exact Or.inr ((hA x).mpr e)))
    · obtain ⟨u,hu⟩ := hc
      exact ⟨u,(hA u).mpr hu.ne.symm,hGQ hu⟩
    · by_cases hall : ∀ u ∈ A, k ≤ G.degree u
      · exact Or.inl (fun hx hy hxy => hhigh (hall _ hx) (hall _ hy) hxy)
      · push Not at hall
        obtain ⟨z,hz,hlow⟩ := hall
        have high {u : V} (hu : u ∈ A.erase z) : k ≤ G.degree u := by
          obtain ⟨hne,hin⟩ := mem_erase.mp hu
          exact (hpair u z ((hA u).mp hin) ((hA z).mp hz) hne).resolve_right
            (by omega)
        exact Or.inr ⟨z,hz,(fun hu hv hne => hhigh (high hu) (high hv) hne)⟩
    · intro u hu
      have hd : 1 < (G.neighborFinset u).card := by
        rw [G.card_neighborFinset_eq_degree]
        exact htwo u ((hA u).mp hu)
      obtain ⟨x,hx,y,hy,ne⟩ := Finset.one_lt_card.mp hd
      exact ⟨x,hi x,y,hi y,ne,hGQ ((G.mem_neighborFinset u x).mp hx),
        hGQ ((G.mem_neighborFinset u y).mp hy)⟩

#print axioms marked_trace_at_small_root_of_finish

end Graph189SmallRoot
