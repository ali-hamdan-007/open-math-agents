module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.List.Chain

public section

namespace Graph189

open SimpleGraph Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
private theorem chain_of_clique_list {s : V → Prop} {L : List V}
    (hn : L.Nodup) (hm : ∀ x ∈ L, s x)
    (hclique : ∀ {u v}, s u → s v → u ≠ v → G.Adj u v) :
    L.IsChain G.Adj :=
  List.Pairwise.isChain (hn.imp_of_mem (fun {_ _} ha hb hne =>
    hclique (hm _ ha) (hm _ hb) hne))

/-- A finite clique has a spanning path starting at any prescribed member. -/
theorem rootedCliqueList (s : Finset V) {r : V} (hr : r ∈ s)
    (hclique : ∀ {u v}, u ∈ s → v ∈ s → u ≠ v → G.Adj u v) :
    ∃ L : List V, L.head? = some r ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ x, x ∈ L ↔ x ∈ s := by
  let L := r :: (s.erase r).toList
  have hm (x : V) : x ∈ L ↔ x ∈ s := by
    by_cases hx : x = r <;> simp [L, hx, hr]
  have hn : L.Nodup := List.nodup_cons.mpr ⟨by simp, Finset.nodup_toList _⟩
  exact ⟨L, rfl, hn, chain_of_clique_list hn (fun x hx => (hm x).mp hx) hclique, hm⟩

/-- A finite clique has a spanning path between distinct prescribed members. -/
theorem rootedCliqueBetweenList (s : Finset V) {r t : V}
    (hr : r ∈ s) (ht : t ∈ s) (hrt : r ≠ t)
    (hclique : ∀ {u v}, u ∈ s → v ∈ s → u ≠ v → G.Adj u v) :
    ∃ L : List V, L.head? = some r ∧ L.getLast? = some t ∧
      L.Nodup ∧ L.IsChain G.Adj ∧ ∀ x, x ∈ L ↔ x ∈ s := by
  let L := r :: (((s.erase r).erase t).toList ++ [t])
  have hm (x : V) : x ∈ L ↔ x ∈ s := by
    by_cases hxr : x = r
    · simp [L, hxr, hr]
    by_cases hxt : x = t
    · simp [L, hxt, ht]
    · simp [L, hxr, hxt]
  have hn : L.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨by simp [hrt], List.nodup_append.mpr ⟨Finset.nodup_toList _, by simp, ?_⟩⟩
    intro x hx y hy hxy
    have hyt : y = t := by simpa using hy
    exact (Finset.mem_erase.mp (Finset.mem_toList.mp hx)).1 (hxy.trans hyt)
  have hlast : L.getLast? = some t := by simp [L, List.getLast?_cons, List.getLast?_append]
  exact ⟨L, rfl, hlast, hn, chain_of_clique_list hn (fun x hx => (hm x).mp hx) hclique, hm⟩

/-- A graph that is a clique except at z has a rooted spanning path if z has a
clique neighbor different from the root, or if the root is z itself. -/
theorem rootedCliqueExceptList (s : Finset V) {r z : V}
    (hr : r ∈ s) (hz : z ∈ s)
    (hclique : ∀ {u v}, u ∈ s.erase z → v ∈ s.erase z → u ≠ v → G.Adj u v)
    (hcontact : ∃ u ∈ s.erase z, G.Adj z u ∧ (r = z ∨ r ≠ u)) :
    ∃ L : List V, L.head? = some r ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ x, x ∈ L ↔ x ∈ s := by
  obtain ⟨u, hu, hzu, hroot⟩ := hcontact
  by_cases hrz : r = z
  · subst r
    obtain ⟨L, hhead, hn, hc, hm⟩ := rootedCliqueList (G := G) (s.erase z) hu hclique
    refine ⟨z :: L, rfl, ?_, ?_, ?_⟩
    · exact List.nodup_cons.mpr ⟨fun hmz => (Finset.mem_erase.mp ((hm z).mp hmz)).1 rfl, hn⟩
    · exact hc.cons (by simpa [hhead] using hzu)
    · intro x
      by_cases hx : x = z <;> simp [hx, hz, hm]
  · have hru : r ≠ u := hroot.resolve_left hrz
    obtain ⟨L, hhead, hlast, hn, hc, hm⟩ :=
      rootedCliqueBetweenList (G := G) (s.erase z) (Finset.mem_erase.mpr ⟨hrz,hr⟩) hu hru hclique
    refine ⟨L ++ [z], ?_, ?_, ?_, ?_⟩
    · have hne : L ≠ [] := by intro he; simp [he] at hhead
      rwa [List.head?_append_of_ne_nil _ hne]
    · apply List.nodup_append.mpr
      refine ⟨hn, by simp, ?_⟩
      intro x hx y hy hxy
      have hyz : y = z := by simpa using hy
      exact (Finset.mem_erase.mp ((hm x).mp hx)).1 (hxy.trans hyz)
    · apply hc.append (List.IsChain.singleton z)
      intro x hx y hy
      have hux : u = x := by simpa [hlast] using hx
      have hzy : z = y := by simpa using hy
      exact hux ▸ hzy ▸ hzu.symm
    · intro x
      by_cases hx : x = z <;> simp [hx, hz, hm]

/-- Span a core from its gate after closure has made all but at most one core
vertex a clique. Two internal neighbors suffice for the exceptional vertex. -/
theorem rootedGateCliqueList (A : Finset V) {c : V} (hc : c ∉ A)
    (hcontact : ∃ u ∈ A, G.Adj c u)
    (hshape : (∀ {u v}, u ∈ A → v ∈ A → u ≠ v → G.Adj u v) ∨
      ∃ z ∈ A, ∀ {u v}, u ∈ A.erase z → v ∈ A.erase z → u ≠ v → G.Adj u v)
    (htwo : ∀ u ∈ A, ∃ x ∈ insert c A, ∃ y ∈ insert c A,
      x ≠ y ∧ G.Adj u x ∧ G.Adj u y) :
    ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ x, x ∈ L ↔ x = c ∨ x ∈ A := by
  suffices h : ∃ u, G.Adj c u ∧ ∃ L : List V, L.head? = some u ∧
      L.Nodup ∧ L.IsChain G.Adj ∧ ∀ x, x ∈ L ↔ x ∈ A by
    obtain ⟨u, hcu, L, hhead, hn, hchain, hm⟩ := h
    refine ⟨c :: L, rfl, List.nodup_cons.mpr ⟨fun h => hc ((hm c).mp h), hn⟩, ?_, ?_⟩
    · exact hchain.cons (by simpa [hhead] using hcu)
    · intro x
      simp [hm, eq_comm]
  obtain ⟨u, hu, hcu⟩ := hcontact
  rcases hshape with hclique | ⟨z, hz, hclique⟩
  · exact ⟨u, hcu, rootedCliqueList (G := G) A hu hclique⟩
  obtain ⟨x, hx, y, hy, hxy, hzx, hzy⟩ := htwo z hz
  by_cases hcz : G.Adj c z
  · refine ⟨z, hcz, rootedCliqueExceptList (G := G) A hz hz hclique ?_⟩
    by_cases hxc : x = c
    · have hyc : y ≠ c := fun he => hxy (hxc.trans he.symm)
      exact ⟨y, Finset.mem_erase.mpr ⟨hzy.ne.symm, (Finset.mem_insert.mp hy).resolve_left hyc⟩,
        hzy, Or.inl rfl⟩
    · exact ⟨x, Finset.mem_erase.mpr ⟨hzx.ne.symm, (Finset.mem_insert.mp hx).resolve_left hxc⟩,
        hzx, Or.inl rfl⟩
  · refine ⟨u, hcu, rootedCliqueExceptList (G := G) A hu hz hclique ?_⟩
    have hxc : x ≠ c := fun he => hcz (he ▸ hzx).symm
    have hyc : y ≠ c := fun he => hcz (he ▸ hzy).symm
    by_cases hxu : x = u
    · have huy : u ≠ y := fun he => hxy (hxu.trans he)
      exact ⟨y, Finset.mem_erase.mpr ⟨hzy.ne.symm, (Finset.mem_insert.mp hy).resolve_left hyc⟩,
        hzy, Or.inr huy⟩
    · exact ⟨x, Finset.mem_erase.mpr ⟨hzx.ne.symm, (Finset.mem_insert.mp hx).resolve_left hxc⟩,
        hzx, Or.inr (fun he => hxu he.symm)⟩

#print axioms rootedCliqueList
#print axioms rootedCliqueBetweenList
#print axioms rootedCliqueExceptList
#print axioms rootedGateCliqueList

end Graph189
