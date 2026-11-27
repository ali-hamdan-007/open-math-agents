import Graph189OddCycleCount

namespace Graph189ShortestOdd
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/-- In a connected nonbipartite graph, walks from a root provide an odd closed walk. -/
theorem exists_odd_closed (h : G.Connected) (hB : ¬ G.IsBipartite) :
    ∃ a : V, ∃ p : G.Walk a a, p.length % 2 = 1 := by
  by_contra! hn
  obtain ⟨a⟩ := h.nonempty
  let color (v : V) : Fin 2 := ⟨G.dist a v % 2, Nat.mod_lt _ (by decide)⟩
  apply hB
  refine ⟨Coloring.mk color ?_⟩
  intro x y hxy he
  obtain ⟨p,hp⟩ := h.exists_walk_length_eq_dist a x
  obtain ⟨q,hq⟩ := h.exists_walk_length_eq_dist a y
  let w := (p.concat hxy).append q.reverse
  have ho := hn a w
  have hel : G.dist a x % 2 = G.dist a y % 2 := congrArg Fin.val he
  dsimp only [w] at ho
  rw [Walk.length_append, Walk.length_concat, Walk.length_reverse, hp, hq] at ho
  omega

/-- A shortest odd closed walk minimizes length among all odd closed walks. -/
theorem exists_shortest (h : G.Connected) (hB : ¬ G.IsBipartite) :
    ∃ a : V, ∃ p : G.Walk a a, p.length % 2 = 1 ∧
      ∀ b : V, ∀ q : G.Walk b b, q.length % 2 = 1 → p.length ≤ q.length := by
  classical
  let P (n : ℕ) := ∃ a : V, ∃ p : G.Walk a a, p.length = n ∧ p.length % 2 = 1
  obtain ⟨a,p,hp⟩ := exists_odd_closed h hB
  have hP : ∃ n, P n := ⟨p.length,a,p,rfl,hp⟩
  obtain ⟨b,q,hq,hqo⟩ := Nat.find_spec hP
  exact ⟨b,q,hqo,fun c r hr => hq.symm ▸ Nat.find_min' hP ⟨c,r,rfl,hr⟩⟩

/-- An outside walk between two indices of a minimal odd closed walk must
be as long as the cycle arc of the same parity. -/
theorem detour_lower_bound {a : V} (p : G.Walk a a) (hp : p.length % 2 = 1)
    (hmin : ∀ b : V, ∀ q : G.Walk b b, q.length % 2 = 1 → p.length ≤ q.length)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) (r : G.Walk (p.getVert i) (p.getVert j)) :
    (r.length % 2 = (j-i) % 2 → j-i ≤ r.length) ∧
    (r.length % 2 ≠ (j-i) % 2 → p.length-(j-i) ≤ r.length) := by
  let forward : G.Walk (p.getVert i) (p.getVert j) := ((p.drop i).take (j-i)).copy rfl (by rw [Walk.drop_getVert, show i + (j-i) = j by omega])
  let back := (p.drop j).append (p.take i)
  have hf : forward.length = j-i := by
    dsimp [forward]
    rw [Walk.length_copy, Walk.take_length, Walk.drop_length, Nat.min_eq_left (by omega)]
  have hb : back.length = p.length-(j-i) := by
    dsimp [back]
    rw [Walk.length_append, Walk.drop_length, Walk.take_length, Nat.min_eq_left (by omega)]
    omega
  constructor
  · intro he
    have hlen : (r.append back).length = r.length + (p.length-(j-i)) := by rw [Walk.length_append,hb]
    have h := hmin _ (r.append back) (by rw [hlen]; omega)
    rw [hlen] at h
    omega
  · intro he
    have hlen : (r.append forward.reverse).length = r.length + (j-i) := by
      rw [Walk.length_append,Walk.length_reverse,hf]
    have h := hmin _ (r.append forward.reverse) (by rw [hlen]; omega)
    rw [hlen] at h
    omega

theorem shortest_index_injective {a : V} (p : G.Walk a a) (hp : p.length % 2 = 1)
    (hmin : ∀ b : V, ∀ q : G.Walk b b, q.length % 2 = 1 → p.length ≤ q.length) :
    Function.Injective (fun i : Fin p.length => p.getVert i.val) := by
  have hinc (i j : Fin p.length) (hij : i < j) : p.getVert i.val ≠ p.getVert j.val := by
    intro he
    let r : G.Walk (p.getVert i.val) (p.getVert j.val) := (Walk.nil : G.Walk _ _).copy rfl he
    have hr : r.length = 0 := by simp [r]
    have h := detour_lower_bound p hp hmin (Nat.le_of_lt hij) (Nat.le_of_lt j.isLt) r
    simp only [hr, Nat.zero_mod, Nat.le_zero_eq] at h
    have hi' := i.isLt
    have hj' := j.isLt
    change i.val < j.val at hij
    omega
  intro i j he
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact (hinc i j hij he).elim
  · rfl
  · exact (hinc j i hji he.symm).elim

/-- Distance one and two detours pin the cyclic gap of their endpoints. -/
theorem short_detours {a : V} (p : G.Walk a a) (hp : p.length % 2 = 1)
    (hmin : ∀ b : V, ∀ q : G.Walk b b, q.length % 2 = 1 → p.length ≤ q.length)
    {i j : ℕ} (hij : i < j) (hj : j < p.length) :
    (G.Adj (p.getVert i) (p.getVert j) → j-i = 1 ∨ j-i = p.length-1) ∧
    ((∃ x, G.Adj (p.getVert i) x ∧ G.Adj x (p.getVert j)) → j-i = 2 ∨ j-i = p.length-2) := by
  constructor
  · intro he
    let r := Walk.cons he Walk.nil
    have hr : r.length = 1 := rfl
    have h := detour_lower_bound p hp hmin hij.le hj.le r
    rw [hr] at h
    omega
  · rintro ⟨x,hix,hxj⟩
    let r := Walk.cons hix (Walk.cons hxj Walk.nil)
    have hr : r.length = 2 := rfl
    have h := detour_lower_bound p hp hmin hij.le hj.le r
    rw [hr] at h
    omega

/-- A closed odd walk in a triangle-free simple graph has length at least five. -/
theorem odd_ge_five {a : V} (p : G.Walk a a) (hp : p.length % 2 = 1)
    (htri : ∀ {x y z}, G.Adj x y → G.Adj y z → ¬ G.Adj x z) : 5 ≤ p.length := by
  by_contra! h
  have he : p.length = 1 ∨ p.length = 3 := by omega
  rcases he with he | he
  · have h1 := p.adj_getVert_succ (i := 0) (by omega)
    rw [Walk.getVert_zero, show 0+1 = p.length by omega, Walk.getVert_length] at h1
    exact G.irrefl h1
  · have h1 := p.adj_getVert_succ (i := 0) (by omega)
    have h2 := p.adj_getVert_succ (i := 1) (by omega)
    have h3 := p.adj_getVert_succ (i := 2) (by omega)
    rw [Walk.getVert_zero] at h1
    rw [show 2+1 = p.length by omega, Walk.getVert_length] at h3
    exact htri h1 h2 h3.symm

#print axioms short_detours
#print axioms shortest_index_injective
end Graph189ShortestOdd
