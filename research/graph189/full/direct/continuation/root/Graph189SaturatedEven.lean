import Graph189QuadraticOrder

open SimpleGraph Finset
namespace Graph189SaturatedEven
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Spending the full distance-two allowance identifies every even-distance vertex. -/
theorem even_shell (x : V) (D : Finset V) [DecidableEq V] (off : x∉D)
    (two : ∀ y∈D, G.dist x y=2) (cap : G.distEven x≤D.card+1) :
    univ.filter (fun y => Even (G.dist x y)) = insert x D := by
  classical
  symm
  apply eq_of_subset_of_card_le
  · intro y hy
    rcases mem_insert.mp hy with rfl|hy
    · simp
    · apply mem_filter.mpr
      exact ⟨mem_univ _,by rw [two y hy]; decide⟩
  · rw [card_insert_of_notMem off]
    exact cap

/-- A walk avoiding a full distance-two witness set cannot leave the closed
neighborhood of its initial vertex. All distances are in the original graph. -/
theorem walk_in_closed_neighborhood (x : V) (D : Finset V) (off : x∉D)
    (two : ∀ y∈D, G.dist x y=2) (cap : G.distEven x≤D.card+1)
    {u v : V} (p : G.Walk u v) (hu : G.dist x u≤1) (free : ∀ w∈p.support, w∉D) :
    G.dist x v≤1 := by
  classical
  have shell := even_shell (G:=G) x D off two cap
  induction p with
  | nil => exact hu
  | @cons u a v edge tail ih =>
    apply ih
    · have changeByOne := edge.diff_dist_adj (u:=x)
      by_contra! bad
      have ha : G.dist x a=2 := by omega
      have mem : a∈univ.filter (fun y => Even (G.dist x y)) :=
        mem_filter.mpr ⟨mem_univ _,by rw [ha]; decide⟩
      rw [shell] at mem
      have ax : a≠x := by intro e; subst a; simp at ha
      exact free a (by simp only [Walk.support_cons,List.mem_cons]; exact Or.inr tail.start_mem_support)
        (mem_of_mem_insert_of_ne mem ax)
    · intro y hy
      exact free y (by simp only [Walk.support_cons,List.mem_cons]; exact Or.inr hy)

/-- Every other vertex reached from x without visiting D is a genuine neighbor of x. -/
theorem forced_edge (x : V) (D : Finset V) (off : x∉D)
    (two : ∀ y∈D, G.dist x y=2) (cap : G.distEven x≤D.card+1)
    {v : V} (p : G.Walk x v) (free : ∀ w∈p.support, w∉D)
    (ne : x≠v) : G.Adj x v := by
  have hi := walk_in_closed_neighborhood x D off two cap p (by simp) free
  by_contra missing
  have far := p.reachable.one_lt_dist_of_ne_of_not_adj ne missing
  omega

#print axioms forced_edge
end Graph189SaturatedEven
