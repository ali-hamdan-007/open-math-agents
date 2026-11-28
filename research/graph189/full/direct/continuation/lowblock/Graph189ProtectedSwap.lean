import Graph189ProtectedIntervals

open SimpleGraph
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {a b x y : V}

/-- Exchanging an interval for an equally long exterior path retains the
maximum through z.  Uniform neighborhoods on the new path then turn one
edge into the removed interval into an edge to every vertex of that interval. -/
theorem protected_swap_neighbors_with_route (p : G.Walk a b) (hp : p.IsPath) (z : V)
    (A J B : List V) (split : p.support=A++J++B) (kept : z ∈ A ∨ z ∈ B)
    (q : G.Walk x y) (hq : q.IsPath) (dis : List.Disjoint q.support p.support)
    (size : q.support.length=J.length)
    (left : ∀ v∈A.getLast?, G.Adj v x) (right : ∀ v∈B.head?, G.Adj y v)
    (uniform : ∀ {i j}, ∀ r : G.Walk i j, r.IsPath → z ∈ r.support → q.support ⊆ r.support → r.length=p.length →
      ∀ c ∈ r.support, ∀ v ∉ r.support, ∀ w ∉ r.support, G.Adj c v → G.Adj c w)
    {c : V} (contact : c ∈ A ∨ c ∈ B) (neighbor : ∃ v ∈ J, G.Adj c v) :
    ∀ v ∈ J, G.Adj c v := by
  obtain ⟨i,j,r,hr,e⟩ := splice_support p hp A J B split q hq dis left right
  have nd := hp.support_nodup
  rw [split] at nd
  have separated (v : V) (hv : v ∈ J) : v ∉ r.support := by
    rw [e]
    intro h
    rcases List.mem_append.mp h with mid | last
    · rcases List.mem_append.mp mid with first | new
      · exact List.disjoint_left.mp nd.of_append_left.disjoint first hv
      · exact List.disjoint_left.mp dis new (by simp [split,hv])
    · exact List.disjoint_left.mp nd.disjoint (by simp [hv]) last
  have length : r.length=p.length := by
    have h := r.length_support
    have g := p.length_support
    rw [split] at g
    rw [e] at h
    simp only [List.length_append,size] at h g
    omega
  have keep (v : V) (h : v∈A ∨ v∈B) : v∈r.support := by
    rw [e]
    rcases h with h | h <;> simp [h]
  obtain ⟨v,hv,edge⟩ := neighbor
  exact fun w hw => uniform r hr (keep z kept) (fun v hv => by rw [e]; simp [hv]) length c (keep c contact)
    v (separated v hv) w (separated w hw) edge

theorem protected_swap_neighbors (p : G.Walk a b) (hp : p.IsPath) (z : V)
    (A J B : List V) (split : p.support=A++J++B) (kept : z ∈ A ∨ z ∈ B)
    (q : G.Walk x y) (hq : q.IsPath) (dis : List.Disjoint q.support p.support)
    (size : q.support.length=J.length)
    (left : ∀ v∈A.getLast?, G.Adj v x) (right : ∀ v∈B.head?, G.Adj y v)
    (uniform : ∀ {i j}, ∀ r : G.Walk i j, r.IsPath → z ∈ r.support → r.length=p.length →
      ∀ c ∈ r.support, ∀ v ∉ r.support, ∀ w ∉ r.support, G.Adj c v → G.Adj c w)
    {c : V} (contact : c ∈ A ∨ c ∈ B) (neighbor : ∃ v ∈ J, G.Adj c v) :
    ∀ v ∈ J, G.Adj c v := by
  apply protected_swap_neighbors_with_route p hp z A J B split kept q hq dis size left right _ contact neighbor
  exact fun r hr hz _ => uniform r hr hz

#print axioms protected_swap_neighbors
end Graph189ExteriorGap
