import Graph189ContactIntervals

open SimpleGraph
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y : V}

/-- All direct contacts of an omitted vertex are internal positions of any longest path. -/
theorem omitted_contact_internal (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a : V} (outside : a∉p.support) (i : Fin p.support.length) (contact : G.Adj p.support[i.val] a) :
    0 < i.val ∧ i.val + 1 < p.support.length := by
  let q : G.Walk a a := Walk.nil
  have hq : q.IsPath := by simp [q]
  have hd : List.Disjoint q.support p.support := by simpa [q,List.disjoint_left] using outside
  have h₁ := prefix_of_detour p hp longest i q hq hd contact.symm
  have h₂ := suffix_of_detour p hp longest i q hq hd contact
  simp only [q,Walk.support_nil,List.length_singleton] at h₁ h₂
  omega

/-- The contacts of an omitted vertex cannot occupy two adjacent path positions. -/
theorem omitted_contact_spacing (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a : V} (outside : a∉p.support) (i j : Fin p.support.length) (ordered : i<j)
    (first : G.Adj p.support[i.val] a) (second : G.Adj p.support[j.val] a) :
    i.val+2 ≤ j.val := by
  let q : G.Walk a a := Walk.nil
  have hq : q.IsPath := by simp [q]
  have hd : List.Disjoint q.support p.support := by simpa [q,List.disjoint_left] using outside
  exact interval_of_detour p hp longest i j ordered q hq hd first second.symm

/-- The cross contacts of two adjacent omitted vertices are separated by at least
three path positions. This is independent of both degree and metric quotas. -/
theorem adjacent_omitted_contact_spacing (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    (i j : Fin p.support.length) (ordered : i<j)
    (first : G.Adj p.support[i.val] a) (second : G.Adj p.support[j.val] b) :
    i.val+3 ≤ j.val := by
  let q : G.Walk a b := Walk.cons ab Walk.nil
  have hq : q.IsPath := Walk.IsPath.mk' (by simp [q,ab.ne])
  have hd : List.Disjoint q.support p.support := by
    rw [List.disjoint_left]
    intro z hz h
    rcases (show z=a ∨ z=b by simpa [q] using hz) with rfl | rfl
    · exact ha h
    · exact hb h
  exact interval_of_detour p hp longest i j ordered q hq hd first second.symm

#print axioms omitted_contact_internal
#print axioms omitted_contact_spacing
#print axioms adjacent_omitted_contact_spacing
end Graph189ExteriorGap
