import Graph189SingleExteriorShift
import Graph189ExteriorDegree

open SimpleGraph Finset

namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {x y : V}

theorem shifted_contact (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a : V} (out : a ∉ p.support) {i : ℕ} (mark : i∈contactPositions p a) :
    0 < i ∧ i+1 < p.support.length ∧ G.dist a (p.getVert (i-1))=2 ∧ G.dist a (p.getVert (i+1))=2 := by
  obtain ⟨inside,edge⟩ := (mem_contactPositions p a i).mp mark
  have adj : G.Adj p.support[i] a := by rwa [get_at p inside]
  obtain ⟨pos,below⟩ := omitted_contact_internal p hp longest out ⟨i,inside⟩ adj
  change 0 < i at pos
  change i+1 < p.support.length at below
  have ls := p.length_support
  have pred : i-1 < p.support.length := by omega
  have pre (j : ℕ) (inrange : j < p.support.length) (close : j+1=i ∨ i+1=j)
      (step : G.Adj (p.getVert j) (p.getVert i)) : G.dist a (p.getVert j)=2 := by
    have different : a ≠ p.getVert j := by rintro rfl; exact out (p.getVert_mem_support j)
    apply two_step_metric different _ edge.symm step
    intro adjacent
    have other : G.Adj p.support[j] a := by rw [get_at p inrange]; exact adjacent.symm
    rcases close with left | right
    · have bad := omitted_contact_spacing p hp longest out ⟨j,inrange⟩ ⟨i,inside⟩
        (show j < i by omega) other adj
      change j+2 ≤ i at bad
      omega
    · have bad := omitted_contact_spacing p hp longest out ⟨i,inside⟩ ⟨j,inrange⟩
        (show i < j by omega) adj other
      change i+2 ≤ j at bad
      omega
  refine ⟨pos,below,pre _ pred (Or.inl (by omega)) ?_,
    pre _ below (Or.inr rfl) (p.adj_getVert_succ (i:=i) (by omega)).symm⟩
  have e := p.adj_getVert_succ (i:=i-1) (by omega)
  rwa [show i-1+1=i by omega] at e

/-- Under a three-vertex second-layer quota, any two distinct contacts of one
omitted vertex of a longest path lie at distance precisely two along that path. -/
theorem two_marks_exact (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a : V} (out : a ∉ p.support) (quota : (univ.filter (fun z => G.dist a z=2)).card ≤ 3)
    {i j : ℕ} (hi : i∈contactPositions p a) (hj : j∈contactPositions p a) (lt : i < j) :
    i+2=j := by
  classical
  obtain ⟨ir,ie⟩ := (mem_contactPositions p a i).mp hi
  obtain ⟨jr,je⟩ := (mem_contactPositions p a j).mp hj
  have sep := omitted_contact_spacing p hp longest out ⟨i,ir⟩ ⟨j,jr⟩ lt
    (by simpa [get_at] using ie) (by simpa [get_at] using je)
  change i+2 ≤ j at sep
  by_contra diff
  obtain ⟨pi,bi,si,ti⟩ := shifted_contact p hp longest out hi
  obtain ⟨pj,bj,sj,tj⟩ := shifted_contact p hp longest out hj
  let W : Finset ℕ := {i-1,i+1,j-1,j+1}
  have card : W.card = 4 := by
    dsimp [W]
    rw [card_insert_of_notMem (by simp only [mem_insert,mem_singleton]; omega),
      card_insert_of_notMem (by simp only [mem_insert,mem_singleton]; omega),
      card_insert_of_notMem (by simp only [mem_singleton]; omega),card_singleton]
  have good (t : ℕ) (h : t∈W) : t < p.support.length ∧ G.dist a (p.getVert t)=2 := by
    simp only [W,mem_insert,mem_singleton] at h
    rcases h with rfl|rfl|rfl|rfl <;> constructor <;> first | assumption | omega
  have ls := p.length_support
  have inj : Set.InjOn p.getVert ↑W := by
    intro u hu v hv eq
    have := (good u hu).1
    have := (good v hv).1
    exact hp.getVert_injOn (by change u ≤ p.length; omega) (by change v ≤ p.length; omega) eq
  have sub : W.image p.getVert ⊆ univ.filter (fun z => G.dist a z=2) := by
    intro z h
    obtain ⟨t,ht,rfl⟩ := mem_image.mp h
    exact mem_filter.mpr ⟨mem_univ _,(good t ht).2⟩
  have bad := (card_le_card sub).trans quota
  rw [card_image_of_injOn inj,card] at bad
  omega

#print axioms two_marks_exact
end Graph189ExteriorGap
