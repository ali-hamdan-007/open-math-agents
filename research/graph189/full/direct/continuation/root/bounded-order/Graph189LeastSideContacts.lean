import Graph189SmallMixedOrders
import Graph189BoundaryMatching

open SimpleGraph Finset
namespace Graph189SmallMixedPair
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

/-- If a separator vertex has just one contact in a globally least side,
replace that separator vertex by the contact. The new side is smaller. -/
theorem least_two_marks (sides : Graph189CutSides.CutSides G A B S) (pair : S={p,q}) (ne : p≠q)
    (sc : S.card≤G.vertexConnectivity) (two : 2≤A.card)
    (least : ∀ C D T,Graph189CutSides.CutSides G C D T → T.card=2 → A.card≤C.card) :
    2≤(A.filter (G.Adj p)).card := by
  classical
  have ps : p∈S := by simp [pair]
  have qs : q∈S := by simp [pair]
  obtain ⟨⟨x,xa,xp⟩,_⟩ := sides.contacts_of_minimum (fun T h => Graph189CutSides.connected_after_smaller_deletion T (h.trans_le sc)) ps
  by_contra! few
  have only : ∀v∈A,G.Adj p v → v=x := by
    intro v va pv
    exact card_le_one.mp (by omega : (A.filter (G.Adj p)).card≤1) v (mem_filter.mpr ⟨va,pv⟩) x (mem_filter.mpr ⟨xa,xp.symm⟩)
  have xq : x≠q := fun eq => disjoint_left.mp sides.left_cut xa (eq ▸ qs)
  have xnp : x≠p := fun eq => disjoint_left.mp sides.left_cut xa (eq ▸ ps)
  have cnt := card_erase_add_one xa
  have cut : Graph189CutSides.CutSides G (A.erase x) (insert p B) {x,q} := by
    refine ⟨card_pos.mp (by omega),⟨p,mem_insert_self _ _⟩,?_,?_,?_,?_,?_⟩
    · refine disjoint_left.mpr (fun v hv hi => ?_)
      rcases mem_insert.mp hi with rfl|h
      · exact disjoint_left.mp sides.left_cut (mem_erase.mp hv).2 ps
      · exact disjoint_left.mp sides.apart (mem_erase.mp hv).2 h
    · refine disjoint_left.mpr (fun v hv hi => ?_)
      rcases (show v=x ∨ v=q by simpa using hi) with h|rfl
      · exact (mem_erase.mp hv).1 h
      · exact disjoint_left.mp sides.left_cut (mem_erase.mp hv).2 qs
    · refine disjoint_left.mpr (fun v hv hi => ?_)
      rcases (show v=x ∨ v=q by simpa using hi) with rfl|rfl
      · exact (mem_insert.mp hv).elim xnp (fun h => disjoint_left.mp sides.apart xa h)
      · exact (mem_insert.mp hv).elim ne.symm (fun h => disjoint_left.mp sides.right_cut h qs)
    · intro v
      rcases sides.cover v with h|h|h
      · by_cases eq : v=x
        · exact Or.inr (Or.inr (by simp [eq]))
        · exact Or.inl (mem_erase.mpr ⟨eq,h⟩)
      · exact Or.inr (Or.inl (mem_insert_of_mem h))
      · rcases (show v=p ∨ v=q by simpa [pair] using h) with rfl|rfl <;> simp
    · intro u hu v hv e
      rcases mem_insert.mp hv with rfl|vb
      · exact (mem_erase.mp hu).1 (only _ (mem_erase.mp hu).2 e.symm)
      · exact sides.no_cross _ (mem_erase.mp hu).2 _ vb e
  have no := least _ _ _ cut (by simp [xq])
  omega

theorem two_side_ports (sides : Graph189CutSides.CutSides G A B S) (sz : S.card=2)
    (sc : S.card≤G.vertexConnectivity) (two : 2≤A.card) : 2≤(ports G A S).card := by
  classical
  obtain ⟨T,ts,tm,f,edges⟩ := Graph189ExteriorGap.matching_at_component_boundary S A sides.left_cut.symm
    (fun x xa y ya e => by
      rcases sides.cover y with h|h|h
      · exact (ya h).elim
      · exact (sides.no_cross _ xa _ h e).elim
      · exact h) sz.ge two (fun cut lt => Graph189CutSides.connected_after_smaller_deletion cut (by omega))
  let embed : T ↪ (ports G A S) := ⟨fun i => ⟨(f i).val,mem_filter.mpr ⟨(f i).property,i.val,ts i.property,edges i⟩⟩,
    fun i j e => f.injective (Subtype.ext (congrArg (fun w : (ports G A S) => w.val) e))⟩
  have h := Fintype.card_le_of_embedding embed
  rw [Fintype.card_coe,Fintype.card_coe] at h
  omega

end Graph189SmallMixedPair
#print axioms Graph189SmallMixedPair.least_two_marks
#print axioms Graph189SmallMixedPair.two_side_ports
