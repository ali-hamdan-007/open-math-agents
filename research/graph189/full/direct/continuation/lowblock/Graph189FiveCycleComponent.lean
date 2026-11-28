import Graph189FiveCycleLinks

open Finset SimpleGraph
namespace Graph189FiveCycleComponent
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Among at most four vertices, all components meeting the cycle must
coincide when each such component has at least three vertices. Their
combined anchor set has at most two members, and each anchor begins
a two-vertex tail outside the cycle. -/
theorem layout (W F : Finset V) (small : F.card≤4)
    (two : ∀v∈F,(G.neighborFinset v∩W).card≤2)
    (min : ∀ v∈F, ∀ w∈F, G.Adj v w → 2≤(G.neighborFinset v∩W).card+(G.neighborFinset v∩F).card)
    (strong : ∀ v∈F, (∃ u∈W,G.Adj u v) → 3≤(G.neighborFinset v∩W).card+(G.neighborFinset v∩F).card)
    (unique : ∀ (x y : F), x≠y → (G.induce (F : Set V)).Reachable x y →
      ∀ u∈W, ∀ v∈W, G.Adj u x.val → G.Adj y.val v → u=v) :
    let A := W.filter (fun u => ∃ x∈F, G.Adj u x)
    A.card≤2 ∧ ∀ a∈A, ∃ x∈F, ∃ y∈F, G.Adj a x ∧ G.Adj x y := by
  classical
  let J := G.induce (F : Set V)
  let T (x : F) := F.filter (fun v => ∃ h : v∈F, J.Reachable x ⟨v,h⟩)
  let A := W.filter (fun u => ∃ x∈F, G.Adj u x)
  have linked {x y : F} (xt : ∃ u∈W, G.Adj u x.val) (yt : ∃ u∈W, G.Adj u y.val) : J.Reachable x y := by
    have sx := Graph189FiveCycleLinks.component_three W F two min unique x (strong _ x.property xt)
    have sy := Graph189FiveCycleLinks.component_three W F two min unique y (strong _ y.property yt)
    change 3≤(T x).card at sx
    change 3≤(T y).card at sy
    by_contra no
    have d : Disjoint (T x) (T y) := disjoint_left.mpr (by
      intro v vx vy
      obtain ⟨h,xv⟩ := (mem_filter.mp vx).2
      obtain ⟨_,yv⟩ := (mem_filter.mp vy).2
      exact no (xv.trans yv.symm))
    have bound := card_le_card (show T x∪T y⊆F from union_subset (filter_subset _ _) (filter_subset _ _))
    rw [card_union_of_disjoint d] at bound
    omega
  have card : A.card≤2 := by
    rcases A.eq_empty_or_nonempty with emp|⟨a,ha⟩
    · simp [emp]
    obtain ⟨aw,x,xf,ax⟩ := mem_filter.mp ha
    let X : F := ⟨x,xf⟩
    by_cases other : ∃ y∈F, y≠x ∧ ∃ b∈W,G.Adj b y
    · obtain ⟨y,yf,yx,b,bw,yb⟩ := other
      let Y : F := ⟨y,yf⟩
      have ne : X≠Y := fun h => yx (congrArg Subtype.val h).symm
      have link := linked (x:=X) (y:=Y) ⟨a,aw,ax⟩ ⟨b,bw,yb⟩
      have same : a=b := unique X Y ne link a aw b bw ax yb.symm
      have singleton : A⊆{a} := by
        intro c cm
        obtain ⟨cw,z,zf,cz⟩ := mem_filter.mp cm
        let Z : F := ⟨z,zf⟩
        apply mem_singleton.mpr
        by_cases zx : z=x
        · subst z
          exact (unique X Y ne link _ cw b bw cz yb.symm).trans same.symm
        have zn : Z≠X := fun e => zx (congrArg Subtype.val e)
        exact unique Z X zn (linked ⟨c,cw,cz⟩ ⟨a,aw,ax⟩) c cw a aw cz ax.symm
      have n := card_le_card singleton
      rw [card_singleton] at n
      omega
    · have inc : A⊆G.neighborFinset x∩W := by
        intro c cm
        obtain ⟨cw,y,yf,cy⟩ := mem_filter.mp cm
        have same : y=x := by
          by_contra ne
          exact other ⟨y,yf,ne,c,cw,cy⟩
        exact mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr (same ▸ cy.symm),cw⟩
      exact (card_le_card inc).trans (two x xf)
  refine ⟨card,?_⟩
  intro a am
  obtain ⟨aw,x,xf,ax⟩ := mem_filter.mp am
  have n := strong x xf ⟨a,aw,ax⟩
  have l := two x xf
  obtain ⟨y,yn⟩ := card_pos.mp (show 0<(G.neighborFinset x∩F).card by omega)
  exact ⟨x,xf,y,(mem_inter.mp yn).2,ax,(G.mem_neighborFinset _ _).mp (mem_inter.mp yn).1⟩

#print axioms layout
end Graph189FiveCycleComponent
