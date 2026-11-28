import Graph189PortLabels
import Graph189CutSides
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance

open Finset SimpleGraph
namespace Graph189BoundaryDebit

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S Y : Finset V}

/-- Each unit of minimum separator size not already supplied by a label
adjacent to x consumes a positive even-distance vertex away from B. -/
theorem even_quota (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (smaller : ∀ T : Finset V, T.card < S.card → (G.induce {u : V | u ∉ T}).Connected)
    {k : ℕ} (cap : ∀ v, G.distEven v ≤ k+1) (sub : Y ⊆ B) {x : V} (hx : x ∈ A) :
    (Y.filter (fun v => Even (G.dist x v))).card + S.card ≤
      k + (Graph189PortLabels.support G S x).card := by
  classical
  let P := Graph189PortLabels.support G S x
  let regions := (univ.filter (fun y => Even (G.dist x y))).erase x
  let E := regions \ B
  let K := P ∪ E
  let W := A.filter (fun y => y = x ∨ G.Adj x y)
  have xw : x ∈ W := mem_filter.mpr ⟨hx,Or.inl rfl⟩
  have xk : x ∉ K := by
    intro h
    rcases mem_union.mp h with p | e
    · exact Finset.disjoint_left.mp sides.left_cut hx (mem_filter.mp p).1
    · exact (mem_erase.mp (mem_sdiff.mp e).1).1 rfl
  have b_free {b : V} (hb : b ∈ B) : b ∉ K := by
    intro h
    rcases mem_union.mp h with p | e
    · exact Finset.disjoint_left.mp sides.right_cut hb (mem_filter.mp p).1
    · exact (mem_sdiff.mp e).2 hb
  have exit {a b : V} (ha : a ∈ W) (hb : b ∉ W) (ab : G.Adj a b) : b ∈ K := by
    obtain ⟨aa,ax⟩ := mem_filter.mp ha
    have nb : b ∉ B := fun h => sides.no_cross a aa b h ab
    by_cases xb : G.Adj x b
    · rcases sides.cover b with ba | bb | bs
      · exact (hb (mem_filter.mpr ⟨ba,Or.inr xb⟩)).elim
      · exact (nb bb).elim
      · exact mem_union_left _ (mem_filter.mpr ⟨bs,xb⟩)
    · have ne : x ≠ b := fun eq => hb (eq ▸ xw)
      have xa : G.Adj x a := ax.resolve_left (fun e => xb (e ▸ ab))
      have two := hc.dist_triangle (u:=x) (v:=a) (w:=b)
      rw [dist_eq_one_iff_adj.mpr xa,dist_eq_one_iff_adj.mpr ab] at two
      have nz : G.dist x b ≠ 0 := fun eq => ne (hc.dist_eq_zero_iff.mp eq)
      have no : G.dist x b ≠ 1 := fun eq => xb (dist_eq_one_iff_adj.mp eq)
      have dist : G.dist x b = 2 := by omega
      have even : Even (G.dist x b) := by rw [dist]; decide
      exact mem_union_right _ (mem_sdiff.mpr ⟨mem_erase.mpr ⟨ne.symm,
        mem_filter.mpr ⟨mem_univ _,even⟩⟩,nb⟩)
  have minbound : S.card ≤ K.card := by
    by_contra! lt
    obtain ⟨b,hb⟩ := sides.right_nonempty
    have bw : b ∉ W := fun h => Finset.disjoint_left.mp sides.apart (mem_filter.mp h).1 hb
    let T : Set V := {v | v ∉ K}
    obtain ⟨walk⟩ := smaller K lt (⟨x,xk⟩ : T) (⟨b,b_free hb⟩ : T)
    obtain ⟨u,v,hu,hv,edge,_⟩ := Graph189CutSides.walk_exits (G := G.induce T)
      (fun v : T => v.val ∈ W) walk xw bw
    exact v.property (exit hu hv edge)
  let Z := Y.filter (fun v => Even (G.dist x v))
  have ez : Disjoint E Z := Finset.disjoint_left.mpr (fun _ a b =>
    (mem_sdiff.mp a).2 (sub (mem_filter.mp b).1))
  have inside : E ∪ Z ⊆ regions := by
    intro v h
    rcases mem_union.mp h with he | hz
    · exact (mem_sdiff.mp he).1
    · obtain ⟨vy,ev⟩ := mem_filter.mp hz
      have ne : v ≠ x := fun eq => Finset.disjoint_left.mp sides.apart hx (eq ▸ sub vy)
      exact mem_erase.mpr ⟨ne,mem_filter.mpr ⟨mem_univ _,ev⟩⟩
  have ezcard := card_le_card inside
  rw [card_union_of_disjoint ez] at ezcard
  have ec := card_erase_of_mem (show x ∈ univ.filter (fun y => Even (G.dist x y)) by simp)
  have capx := cap x
  change (univ.filter (fun y => Even (G.dist x y))).card ≤ k+1 at capx
  have kc : K.card ≤ P.card + E.card := card_union_le _ _
  change Z.card + S.card ≤ k + P.card
  change regions.card = _ at ec
  omega

#print axioms even_quota
end Graph189BoundaryDebit
