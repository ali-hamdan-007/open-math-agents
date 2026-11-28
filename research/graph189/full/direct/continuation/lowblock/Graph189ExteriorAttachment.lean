import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Graph189HallDeficiency

open Finset SimpleGraph
namespace Graph189ExteriorAttachment
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}

/-- Distinct exterior vertices with many neighbors on a path give equally
many distinct attachment positions, even for a path selected with additional
constraints. All edges are edges of the original graph. -/
theorem marks_of_many_neighbors (p : G.Walk x y) (W : Finset V) (j : ℕ)
    (size : j ≤ W.card)
    (rows : ∀ w ∈ W, j ≤ ((univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] w)).card) :
    ∃ marks : Finset (Fin p.support.length), marks.card = j ∧
      ∃ attach : marks ↪ W, ∀ i : marks, G.Adj p.support[i.val.val] (attach i).val := by
  classical
  obtain ⟨U,uw,us⟩ := exists_subset_card_eq size
  let N (w : V) := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] w)
  obtain ⟨f,edges⟩ := Graph189ExteriorGap.hall_on_dense_vertices N j U us (fun w hw => rows w (uw hw))
  let M := (univ : Finset U).image f
  let f' (u : U) : M := ⟨f u,mem_image_of_mem _ (mem_univ _)⟩
  have bij : Function.Bijective f' := by
    constructor
    · intro a b eq; exact f.injective (congrArg Subtype.val eq)
    · intro m
      obtain ⟨u,_,eq⟩ := mem_image.mp m.property
      exact ⟨u,Subtype.ext eq⟩
  let equiv := Equiv.ofBijective f' bij
  let inc : U ↪ W := ⟨fun u => ⟨u.val,uw u.property⟩,
    fun _ _ eq => Subtype.ext (congrArg (fun w : W => w.val) eq)⟩
  have card : M.card = U.card := by simpa using Fintype.card_congr equiv.symm
  refine ⟨M,card.trans us,equiv.symm.toEmbedding.trans inc,?_⟩
  intro m
  have eq : f (equiv.symm m) = m.val := congrArg Subtype.val (equiv.apply_symm_apply m)
  have edge := (mem_filter.mp (edges (equiv.symm m))).2
  rw [eq] at edge
  exact edge

#print axioms marks_of_many_neighbors
end Graph189ExteriorAttachment
