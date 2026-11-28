import Graph189ExteriorAttachment

open Finset SimpleGraph

namespace Graph189ExteriorAttachment

/-- A family of more than j vertices with at least j contacts apiece has a
matching of j+1 distinct path positions as soon as their union has more than
j positions. The returned injection assigns each position its incident vertex. -/
theorem extra_port {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (p : G.Walk x y) (W : Finset V) (j : ℕ) (many : j < W.card)
    (rows : ∀ w ∈ W, j ≤ ((univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] w)).card)
    (cover : j < (W.biUnion (fun w => (univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] w))).card) :
    ∃ marks : Finset (Fin p.support.length), marks.card = j+1 ∧
      ∃ attach : marks ↪ W, ∀ i : marks, G.Adj p.support[i.val.val] (attach i).val := by
  classical
  let N (w : V) := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] w)
  let F (w : W) := N w.val
  have size : Fintype.card W = W.card := Fintype.card_coe W
  have whole : (univ.biUnion F).card = (W.biUnion N).card := by
    congr 1
    ext i
    constructor
    · intro hi
      obtain ⟨w,_,hw⟩ := mem_biUnion.mp hi
      exact mem_biUnion.mpr ⟨w.val,w.property,hw⟩
    · intro hi
      obtain ⟨w,hw,edge⟩ := mem_biUnion.mp hi
      exact mem_biUnion.mpr ⟨⟨w,hw⟩,mem_univ _,edge⟩
  have hall (T : Finset W) : T.card ≤ (T.biUnion F).card + (Fintype.card W-(j+1)) := by
    by_cases all : T=univ
    · rw [all,card_univ,whole,size]
      change j < (W.biUnion N).card at cover
      omega
    rcases T.eq_empty_or_nonempty with rfl | ⟨w,hw⟩
    · simp
    have proper : T.card < W.card := by
      by_contra! h
      exact all (Finset.eq_of_subset_of_card_le (subset_univ _) (by simpa using h))
    have incl : F w ⊆ T.biUnion F := fun i hi => mem_biUnion.mpr ⟨w,hw,hi⟩
    have lower := (rows w.val w.property).trans (card_le_card incl)
    omega
  obtain ⟨U,large,f,edge⟩ := Graph189ExteriorGap.hall_at_least F (j+1) (by omega) hall
  obtain ⟨B,sub,cardB⟩ := exists_subset_card_eq large
  let inc : B ↪ U := ⟨fun b => ⟨b.val,sub b.property⟩,
    fun _ _ e => Subtype.ext (congrArg (fun w : U => w.val) e)⟩
  let pos := inc.trans f
  let M := (univ : Finset B).image pos
  let chosen (b : B) : M := ⟨pos b,mem_image_of_mem _ (mem_univ _)⟩
  have bij : Function.Bijective chosen := by
    constructor
    · intro u v eq
      exact pos.injective (congrArg Subtype.val eq)
    · intro i
      obtain ⟨b,_,eq⟩ := mem_image.mp i.property
      exact ⟨b,Subtype.ext eq⟩
  let equiv := Equiv.ofBijective chosen bij
  let vertex : B ↪ W := ⟨Subtype.val,Subtype.val_injective⟩
  have card : M.card = B.card := by simpa using Fintype.card_congr equiv.symm
  refine ⟨M,card.trans cardB,equiv.symm.toEmbedding.trans vertex,?_⟩
  intro i
  have value : pos (equiv.symm i) = i.val := congrArg Subtype.val (equiv.apply_symm_apply i)
  have adj := (mem_filter.mp (edge (inc (equiv.symm i)))).2
  change G.Adj p.support[(pos (equiv.symm i)).val] (equiv.symm i).val.val at adj
  exact (congrArg (fun index : Fin p.support.length =>
    G.Adj (p.support.get index) (equiv.symm i).val.val) value).mp adj

#print axioms extra_port
end Graph189ExteriorAttachment
