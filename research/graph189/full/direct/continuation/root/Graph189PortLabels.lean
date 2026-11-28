import Graph189SupportClassification
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace Graph189PortLabels
open Finset

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The actual anchor labels touched by a vertex. -/
def support (S : Finset V) (v : V) := S.filter (G.Adj v)

/-- The possible high-port patterns if each port has at most one label
absent at any other port. Ranges over the whole family at once. -/
theorem classify (A S : Finset V)
    (close : ∀ i ∈ A, ∀ j ∈ A, (support G S i \ support G S j).card ≤ 1) :
    (∀ i ∈ A, ((support G S i).filter (fun z => ∃ j ∈ A, ¬ G.Adj j z)).card ≤ 1) ∨
    (∀ i ∈ A, (S.filter (fun z => ¬ G.Adj i z ∧ ∃ j ∈ A, G.Adj j z)).card ≤ 1) := by
  classical
  let H (i : ↥A) (a : ↥S) := G.Adj i.val a.val
  have near : Graph189SupportClassification.OneDifference H := by
    intro i j a b hia hja hib hjb
    apply Subtype.ext
    apply (card_le_one_iff.mp (close i.val i.property j.val j.property))
    · exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨a.property,hia⟩,fun ha => hja (mem_filter.mp ha).2⟩
    · exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨b.property,hib⟩,fun hb => hjb (mem_filter.mp hb).2⟩
  rcases Graph189SupportClassification.classify near with small | large
  · left
    intro i hi
    apply card_le_one_iff.mpr
    intro a b ha hb
    obtain ⟨ha,ja,hja,hnja⟩ := mem_filter.mp ha
    obtain ⟨hb,jb,hjb,hnjb⟩ := mem_filter.mp hb
    obtain ⟨has,hia⟩ := mem_filter.mp ha
    obtain ⟨hbs,hib⟩ := mem_filter.mp hb
    exact congrArg Subtype.val (small ⟨i,hi⟩ ⟨a,has⟩ ⟨b,hbs⟩ hia
      ⟨⟨ja,hja⟩,hnja⟩ hib ⟨⟨jb,hjb⟩,hnjb⟩)
  · right
    intro i hi
    apply card_le_one_iff.mpr
    intro a b ha hb
    obtain ⟨has,hnia,ja,hja,hja'⟩ := mem_filter.mp ha
    obtain ⟨hbs,hnib,jb,hjb,hjb'⟩ := mem_filter.mp hb
    exact congrArg Subtype.val (large ⟨i,hi⟩ ⟨a,has⟩ ⟨b,hbs⟩
      ⟨⟨ja,hja⟩,hja'⟩ hnia ⟨⟨jb,hjb⟩,hjb'⟩ hnib)

#print axioms classify
end Graph189PortLabels
