import Graph189OptimalMidpoint
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

open SimpleGraph Finset
namespace Graph189OptimalExterior
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Every edge of the omitted induced graph lies in one part of a maximizing
partition. Together with preconnectedness this identifies the nonempty parts
with the actual exterior components. -/
theorem same_part {U : Finset V} {F : V→Finset V} (part : Partition G U F)
    (best : ∀K : V→Finset V,Partition G U K → score K≤score F)
    {i j x y : V} (xi : x∈F i) (yj : y∈F j) (edge : G.Adj x y) : i=j := by
  classical
  by_contra different
  have diff : i≠j := different
  let K (l : V) := if l=i then ∅ else if l=j then F i ∪ F j else F l
  have ki : K i=∅ := by simp [K]
  have kj : K j=F i∪F j := by simp [K,diff.symm]
  have other {l : V} (li : l≠i) (lj : l≠j) : K l=F l := by simp [K,li,lj]
  have unique {l l' v : V} (h : v∈F l) (h' : v∈F l') : l=l' := by
    by_contra ne
    exact Finset.disjoint_left.mp (part.separate l l' ne) h h'
  let dest (l : V) := if l=i then j else l
  have transfer {v l : V} (m : v∈F l) : v∈K (dest l) := by
    by_cases li : l=i
    · subst l; simpa [dest,kj] using (mem_union_left (F j) m)
    by_cases lj : l=j
    · subst l; simpa [dest,diff.symm,kj] using (mem_union_right (F i) m)
    simpa [dest,li,other li lj] using m
  have origin {v l : V} (m : v∈K l) : ∃t,v∈F t ∧ dest t=l := by
    by_cases li : l=i
    · subst l; simp [ki] at m
    by_cases lj : l=j
    · subst l; rw [kj] at m
      rcases mem_union.mp m with h|h
      · exact ⟨i,h,by simp [dest]⟩
      · exact ⟨j,h,by simp [dest,diff.symm]⟩
    exact ⟨l,other li lj ▸ m,by simp [dest,li]⟩
  have next : Partition G U K := by
    constructor
    · intro v
      rw [part.cover]
      constructor
      · rintro ⟨l,m⟩; exact ⟨dest l,transfer m⟩
      rintro ⟨l,m⟩
      obtain ⟨t,ht,_⟩ := origin m
      exact ⟨t,ht⟩
    · intro l l' ne
      apply Finset.disjoint_left.mpr
      intro v vl vl'
      obtain ⟨t,vt,tl⟩ := origin vl
      obtain ⟨s,vs,sl⟩ := origin vl'
      exact ne (tl.symm.trans ((congrArg dest (unique vt vs)).trans sl))
    · intro l
      by_cases li : l=i
      · subst l; rw [ki]; intro z; exact False.elim (notMem_empty _ z.property)
      by_cases lj : l=j
      · subst l
        rw [kj,coe_union]
        exact (G.connected_induce_union (part.connected i) (part.connected j) xi yj edge).preconnected
      rw [other li lj]; exact part.connected l
  let S := (univ.erase i).erase j
  have jin : j∈univ.erase i := mem_erase.mpr ⟨diff.symm,mem_univ _⟩
  have sums (T : V→Finset V) : (∑l∈S,(T l).card^2)+(T j).card^2+(T i).card^2=score T := by
    rw [show (∑l∈S,(T l).card^2)+(T j).card^2=∑l∈univ.erase i,(T l).card^2 from
      sum_erase_add _ (fun l => (T l).card^2) jin]
    exact sum_erase_add _ (fun l => (T l).card^2) (mem_univ _)
  have rem : (∑l∈S,(K l).card^2)=∑l∈S,(F l).card^2 := by
    apply sum_congr rfl
    intro l hl
    rw [other (mem_erase.mp (mem_erase.mp hl).2).1 (mem_erase.mp hl).1]
  have bound := best K next
  rw [←sums K,←sums F,rem,ki,kj,card_union_of_disjoint (part.separate _ _ diff),card_empty] at bound
  have positive := Nat.mul_pos (card_pos.mpr ⟨x,xi⟩) (card_pos.mpr ⟨y,yj⟩)
  nlinarith

end Graph189OptimalExterior
#print axioms Graph189OptimalExterior.same_part
