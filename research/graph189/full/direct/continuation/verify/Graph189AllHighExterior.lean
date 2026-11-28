import Graph189ProtectedExteriorDegree
import Graph189PrescribedBatch
import Graph189ExteriorPopulation

open SimpleGraph Finset Graph189ExteriorDegreeCycle
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

namespace Graph189AllHighExterior
open Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}

/-- Each vertex outside a longest path with all omitted vertices above the second-degree threshold retains
at least half the second-smallest degree, rounded down, in the exterior. -/
theorem minimum (p : G.Walk a b) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    (positive : 0 < G.secondSmallestDegree)
    (high : ∀ {v : V}, v∉p.support → G.secondSmallestDegree≤G.degree v)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) (x : (p.support.toFinsetᶜ : Finset V)) :
    G.secondSmallestDegree / 2 ≤ (G.induce ((p.support.toFinsetᶜ : Finset V) : Set V)).degree x := by
  classical
  let P := p.support.toFinset
  let E := Pᶜ
  let k := G.secondSmallestDegree
  have quota (v : V) : (univ.filter (fun y => G.dist v y = 2)).card ≤ k := by
    let T := univ.filter (fun y => G.dist v y = 2)
    have miss : v ∉ T := by simp [T]
    have sub : insert v T ⊆ univ.filter (fun y => Even (G.dist v y)) := by
      intro y hy
      rcases mem_insert.mp hy with rfl | h
      · simp
      · exact mem_filter.mpr ⟨mem_univ _,by rw [(mem_filter.mp h).2]; decide⟩
    have h := card_le_card sub
    rw [card_insert_of_notMem miss] at h
    change T.card+1 ≤ G.distEven v at h
    have capv := cap v
    change G.distEven v ≤ k+1 at capv
    change T.card ≤ k
    omega
  have outside : x.val ∉ p.support := fun h => (mem_compl.mp x.property) (List.mem_toFinset.mpr h)
  have gram : ((G.neighborFinset x.val).filter (fun u => u ∈ (E : Set V))) = G.neighborFinset x.val \ P := by
    ext v
    simp [E]
  change k/2 ≤ (G.induce (E : Set V)).degree x
  rw [degree_induce_filter,gram]
  obtain ⟨y,hy⟩ : (G.neighborFinset x.val \ P).Nonempty := by
    apply Classical.byContradiction
    intro empty
    have sub : G.neighborFinset x.val ⊆ P := by
      intro v hv
      by_contra out
      exact empty ⟨v,mem_sdiff.mpr ⟨hv,out⟩⟩
    have eq : (contactPositions p x.val).card = G.degree x.val := by
      rw [contact_card_neighbors p hp]
      change (G.neighborFinset x.val ∩ P).card = G.degree x.val
      rw [inter_eq_left.mpr sub, G.card_neighborFinset_eq_degree]
    have hx := high outside
    have pos : (contactPositions p x.val).Nonempty := card_pos.mp (by change 0 < k at positive; omega)
    have shift := protected_single_shell p hp t longest outside pos
    have shell : P.filter (fun y => G.dist x.val y=2) ⊆ univ.filter (fun y => G.dist x.val y=2) :=
      filter_subset_filter _ (subset_univ _)
    have count := (card_le_card shell).trans (quota _)
    change (contactPositions p x.val).card + 1 ≤ (P.filter _).card at shift
    omega
  have outy : y ∉ p.support := fun h => (mem_sdiff.mp hy).2 (List.mem_toFinset.mpr h)
  have bound := protected_half_degree p hp t longest outside outy
    ((G.mem_neighborFinset _ _).mp (mem_sdiff.mp hy).1) (quota _) (high outy)
  have := high outside
  change G.degree x.val ≤ 2*(G.neighborFinset x.val \ P).card+1 at bound
  omega


#print axioms minimum
end Graph189AllHighExterior
