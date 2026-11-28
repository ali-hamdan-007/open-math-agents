import Graph189FourTail
import Graph189FourExterior
import Graph189ThreeOriginal

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189FourTiedOriginal
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The registered Graph 189 hypotheses imply traceability whenever the
two smallest entries of the degree sequence are both four. -/
theorem traceable_tied_four (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (least : G.minDegree=4) (degree : G.secondSmallestDegree=4) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have localCap (v : V) : G.distEven v ≤ 1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  by_cases short : Fintype.card V ≤ 2*G.secondSmallestDegree+2
  · exact OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.theorem_C hc localCap short
  by_cases uncut : ∀ z : V, (G.induce {v : V | v≠z}).Connected
  · have minimum (v : V) : 4 ≤ G.degree v := least ▸ G.minDegree_le_degree v
    have order := Graph189OrderBound.order_le hc cap
    rw [least,degree] at order
    norm_num at order
    have quota (v : V) : (univ.filter (fun w => G.dist v w=2)).card ≤ 4 := by
      let T := univ.filter (fun w => G.dist v w=2)
      have self : v∉T := by simp [T]
      have sub : insert v T ⊆ univ.filter (fun w => Even (G.dist v w)) := by
        intro w hw
        rcases mem_insert.mp hw with rfl|h
        · simp
        · exact mem_filter.mpr ⟨mem_univ _,by rw [(mem_filter.mp h).2]; decide⟩
      have bound := card_le_card sub
      rw [card_insert_of_notMem self] at bound
      change T.card+1 ≤ G.distEven v at bound
      have := localCap v
      change T.card ≤ 4
      omega
    have cuts (U : Finset V) (small : U.card < 2) : (G.induce {v : V | v∉U}).Connected := by
      by_cases empty : U=∅
      · subst U
        rw [show {v : V | v∉(∅ : Finset V)}=Set.univ by ext; simp]
        exact hc.map G.induceUnivIso.symm.toHom G.induceUnivIso.symm.surjective
      obtain ⟨v,rfl⟩ := card_eq_one.mp (show U.card=1 by have := card_pos.mpr (nonempty_iff_ne_empty.mpr empty); omega)
      rw [show {w : V | w∉({v} : Finset V)}={w : V | w≠v} by ext; simp]
      exact uncut v
    obtain ⟨x⟩ := hc.nonempty
    obtain ⟨a,b,p,hp,longest⟩ := Graph189ThreeRegularMinimum.longest_path (G:=G) x
    refine ⟨a,b,p,hp.isHamiltonian_of_mem (fun v => ?_)⟩
    by_contra missing
    have lower := high_outside_order_gap p hp longest missing (quota v) (minimum v)
      (fun w => by have := minimum w; omega) (fun u _ hu _ => by have := minimum u; omega)
    have upper := Graph189FourExterior.fewer_than_four p hp longest cuts minimum quota order
    have total := card_add_card_compl p.support.toFinset
    rw [List.toFinset_card_of_nodup hp.support_nodup] at total
    exact Graph189FourTriangle.no_three_omitted p hp longest minimum quota order (by omega)
  · push Not at uncut
    exact Graph189CutH1.cut_vertex_case G hc localCap (by omega) uncut

#print axioms traceable_tied_four
end Graph189FourTiedOriginal
