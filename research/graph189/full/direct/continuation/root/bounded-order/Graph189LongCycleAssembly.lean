import Graph189DenseTerminal
import Graph189FanCycle

open SimpleGraph Finset Graph189OptimalExterior Graph189ExteriorGap
namespace Graph189ExteriorLeaf
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The strict larger-order case of the one-exception circumference theorem,
stated on induced subgraphs in the original vertex type. -/
def LongCycles (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀(S : Finset V)(z : V),z∈S → ∀q : ℕ,3≤S.card → 2*q<S.card →
    (∀u∈S,(G.induce (S.erase u:Set V)).Preconnected) →
    (∀u∈S,u≠z → q≤(G.neighborFinset u∩S).card) →
    ∃a,∃Q : G.Walk a a,Q.IsCycle ∧ (∀v∈Q.support,v∈S) ∧ 2*q≤Q.length

omit [Nontrivial V] in
private theorem circumference (long : LongCycles G) (S : Finset V) (z : V) (zs : z∈S)
    (q : ℕ) (three : 3≤S.card) (two : ∀u∈S,(G.induce (S.erase u:Set V)).Preconnected)
    (deg : ∀u∈S,u≠z → q≤(G.neighborFinset u∩S).card) :
    ∃a,∃Q : G.Walk a a,Q.IsCycle ∧ (∀v∈Q.support,v∈S) ∧ min S.card (2*q)≤Q.length := by
  by_cases small : S.card≤2*q
  · obtain ⟨a,Q,cycle,inside,len⟩ := Graph189FanCycle.induced_small_cycle S zs three small two deg
    exact ⟨a,Q,cycle,inside,len.symm ▸ min_le_left _ _⟩
  obtain ⟨a,Q,cycle,inside,len⟩ := long S z zs q three (by omega) two deg
  exact ⟨a,Q,cycle,inside,(min_le_right _ _).trans len⟩

/-- Both component types now close from the single classical strict circumference
input. All graph data, choices of endblock and minimizing degrees are produced here. -/
theorem three_connected_of_long_cycles (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (lo : 7≤G.secondSmallestDegree) (hi : G.secondSmallestDegree≤21)
    (upper : Fintype.card V≤5*G.secondSmallestDegree-5) (minimum : 3≤G.minDegree)
    (conn : 3≤G.vertexConnectivity) (long : LongCycles G) : ∃a b,∃Q : G.Walk a b,Q.IsHamiltonian := by
  classical
  by_contra bad
  let k := G.secondSmallestDegree
  obtain ⟨a,b,p,C,h⟩ := choose hc cap (by omega) minimum bad
  have point (v : V) : G.distEven v≤1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have quota := Graph189OrdinaryPathGap.second_layer_budget point
  have unique (u v : V) (hu : G.degree u<k) (hv : G.degree v<k) : u=v := by
    by_contra ne
    exact (OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) u v ne).elim
      (Nat.not_le_of_gt hu) (Nat.not_le_of_gt hv)
  have minDeg (v : V) := minimum.trans (G.minDegree_le_degree v)
  have gap : p.support.length+(k+1)/2+1<Fintype.card V := by
    by_contra! short
    exact bad (Graph189OrdinaryPathGap.traceable_of_near_unrestricted hc point (by omega) minimum p h.path short)
  obtain ⟨v,vc,vh⟩ := h.high
  obtain ⟨z,zc,others⟩ : ∃z∈C,∀u∈C,u≠z → k≤G.degree u := by
    by_cases ex : ∃u∈C,G.degree u<k
    · obtain ⟨z,zc,low⟩ := ex
      exact ⟨z,zc,fun u _ ne => Nat.le_of_not_lt (fun miss => ne (unique _ _ miss low))⟩
    exact ⟨v,vc,fun u uc _ => Nat.le_of_not_lt (fun miss => ex ⟨_,uc,miss⟩)⟩
  let N (x : V) := (G.neighborFinset x∩C).card
  by_cases cut : ∃w∈C,¬(G.induce (C.erase w:Set V)).Preconnected
  · obtain ⟨D,w,L,avoid,interior,noncut⟩ := exists_leaf h.connected z cut
    have all (u : V) (ud : u∈D) : k≤G.degree u := others _ (L.sub ud) (fun eq => avoid (eq ▸ ud))
    obtain ⟨x,xd,least⟩ := D.exists_min_image N L.nonempty
    by_cases short : D.card+3≤2*N x
    · exact no_short_leaf h L conn (fun u ud => (noncut u ud).2) all
        (fun u ud => short.trans (Nat.mul_le_mul_left _ (least u ud))) lo hi upper quota minDeg unique
    let B := insert w D
    have sub : B⊆C := insert_subset L.gate L.sub
    have card : B.card=D.card+1 := card_insert_of_notMem L.fresh
    have localEq (u : V) (ud : u∈D) : (G.neighborFinset u∩B)=(G.neighborFinset u∩C) := by
      apply Subset.antisymm (inter_subset_inter_left sub)
      intro y hy
      have e := (G.mem_neighborFinset _ _).mp (mem_inter.mp hy).1
      exact mem_inter.mpr ⟨(mem_inter.mp hy).1,mem_insert.mpr (L.exits _ ud _ (mem_inter.mp hy).2 e).symm⟩
    have half := (all _ xd).trans (internal_half h (L.sub xd) (all _ xd) (quota _) minDeg unique)
    change k≤2*N x at half
    have lim := card_le_card (inter_subset_right (s₁:=G.neighborFinset x) (s₂:=B))
    rw [localEq _ xd] at lim
    change N x≤B.card at lim
    change 7≤k at lo
    obtain ⟨c,Q,cycle,inside,len⟩ := circumference long B w (mem_insert_self _ _) (N x) (by omega) (by
      intro u ub
      rcases mem_insert.mp ub with eq|ud
      · subst u
        have erase : B.erase w=D := erase_insert L.fresh
        rwa [erase]
      exact (noncut _ ud).2) (by
      intro u ub ne
      have ud : u∈D := (mem_insert.mp ub).resolve_left ne
      rw [localEq _ ud]; exact least _ ud)
    apply no_long_leaf_cycle h L conn xd (all _ xd) (noncut _ xd).1 _ Q cycle (fun u mem => sub (inside u mem)) _ lo hi upper quota minDeg unique
    · change 2*N x≤D.card+2; omega
    · change 2*N x≤Q.length+1; omega
  have two (w : V) (wc : w∈C) : (G.induce (C.erase w:Set V)).Preconnected :=
    Classical.byContradiction (fun fail => cut ⟨_,wc,fail⟩)
  let H := C.filter (fun u => k≤G.degree u)
  obtain ⟨x,xH,least⟩ := H.exists_min_image N ⟨v,mem_filter.mpr ⟨vc,vh⟩⟩
  obtain ⟨xc,xh⟩ := mem_filter.mp xH
  by_cases large : 2*N x≤C.card
  · have half := xh.trans (internal_half h xc xh (quota _) minDeg unique)
    change k≤2*N x at half
    change 7≤k at lo
    obtain ⟨c,Q,cycle,inside,len⟩ := circumference long C z zc (N x) (by omega) two
      (fun u uc ne => least u (mem_filter.mpr ⟨uc,others u uc ne⟩))
    rw [min_eq_right large] at len
    exact no_large_component h conn two xc xh large Q cycle inside len lo hi upper quota minDeg unique
  apply no_dense_component h _ lo upper (Or.inl conn) quota minDeg unique gap
  intro u uc uh
  have low := least u (mem_filter.mpr ⟨uc,uh⟩)
  change C.card+1≤2*N u
  omega

end Graph189ExteriorLeaf
#print axioms Graph189ExteriorLeaf.three_connected_of_long_cycles
