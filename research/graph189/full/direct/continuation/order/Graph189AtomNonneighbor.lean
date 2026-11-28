import Graph189CriticalConnectivity

open Finset SimpleGraph Graph189CutSides Graph189UniversalCycle
namespace Graph189AtomNonneighbor
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A low vertex at the extremal cut-degree bound misses an entire edge to
some vertex outside every minimum cut. The witness lies in a genuine atom. -/
theorem free_nonneighbor (z : V)
    {U W T : Finset V} (given : CutSides G U W T) (size : T.card=G.vertexConnectivity) (onCut : z∈T)
    (room : G.vertexConnectivity<Fintype.card V-1)
    (large : 3*G.vertexConnectivity<2*(G.minDegree+1))
    (low : G.degree z<G.secondSmallestDegree)
    (deficit : G.degree z+G.vertexConnectivity≤G.secondSmallestDegree+1) :
    ∃ w : V, w≠z ∧ ¬G.Adj z w ∧
      G.vertexConnectivity+1≤(completeAt G w).vertexConnectivity := by
  classical
  let s := G.vertexConnectivity
  let family : Finset (Finset V) := univ.filter fun X => ∃ B S : Finset V, S.card=s ∧ CutSides G X B S
  have init : U∈family := mem_filter.mpr ⟨mem_univ _,W,T,size,given⟩
  obtain ⟨A,hA,smallest⟩ := family.exists_min_image Finset.card ⟨U,init⟩
  obtain ⟨B,S,sz,cut⟩ := (mem_filter.mp hA).2
  have minimal {X Y Z : Finset V} (c : CutSides G X Y Z) : S.card≤Z.card := by
    by_contra! smaller
    exact Graph189CriticalConnectivity.disconnected c (connected_after_smaller_deletion Z (smaller.trans_eq sz))
  have atom {X Y Z : Finset V} (c : CutSides G X Y Z) (eq : Z.card=S.card) : A.card≤X.card :=
    smallest X (mem_filter.mpr ⟨mem_univ _,Y,Z,eq.trans sz,c⟩)
  obtain ⟨a,ha⟩ := cut.left_nonempty
  have deg := Graph189Removable.degree_in_side cut ha
  have min := G.minDegree_le_degree a
  have free {v : V} (va : v∈A) {X Y Z : Finset V} (other : CutSides G X Y Z) (eq : Z.card=s) :
      v∉Z := by
    intro mem
    have bound := (Graph189Atom.in_cut cut other (eq.trans sz.symm) minimal atom
      (show (A∩Z).Nonempty from ⟨v,mem_inter.mpr ⟨va,mem⟩⟩)).2
    change 3*s<2*(G.minDegree+1) at large
    omega
  have za : z∉A := fun h => free h given size onCut
  have ahigh := (OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair
    (G:=G) a z (fun e => za (e ▸ ha))).resolve_right (not_le.mpr low)
  have non : ∃ w∈A, ¬G.Adj z w := by
    by_contra! every
    have zs : z∈S := by
      rcases cut.cover z with left|right|center
      · exact (za left).elim
      · exact (cut.no_cross a ha z right (every a ha).symm).elim
      · exact center
    have small (L : Finset V) (lt : L.card<S.card) : (G.induce {v : V | v∉L}).Connected :=
      connected_after_smaller_deletion L (lt.trans_eq sz)
    obtain ⟨b,hb,bz⟩ := (cut.contacts_of_minimum small zs).2
    have fresh : b∉A := fun h => Finset.disjoint_left.mp cut.apart h hb
    have inc : insert b A ⊆ G.neighborFinset z := by
      intro v hv
      apply (G.mem_neighborFinset _ _).mpr
      rcases mem_insert.mp hv with rfl|h
      · exact bz.symm
      · exact every v h
    have count := card_le_card inc
    rw [card_insert_of_notMem fresh,G.card_neighborFinset_eq_degree] at count
    change G.degree z+s≤G.secondSmallestDegree+1 at deficit
    omega
  obtain ⟨w,wa,missing⟩ := non
  refine ⟨w,fun eq => za (eq ▸ wa),missing,completeAt_connectivity_add_one w room ?_⟩
  intro K ks wk
  by_contra bad
  have survive : ∃ v, v∉K := by
    by_contra! all
    have eq := eq_univ_iff_forall.mpr all
    rw [eq,card_univ] at ks
    omega
  obtain ⟨X,Y,c⟩ := exists_cutSides_of_disconnected K survive bad
  exact free wa c ks wk

/-- Completing at a nonneighbor raises a one-below-second-degree vertex
and preserves the degrees of every other high vertex. -/
theorem repaired_minDegree (z w : V) (ne : w≠z) (missing : ¬G.Adj z w)
    (low : G.degree z+1=G.secondSmallestDegree) :
    G.secondSmallestDegree≤(completeAt G w).minDegree := by
  classical
  let K := completeAt G w
  obtain ⟨u,mu⟩ := K.exists_minimal_degree_vertex
  change G.secondSmallestDegree≤K.minDegree
  rw [mu]
  by_cases eq : u=z
  · subst u
    have add : insert w (G.neighborFinset z) ⊆ K.neighborFinset z := by
      intro t ht
      apply (K.mem_neighborFinset _ _).mpr
      rcases mem_insert.mp ht with rfl|h
      · exact Or.inr ⟨Or.inr rfl,ne.symm⟩
      · exact Or.inl ((G.mem_neighborFinset _ _).mp h)
    have count := card_le_card add
    rw [card_insert_of_notMem (fun h => missing ((G.mem_neighborFinset _ _).mp h)),
      G.card_neighborFinset_eq_degree,K.card_neighborFinset_eq_degree,low] at count
    exact count
  have high := (OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair
    (G:=G) u z eq).resolve_right (by omega)
  exact high.trans (degree_le_completeAt w u)

end Graph189AtomNonneighbor
#print axioms Graph189AtomNonneighbor.free_nonneighbor
#print axioms Graph189AtomNonneighbor.repaired_minDegree
