import Graph189ProtectedExteriorDegree

open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {u v : V}

/-- At odd second-smallest degree 2d+1, if a high exterior vertex retains
only d neighbors outside the protected path, its high exterior neighbors
are mutually adjacent. The contact-debit inequality is tight at that vertex. -/
theorem adjacent_of_odd_equality (p : G.Walk u v) (hp : p.IsPath) (t : Fin p.support.length)
    (longest : ∀ {i j}, ∀ q : G.Walk i j, q.IsPath → p.support[t.val]∈q.support → q.length≤p.length)
    {a b c : V} (ha : a∉p.support) (hb : b∉p.support) (hc : c∉p.support)
    (ab : G.Adj a b) (ac : G.Adj a c) (diff : b≠c) {d : ℕ}
    (degreeA : 2*d+1 ≤ G.degree a) (degreeB : 2*d+1 ≤ G.degree b)
    (size : (G.neighborFinset a \ p.support.toFinset).card=d)
    (quota : (univ.filter (fun w => G.dist a w=2)).card≤2*d+1) : G.Adj b c := by
  classical
  let P := p.support.toFinset
  let A := G.neighborFinset a \ P
  let C := (G.neighborFinset b \ P) ∩ G.neighborFinset a
  have bound := protected_exterior_contact_degree p hp t longest ha hb ab quota
  change (G.neighborFinset a ∩ P).card + G.degree b ≤ 2*d+1+2+C.card at bound
  have parts := card_sdiff_add_card_inter (G.neighborFinset a) P
  rw [G.card_neighborFinset_eq_degree] at parts
  change A.card+(G.neighborFinset a ∩ P).card=G.degree a at parts
  change A.card=d at size
  have memB : b∈A := mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr ab,fun h => hb (List.mem_toFinset.mp h)⟩
  have memC : c∈A := mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr ac,fun h => hc (List.mem_toFinset.mp h)⟩
  have incl : C ⊆ A.erase b := by
    intro z hz
    obtain ⟨hzB,hzA⟩ := mem_inter.mp hz
    obtain ⟨bz,off⟩ := mem_sdiff.mp hzB
    exact mem_erase.mpr ⟨((G.mem_neighborFinset _ _).mp bz).ne.symm,mem_sdiff.mpr ⟨hzA,off⟩⟩
  have erased := card_erase_add_one memB
  have eq : C=A.erase b := eq_of_subset_of_card_le incl (by omega)
  have common : c∈C := eq ▸ mem_erase.mpr ⟨diff.symm,memC⟩
  exact (G.mem_neighborFinset _ _).mp (mem_sdiff.mp (mem_inter.mp common).1).1

#print axioms adjacent_of_odd_equality
end Graph189ExteriorGap
