import Graph189SixWideRotation
import Graph189SixProtected
import Graph189HighMinimumGap
import Graph189QuadraticOrder

open SimpleGraph Finset
namespace Graph189SixThreeConnected
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At degree six, any actual path missing at most four vertices suffices
for traceability. This is the omission threshold in the separating-pair paper. -/
theorem traceable_of_four (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (six : G.secondSmallestDegree=6) (min : ∀ v, 3≤G.degree v)
    {u v : V} (r : G.Walk u v) (hr : r.IsPath) (near : Fintype.card V≤r.support.length+4) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    have bound := (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
    omega
  obtain ⟨z,sz⟩ := Graph189QuadraticOrder.second_attained (G:=G)
  have quad := Graph189QuadraticOrder.rooted hc z 6 (fun v => by simpa only [six] using point v)
  rw [sz,six] at quad
  have order : Fintype.card V≤25 := by omega
  obtain ⟨a,b,p,hp,mx⟩ := Graph189ThreeRegularMinimum.longest_path (G:=G) z
  let E := (p.support.toFinsetᶜ : Finset V)
  have pop := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at pop
  change p.support.length+E.card=Fintype.card V at pop
  have lr := mx r hr
  have pl := p.length_support
  have rl := r.length_support
  have close : E.card≤4 := by omega
  have quota (v : V) : (univ.filter (fun w => G.dist v w=2)).card≤6 := by
    let T := univ.filter (fun w => G.dist v w=2)
    have inc : insert v T⊆univ.filter (fun w => Even (G.dist v w)) := by
      intro w hw
      rcases mem_insert.mp hw with rfl|h
      · simp
      · exact mem_filter.mpr ⟨mem_univ _,by simp [(mem_filter.mp h).2]⟩
    have bound := card_le_card inc
    rw [card_insert_of_notMem (by simp [T])] at bound
    change T.card+1≤G.distEven v at bound
    change T.card≤6
    have := point v
    omega
  by_cases size : E.card=4
  · let D := E.filter (fun v => 6≤G.degree v)
    have sub : D⊆E := filter_subset _ _
    have many : 3≤D.card := by
      have one : (E\D).card≤1 := by
        apply card_le_one.mpr
        intro u hu v hv
        by_contra ne
        have pair := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) u v ne
        rcases pair with lo|lo
        · exact (mem_sdiff.mp hu).2 (mem_filter.mpr ⟨(mem_sdiff.mp hu).1,by omega⟩)
        · exact (mem_sdiff.mp hv).2 (mem_filter.mpr ⟨(mem_sdiff.mp hv).1,by omega⟩)
      have cnt := card_sdiff_add_card_eq_card sub
      omega
    have off (v : V) (hv : v∈E) : v∉p.support := by simpa [E] using hv
    have hi (v : V) (hv : v∈D) : 6≤G.degree v := (mem_filter.mp hv).2
    have all {u : V} (hu : u∈D) : (G.neighborFinset u\p.support.toFinset)=E.erase u := by
      have inc : (G.neighborFinset u\p.support.toFinset)⊆E.erase u := by
        intro w hw
        exact mem_erase.mpr ⟨((G.mem_neighborFinset _ _).mp (mem_sdiff.mp hw).1).ne.symm,
          mem_compl.mpr (mem_sdiff.mp hw).2⟩
      have d := (Graph189ExteriorGap.high_exterior_half p hp mx (off u (sub hu)) (quota u) (hi u hu)
        min (fun x y lx ly => by
          by_contra ne
          have pair := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) x y ne
          omega)).2
      apply eq_of_subset_of_card_le inc
      rw [card_erase_of_mem (sub hu),size]
      have := hi u hu
      omega
    have joined {u v : V} (hu : u∈D) (hv : v∈E) (ne : u≠v) : G.Adj u v := by
      have h : v∈G.neighborFinset u\p.support.toFinset := (all hu).symm ▸ mem_erase.mpr ⟨ne.symm,hv⟩
      exact (G.mem_neighborFinset _ _).mp (mem_sdiff.mp h).1
    have clique : G.IsClique (E : Set V) := by
      intro u hu v hv ne
      by_cases ud : u∈D
      · exact joined ud hv ne
      by_cases vd : v∈D
      · exact (joined vd hu ne.symm).symm
      have n := card_sdiff_add_card_eq_card sub
      have one : (E\D).card≤1 := by omega
      exact False.elim (ne (card_le_one.mp one u (mem_sdiff.mpr ⟨hu,ud⟩) v (mem_sdiff.mpr ⟨hv,vd⟩)))
    have bound (u : V) (_ : u∈D) (v : V) (_ : G.Adj u v) (no : v∉E) : v∈p.support := by simpa [E] using no
    have left := Graph189SixFullPorts.initial p hp mx E D size many sub off clique bound hi quota order
    have right := Graph189SixFullPorts.initial p.reverse hp.reverse (fun q hq => by simpa using mx q hq)
      E D size many sub (fun v hv => by simpa using off v hv) clique
      (fun u hu v e skip => by simpa using bound u hu v e skip) hi quota order
    have ab : a≠b := by
      intro e
      subst b
      have zero := (Walk.isPath_iff_nil.mp hp).length_eq_zero
      obtain ⟨u,hu,v,hv,ne⟩ := one_lt_card.mp (show 1<D.card by omega)
      have edge := joined hu (sub hv) ne
      have len := mx edge.toWalk edge.isPath_toWalk
      rw [edge.length_toWalk] at len
      omega
    have pair := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) a b ab
    exfalso
    omega
  by_contra fail
  by_cases short : Fintype.card V≤22
  · obtain ⟨w,lw,_,_,r,hr⟩ := Graph189ExteriorDegreeCycle.near_longest_has_hamiltonian_low_deletion
      p hp mx (by omega) fail (by omega) point min
    have high (x : V) (ne : x≠w) : G.secondSmallestDegree≤G.degree x :=
      (OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) x w ne).resolve_right (not_le.mpr lw)
    exact fail (Graph189SixProtected.traceable w (min w) six high point short r hr)
  have high (v : V) : G.secondSmallestDegree<2*G.degree v := by
    have q := Graph189QuadraticOrder.rooted hc v 6 (fun u => by simpa only [six] using point u)
    omega
  have gap := Graph189ExteriorDegreeCycle.high_min_longest_gap p hp mx fail (by omega) point high
  omega

/-- The original conclusion at second-smallest degree six and vertex
connectivity at least three, at every order. -/
theorem traceable (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (six : G.secondSmallestDegree=6) (conn : 3≤G.vertexConnectivity) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    have bound := (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
    omega
  have min (v : V) : 3≤G.degree v := conn.trans (Graph189CutSides.connectivity_le_degree (G:=G) v)
  obtain ⟨z,sz⟩ := Graph189QuadraticOrder.second_attained (G:=G)
  have quad := Graph189QuadraticOrder.rooted hc z 6 (fun v => by simpa only [six] using point v)
  rw [sz,six] at quad
  have order : Fintype.card V≤25 := by omega
  obtain ⟨a,b,p,hp,mx⟩ := Graph189ThreeRegularMinimum.longest_path (G:=G) z
  have quota (v : V) : (univ.filter (fun w => G.dist v w=2)).card≤6 := by
    let T := univ.filter (fun w => G.dist v w=2)
    have inc : insert v T⊆univ.filter (fun w => Even (G.dist v w)) := by
      intro w hw
      rcases mem_insert.mp hw with rfl|h
      · simp
      · exact mem_filter.mpr ⟨mem_univ _,by simp [(mem_filter.mp h).2]⟩
    have bound := card_le_card inc
    rw [card_insert_of_notMem (by simp [T])] at bound
    change T.card+1≤G.distEven v at bound
    change T.card≤6
    have := point v
    omega
  let E := p.support.toFinsetᶜ
  have low (v : V) (hv : v∈E) : G.degree v<6 := by
    by_contra! hi
    exact Graph189SixWideRotation.no_high p hp mx conn order six min quota (by simpa [E] using hv) hi
  have few : E.card≤1 := by
    apply card_le_one.mpr
    intro u hu v hv
    by_contra ne
    have pair := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) u v ne
    have l := low u hu
    have r := low v hv
    omega
  have pop := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at pop
  change p.support.length+E.card=Fintype.card V at pop
  exact traceable_of_four hc cap six min p hp (by omega)

#print axioms traceable_of_four
#print axioms traceable
end Graph189SixThreeConnected
