import Graph189FourTiedOriginal
import Graph189FourLowExterior
import Graph189FourLowTriangle
import Graph189FourProtected
import Graph189FourSingleNeighbor

open SimpleGraph Finset Graph189ExteriorGap
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189FourOriginal
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem three_deletion (z : V) (zdeg : G.degree z=3) (k4 : G.secondSmallestDegree=4)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) (order : Fintype.card V ≤ 14)
    {c d : {v : V | v≠z}} (P : (G.induce {v : V | v≠z}).Walk c d) (hP : P.IsHamiltonian) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  obtain ⟨a,b,p,hp,t,eq,longest⟩ := exists_longest_through G z
  refine ⟨a,b,p,hp.isHamiltonian_of_mem (fun x => ?_)⟩
  by_contra omitted
  let E := (p.support.toFinsetᶜ : Finset V)
  let X : E := ⟨x,by simpa [E] using omitted⟩
  have mx : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val]∈r.support → r.length ≤ p.length :=
    fun r hr h => longest r hr (eq ▸ h)
  have low : G.degree p.support[t.val] < G.secondSmallestDegree := by rw [eq,zdeg,k4]; decide
  have gap := protected_size_of_traceable_deletion z (by omega) P hP p hp longest
  rw [zdeg] at gap
  change 1+3+(3+1)*E.card ≤ Fintype.card V at gap
  have deg := protected_exterior_minimum p hp t mx low cap X
  rw [k4] at deg
  change 2 ≤ (G.induce (E : Set V)).degree X at deg
  have ub := (G.induce (E : Set V)).degree_lt_card_verts X
  change (G.induce (E : Set V)).degree X < Fintype.card E at ub
  rw [Fintype.card_coe] at ub
  omega

private theorem low_traceable (hc : G.Connected)
    (cuts : ∀ U : Finset V, U.card<2 → (G.induce {v : V | v∉U}).Connected)
    (k4 : G.secondSmallestDegree=4) (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (quota : ∀ v, (univ.filter (fun w => G.dist v w=2)).card ≤ 4)
    (z : V) (zdeg : G.degree z=2 ∨ G.degree z=3) (high : ∀ w, w≠z → 4 ≤ G.degree w) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have order : Fintype.card V ≤ 11+G.degree z := by
    have bound := Graph189QuadraticOrder.rooted hc z 4 (fun v => by simpa only [k4] using cap v)
    omega
  obtain ⟨a,b,p,hp,maximal⟩ := Graph189ThreeRegularMinimum.longest_path (G:=G) z
  have retain {c d} (r : G.Walk c d) (hr : r.IsPath) (same : r.length=p.length)
      (w : V) (wz : w≠z) (off : w∉r.support) : 2 ≤ (G.neighborFinset w \ r.support.toFinset).card := by
    have mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length ≤ r.length :=
      fun q hq => same ▸ maximal q hq
    rcases zdeg with two|three
    · exact Graph189FourSingleNeighbor.high_exterior_neighbors r hr mx z two high quota (by omega) wz off
    · have minimum (v : V) : 3 ≤ G.degree v := by
        by_cases e : v=z
        · rw [e,three]
        · exact (high v e).trans' (by decide)
      have uniqueLow (u v : V) (hu : G.degree u<4) (hv : G.degree v<4) : u=v := by
        have uz : u=z := by by_contra h; have := high u h; omega
        have vz : v=z := by by_contra h; have := high v h; omega
        exact uz.trans vz.symm
      have wh := high w wz
      have half := (high_exterior_half r hr mx off (quota w) wh minimum uniqueLow).2
      omega
  have every (w : V) (wz : w≠z) : w∈p.support := by
    by_contra off
    have size := Graph189FourLowExterior.three_omitted p hp maximal cuts z zdeg high (retain p hp rfl)
      quota order wz off
    exact Graph189FourLowTriangle.no_triangle p hp maximal z high retain quota (by omega) size
  by_cases present : z∈p.support
  · exact ⟨a,b,p,hp.isHamiltonian_of_mem (fun w => by
      by_cases wz : w=z
      · exact wz ▸ present
      · exact every w wz)⟩
  let S := {w : V | w≠z}
  have sub : ∀ w∈p.support, w∈S := fun w hw e => present (e ▸ hw)
  let q := p.induce S sub
  let f := (Embedding.induce (G:=G) S).toHom
  have mapped : q.map f=p := Walk.map_induce p sub
  have path : q.IsPath := (Walk.isPath_map_iff_of_injective (f:=f) Subtype.val_injective).mp
    (by rw [mapped]; exact hp)
  have hq : q.IsHamiltonian := path.isHamiltonian_of_mem (by
    intro w
    have belongs := every w.val w.property
    have supp : List.map Subtype.val q.support=p.support := by
      calc
        List.map Subtype.val q.support = (q.map f).support := (Walk.support_map f q).symm
        _ = p.support := congrArg (fun r : G.Walk a b => r.support) mapped
    rw [←supp] at belongs
    obtain ⟨t,ht,eq⟩ := List.mem_map.mp belongs
    exact (Subtype.ext eq : t=w) ▸ ht)
  rcases zdeg with two|three
  · exact Graph189FourProtected.traceable_of_two_deletion hc z two k4 cap q hq
  · exact three_deletion z three k4 cap (by omega) q hq

/-- The exact registered conjecture holds whenever the second entry of the
nondecreasing degree sequence equals four, including either possible low vertex. -/
theorem traceable_four (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (k4 : G.secondSmallestDegree=4) : ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have localCap (v : V) : G.distEven v ≤ 1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  by_cases short : Fintype.card V ≤ 2*G.secondSmallestDegree+2
  · exact OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.theorem_C hc localCap short
  by_cases uncut : ∀ z : V, (G.induce {v : V | v≠z}).Connected
  · by_cases tie : G.minDegree=4
    · exact Graph189FourTiedOriginal.traceable_tied_four hc cap tie k4
    have cuts (U : Finset V) (small : U.card < 2) : (G.induce {v : V | v∉U}).Connected := by
      by_cases empty : U=∅
      · subst U
        rw [show {v : V | v∉(∅ : Finset V)}=Set.univ by ext; simp]
        exact hc.map G.induceUnivIso.symm.toHom G.induceUnivIso.symm.surjective
      obtain ⟨v,rfl⟩ := card_eq_one.mp (show U.card=1 by have := card_pos.mpr (nonempty_iff_ne_empty.mpr empty); omega)
      rw [show {w : V | w∉({v} : Finset V)}={w : V | w≠v} by ext; simp]
      exact uncut v
    have minimum := Graph189CutBounds.two_le_degree hc localCap (by omega)
    obtain ⟨z,eq⟩ := G.exists_minimal_degree_vertex
    have least : G.minDegree ≤ G.secondSmallestDegree := by
      let ds := G.degreeSequence
      have len : 1 < ds.length := by simpa [ds,degreeSequence] using Fintype.one_lt_card (α := V)
      have mem : G.secondSmallestDegree ∈ ds := by
        change ds.getD 1 0 ∈ ds
        cases e : ds with
        | nil => simp [e] at len
        | cons a t =>
          cases f : t with
          | nil => simp [e,f] at len
          | cons b r => simp
      have hm : G.secondSmallestDegree ∈ univ.val.map (fun v : V => G.degree v) := by
        simpa [ds,degreeSequence] using mem
      obtain ⟨w,_,hw⟩ := Multiset.mem_map.mp hm
      exact hw ▸ G.minDegree_le_degree w
    have zlow := minimum z
    have zdeg : G.degree z=2 ∨ G.degree z=3 := by omega
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
    apply low_traceable hc cuts k4 (fun v => by simpa [Nat.add_comm] using localCap v) quota z zdeg
    intro w ne
    have pair := degree_pair (G:=G) w z ne
    omega
  · push Not at uncut
    exact Graph189CutH1.cut_vertex_case G hc localCap (by omega) uncut

end Graph189FourOriginal
#print axioms Graph189FourOriginal.traceable_four
