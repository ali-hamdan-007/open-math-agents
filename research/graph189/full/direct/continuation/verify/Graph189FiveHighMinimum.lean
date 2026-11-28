import Graph189FiveTiedOriginal
import Graph189FiveLowComponent
import Graph189FiveLowExchange
import Graph189FiveLowInsertion

open SimpleGraph Finset Graph189ExteriorGap
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189FiveHighMinimum
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem low_traceable
    (cuts : ∀ U : Finset V, U.card<2 → (G.induce {v : V | v∉U}).Connected)
    (z : V) (low : 3 ≤ G.degree z) (high : ∀ w, w≠z → 5 ≤ G.degree w)
    (quota : ∀ w, (univ.filter (fun t => G.dist w t=2)).card ≤ 5) (order : Fintype.card V ≤ 19) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  obtain ⟨a,b,p,hp,longest⟩ := Graph189ThreeRegularMinimum.longest_path (G:=G) z
  have uniq (u v : V) (hu : G.degree u<5) (hv : G.degree v<5) : u=v := by
    have uz : u=z := by by_contra no; have := high u no; omega
    have vz : v=z := by by_contra no; have := high v no; omega
    exact uz.trans vz.symm
  have minD (w : V) : 3 ≤ G.degree w := by
    by_cases e : w=z
    · exact e ▸ low
    · exact (high w e).trans' (by decide)
  have raw {c d} (r : G.Walk c d) (hr : r.IsPath) (len : r.length=p.length)
      (w : V) (ne : w≠z) (absent : w∉r.support) : 3 ≤ (G.neighborFinset w \ r.support.toFinset).card := by
    have h := high w ne
    have half := (high_exterior_half r hr (fun q hq => len ▸ longest q hq) absent (quota w) h minD uniq).2
    omega
  have through {c d} (r : G.Walk c d) (hr : r.IsPath) (len : r.length=p.length) (inside : z∈r.support) :
      r.IsHamiltonian := by
    apply hr.isHamiltonian_of_mem
    intro w
    by_contra off
    have wz : w≠z := fun e => off (e ▸ inside)
    have mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length ≤ r.length :=
      fun q hq => len ▸ longest q hq
    rcases Graph189FiveLowComponent.classify r hr mx cuts z low high (raw r hr len) quota order wz off with four|solo
    · exact Graph189FiveLowExchange.no_four_through r hr mx z inside high
        (fun q hq same => raw q hq (same.trans len)) quota order four
    · exact solo.2.1 inside
  by_cases on : z∈p.support
  · exact ⟨a,b,p,through p hp rfl on⟩
  have charge := quota z
  have insertZ (all : G.neighborFinset z ⊆ p.support.toFinset) :
      ∃ c d, ∃ q : G.Walk c d, q.IsPath ∧ q.length=p.length ∧ z∈q.support :=
    Graph189FiveLowInsertion.isolated p hp longest on all (by omega)
  suffices h : ∃ c d, ∃ q : G.Walk c d, q.IsPath ∧ q.length=p.length ∧ z∈q.support by
    obtain ⟨c,d,q,hq,l,keep⟩ := h
    exact ⟨c,d,q,through q hq l keep⟩
  by_cases other : ∃ w, w≠z ∧ w∉p.support
  · obtain ⟨w,wz,off⟩ := other
    rcases Graph189FiveLowComponent.classify p hp longest cuts z low high (raw p hp rfl) quota order wz off with four|solo
    · exact Graph189FiveLowInsertion.tetrahedron p hp longest on high (raw p hp rfl) order four
    · exact insertZ solo.2.2
  · apply insertZ
    intro w hw
    apply List.mem_toFinset.mpr
    by_contra absent
    exact other ⟨w,((G.mem_neighborFinset _ _).mp hw).ne.symm,absent⟩

/-- The registered conjecture at second-smallest degree five and minimum
degree at least three. The minimum degree may be three, four or five. -/
theorem traceable (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (k5 : G.secondSmallestDegree=5) (three : 3 ≤ G.minDegree) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have localCap (v : V) : G.distEven v ≤ 1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  by_cases short : Fintype.card V ≤ 2*G.secondSmallestDegree+2
  · exact OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.theorem_C hc localCap short
  by_cases uncut : ∀ z : V, (G.induce {v : V | v≠z}).Connected
  · by_cases tie : G.minDegree=5
    · exact Graph189FiveTiedOriginal.traceable_tied_five hc cap tie k5
    obtain ⟨w,hw⟩ := Graph189QuadraticOrder.second_attained (G:=G)
    obtain ⟨z,least⟩ := G.exists_minimal_degree_vertex
    have mBound := G.minDegree_le_degree w
    have zlow : G.degree z<5 := by omega
    have cuts (U : Finset V) (small : U.card < 2) : (G.induce {v : V | v∉U}).Connected := by
      by_cases empty : U=∅
      · subst U
        rw [show {v : V | v∉(∅ : Finset V)}=Set.univ by ext; simp]
        exact hc.map G.induceUnivIso.symm.toHom G.induceUnivIso.symm.surjective
      obtain ⟨v,rfl⟩ := card_eq_one.mp (show U.card=1 by have := card_pos.mpr (nonempty_iff_ne_empty.mpr empty); omega)
      rw [show {t : V | t∉({v} : Finset V)}={t : V | t≠v} by ext; simp]
      exact uncut v
    have order : Fintype.card V ≤ 19 := by
      have o := Graph189QuadraticOrder.rooted hc z 5 (fun t => by simpa [k5,Nat.add_comm] using localCap t)
      omega
    have quota (v : V) : (univ.filter (fun t => G.dist v t=2)).card ≤ 5 := by
      let T := univ.filter (fun t => G.dist v t=2)
      have self : v∉T := by simp [T]
      have sub : insert v T ⊆ univ.filter (fun t => Even (G.dist v t)) := by
        intro t ht
        rcases mem_insert.mp ht with rfl|h
        · simp
        · exact mem_filter.mpr ⟨mem_univ _,by rw [(mem_filter.mp h).2]; decide⟩
      have bound := card_le_card sub
      rw [card_insert_of_notMem self] at bound
      change T.card+1 ≤ G.distEven v at bound
      have := localCap v
      change T.card ≤ 5
      omega
    apply low_traceable cuts z (by omega) _ quota order
    intro v ne
    have := degree_pair (G:=G) v z ne
    omega
  · push Not at uncut
    exact Graph189CutH1.cut_vertex_case G hc localCap (by omega) uncut

#print axioms traceable
end Graph189FiveHighMinimum
