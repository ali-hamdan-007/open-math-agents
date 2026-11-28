import Graph189ExteriorHalf
import Graph189DoubleExteriorShift
import Graph189MidpointExchange
import Graph189ExteriorPopulation

namespace Graph189ExteriorDegreeCycle
open SimpleGraph Finset Graph189ExteriorGap
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

private theorem exact_quota {V : Type*} [Fintype V] {G : SimpleGraph V} (a : V) {k : ℕ} (cap : G.distEven a ≤ k+1) :
    (exactTwo G a).card ≤ k := by
  classical
  let T := exactTwo G a
  have missing : a ∉ T := by
    intro h
    have two : G.dist a a=2 := (mem_filter.mp h).2
    simp at two
  have cover : insert a T ⊆ univ.filter (fun z => Even (G.dist a z)) := by
    intro v hv
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    rcases mem_insert.mp hv with rfl|h
    · simp
    · rw [show G.dist a v=2 from (mem_filter.mp h).2]; decide
  have sz := card_le_card cover
  rw [card_insert_of_notMem missing] at sz
  change T.card+1 ≤ G.distEven a at sz
  change T.card ≤ k
  omega

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem no_high_off_almost_longest {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (longest : ∀ {x y}, ∀ r : G.Walk x y, r.IsPath → r.length ≤ p.length)
    (near : Fintype.card V ≤ p.support.length+3)
    (k5 : 5 ≤ G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (minimum : ∀ v, 3 ≤ G.degree v) {x : V} (hx : x ∉ p.support) :
    G.degree x < G.secondSmallestDegree := by
  classical
  by_contra! hi
  have uq (a b : V) (ha : G.degree a < G.secondSmallestDegree) (hb : G.degree b < G.secondSmallestDegree) :
      a=b := by
    by_contra h
    exact (degree_pair (G:=G) a b h).elim (fun h => by omega) (fun h => by omega)
  obtain ⟨_,half⟩ := high_exterior_half p hp longest hx (exact_quota x (cap x)) hi minimum uq
  let T := univ \ p.support.toFinset
  have sz : T.card + p.support.length = Fintype.card V := by
    have h := card_sdiff_add_card_inter (univ : Finset V) p.support.toFinset
    rwa [univ_inter,List.toFinset_card_of_nodup hp.support_nodup,card_univ] at h
  have xin : x ∈ T := mem_sdiff.mpr ⟨mem_univ _,fun h => hx (List.mem_toFinset.mp h)⟩
  have sub : G.neighborFinset x \ p.support.toFinset ⊆ T.erase x := by
    intro y hy
    obtain ⟨edge,off⟩ := mem_sdiff.mp hy
    exact mem_erase.mpr ⟨((G.mem_neighborFinset _ _).mp edge).ne.symm,mem_sdiff.mpr ⟨mem_univ _,off⟩⟩
  have bound := card_le_card sub
  have one := card_erase_add_one xin
  omega

/-- The only possible near-spanning longest path is a spanning path in the
deletion of the unique low vertex. This direction has no half-minimum premise. -/
theorem near_longest_has_hamiltonian_low_deletion {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (longest : ∀ {x y}, ∀ r : G.Walk x y, r.IsPath → r.length ≤ p.length)
    (near : Fintype.card V ≤ p.support.length+3)
    (notTrace : ¬ ∃ x y, ∃ q : G.Walk x y, q.IsHamiltonian)
    (k5 : 5 ≤ G.secondSmallestDegree) (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (minimum : ∀ v : V, 3 ≤ G.degree v) :
    ∃ z : V, G.degree z < G.secondSmallestDegree ∧
      ∃ x y, ∃ q : (G.induce {a : V | a ≠ z}).Walk x y, q.IsHamiltonian := by
  classical
  obtain ⟨a,ha⟩ : ∃ a, a ∉ p.support := by
    by_contra! covers
    exact notTrace ⟨u,v,p,hp.isHamiltonian_of_mem covers⟩
  have low := no_high_off_almost_longest p hp longest near k5 cap minimum ha
  let S := {z : V | z ≠ a}
  have sub : ∀ x ∈ p.support, x ∈ S := fun z hz eq => ha (eq ▸ hz)
  let q := p.induce S sub
  let f := (Embedding.induce (G:=G) S).toHom
  have mapped : q.map f = p := Walk.map_induce p sub
  have path : q.IsPath := (Walk.isPath_map_iff_of_injective (f:=f) Subtype.val_injective).mp
    (by rw [mapped]; exact hp)
  refine ⟨a,low,_,_,q,path.isHamiltonian_of_mem ?_⟩
  intro z
  have belongs : z.val ∈ p.support := by
    by_contra off
    have zlow := no_high_off_almost_longest p hp longest near k5 cap minimum off
    exact (degree_pair (G:=G) z.val a z.property).elim (fun h => by omega) (fun h => by omega)
  have supp : List.map Subtype.val q.support = p.support := by
    calc
      List.map Subtype.val q.support = (q.map f).support := (Walk.support_map f q).symm
      _ = p.support := congrArg (fun r : G.Walk u v => r.support) mapped
  rw [←supp] at belongs
  obtain ⟨t,ht,eq⟩ := List.mem_map.mp belongs
  exact (Subtype.ext eq : t = z) ▸ ht

/-- Midpoint exchange plus the ambient degree bound rules out every longest
path missing at most three vertices as soon as twice the minimum degree
exceeds the even-distance budget. -/
theorem high_min_longest_gap {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (longest : ∀ {x y}, ∀ r : G.Walk x y, r.IsPath → r.length ≤ p.length)
    (notTrace : ¬ ∃ x y, ∃ q : G.Walk x y, q.IsHamiltonian)
    (k5 : 5 ≤ G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (minimum : ∀ v, G.secondSmallestDegree < 2*G.degree v) :
    p.support.length+3 < Fintype.card V := by
  classical
  by_contra! near
  have three (v : V) : 3 ≤ G.degree v := by have := minimum v; omega
  obtain ⟨a,ha⟩ : ∃ a, a ∉ p.support := by
    by_contra! covers
    exact notTrace ⟨u,v,p,hp.isHamiltonian_of_mem covers⟩
  have low := no_high_off_almost_longest p hp longest near k5 cap three ha
  have solo (b : V) (hb : b ∉ p.support) : b=a := by
    by_contra h
    have bl := no_high_off_almost_longest p hp longest near k5 cap three hb
    exact (degree_pair (G:=G) b a h).elim (fun h => by omega) (fun h => by omega)
  have wide (i : ℕ) (hi : i ∈ contactPositions p a) (j : ℕ) (hj : j ∈ contactPositions p a)
      (ord : i<j) : i+3 ≤ j := by
    obtain ⟨ir,ic⟩ := (mem_contactPositions p a i).mp hi
    obtain ⟨jr,jc⟩ := (mem_contactPositions p a j).mp hj
    have spaced := omitted_contact_spacing p hp longest ha ⟨i,ir⟩ ⟨j,jr⟩ ord
      (by simpa [get_at] using ic) (by simpa [get_at] using jc)
    by_contra! bad
    have eq : j=i+2 := by change i+2 ≤ j at spaced; omega
    obtain ⟨b,c,q,hq,len,supp⟩ := swap_contact_midpoint p hp ha i (eq ▸ jr) ic (eq ▸ jc)
    have md : p.getVert (i+1) ≠ a := fun e => ha (e ▸ p.getVert_mem_support _)
    have off : p.getVert (i+1) ∉ q.support := by
      intro h
      have on := List.mem_toFinset.mpr h
      rw [supp] at on
      exact (mem_insert.mp on).elim md (fun j => (mem_erase.mp j).1 rfl)
    have longest' : ∀ {x y}, ∀ r : G.Walk x y, r.IsPath → r.length ≤ q.length := by
      intro x y r hr
      rw [len]
      exact longest r hr
    have near' : Fintype.card V ≤ q.support.length+3 := by
      rw [q.length_support,len,←p.length_support]
      exact near
    have midlow := no_high_off_almost_longest q hq longest' near' k5 cap three off
    have different : p.getVert (i+1) ≠ a := fun e => ha (e ▸ p.getVert_mem_support _)
    exact (degree_pair (G:=G) (p.getVert (i+1)) a different).elim (fun h => by omega) (fun h => by omega)
  have costs := double_positions_le_path_shell p hp longest ha wide
  rw [contact_card_neighbors p hp a] at costs
  have sub : G.neighborFinset a ⊆ p.support.toFinset := by
    intro b hb
    apply List.mem_toFinset.mpr
    by_contra absent
    exact ((G.mem_neighborFinset a b).mp hb).ne (solo b absent).symm
  rw [inter_eq_left.mpr sub,G.card_neighborFinset_eq_degree] at costs
  have bound : p.support.toFinset.filter (fun v => G.dist a v = 2) ⊆ exactTwo G a :=
    fun z hz => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hz).2⟩
  have quota := (card_le_card bound).trans (exact_quota a (cap a))
  have := minimum a
  omega

private theorem exists_longest_from_vertex {W : Type*} [Fintype W] {G : SimpleGraph W} (a : W) :
    ∃ x y, ∃ p : G.Walk x y, p.IsPath ∧
      ∀ {i j}, ∀ q : G.Walk i j, q.IsPath → q.length ≤ p.length := by
  classical
  let Good (m : ℕ) := ∃ x y, ∃ q : G.Walk x y, q.IsPath ∧ q.length=m
  have base : Good 0 := ⟨a,a,.nil,by simp,rfl⟩
  obtain ⟨x,y,p,hp,sz⟩ := Nat.findGreatest_spec (Nat.zero_le (Fintype.card W)) base
  have maximal {i j} (q : G.Walk i j) (hq : q.IsPath) : q.length ≤ p.length := by
    rw [sz]
    have len := q.length_support
    have bound := hq.support_nodup.length_le_card
    exact Nat.le_findGreatest (by omega) (show Good q.length from ⟨i,j,q,hq,rfl⟩)
  exact ⟨x,y,p,hp,maximal⟩

/-- The finite longest-path maximum transfers the gap to every walk that is a
path, as required by the arbitrary completion exterior. -/
theorem high_min_all_paths_gap
    (notTrace : ¬ ∃ x y, ∃ q : G.Walk x y, q.IsHamiltonian)
    (k5 : 5 ≤ G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (minimum : ∀ v, G.secondSmallestDegree < 2*G.degree v) :
    ∀ a b, ∀ r : G.Walk a b, r.IsPath → r.support.length+3 < Fintype.card V := by
  classical
  intro a b r hr
  obtain ⟨x,y,p,hp,maximal⟩ := exists_longest_from_vertex (G:=G) a
  have upper := high_min_longest_gap p hp maximal notTrace k5 cap minimum
  have le := maximal r hr
  have l1 := r.length_support
  have l2 := p.length_support
  omega

/-- Without any half-minimum assumption, a large path forces a Hamiltonian
path in the deletion of the unique low vertex. -/
theorem gap_of_no_hamiltonian_low_deletion
    (notTrace : ¬ ∃ x y, ∃ q : G.Walk x y, q.IsHamiltonian)
    (k5 : 5 ≤ G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (minimum : ∀ v, 3 ≤ G.degree v)
    (noLow : ∀ z : V, G.degree z < G.secondSmallestDegree →
      ¬ ∃ x y, ∃ q : (G.induce {a : V | a ≠ z}).Walk x y, q.IsHamiltonian) :
    ∀ a b, ∀ r : G.Walk a b, r.IsPath → r.support.length+3 < Fintype.card V := by
  classical
  intro a b r hr
  obtain ⟨x,y,p,hp,maximal⟩ := exists_longest_from_vertex (G:=G) a
  by_contra! near
  have le := maximal r hr
  have l1 := r.length_support
  have l2 := p.length_support
  obtain ⟨z,hz,path⟩ := near_longest_has_hamiltonian_low_deletion p hp maximal (by omega)
    notTrace k5 cap minimum
  exact noLow z hz path

#print axioms gap_of_no_hamiltonian_low_deletion
#print axioms near_longest_has_hamiltonian_low_deletion
#print axioms high_min_all_paths_gap
#print axioms high_min_longest_gap
end Graph189ExteriorDegreeCycle
