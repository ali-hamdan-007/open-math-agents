import Graph189RootedColumns
import Graph189MatchedOrder
import Graph189ExteriorPopulation

namespace Graph189RootedSplice
open SimpleGraph Finset Graph189ExteriorGap Graph189ExteriorDegreeCycle
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}

private theorem rooted_contact_degree_raw (p : G.Walk x y) (hp : p.IsPath)
    {root : V} (on : root∈p.support)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → root∈r.support → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k) :
    (G.neighborFinset a ∩ p.support.toFinset).card + G.degree b ≤
      k+2+((G.neighborFinset b \ p.support.toFinset) ∩ G.neighborFinset a).card := by
  classical
  let P := p.support.toFinset
  let A := G.neighborFinset a
  let B := G.neighborFinset b
  let D := B \ P
  let C := D ∩ A
  let X := (D.erase a) \ A
  let Q := P.filter (fun z => G.dist a z=2)
  have acol := rooted_cross_positions p hp on longest ha hb ab
  rw [contact_card_neighbors p hp a,contact_card_neighbors p hp b] at acol
  change (A∩P).card+(B∩P).card ≤ Q.card+1 at acol
  have ain : a∈D := Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr ab.symm,
    fun h => ha (List.mem_toFinset.mp h)⟩
  have inter : (D.erase a) ∩ A = C := by
    ext z
    simp only [C,Finset.mem_inter,Finset.mem_erase]
    constructor
    · rintro ⟨⟨_,hd⟩,hA⟩
      exact ⟨hd,hA⟩
    · rintro ⟨hd,hA⟩
      exact ⟨⟨fun eq => G.irrefl (eq ▸ (G.mem_neighborFinset a z).mp hA),hd⟩,hA⟩
  have part₁ := Finset.card_sdiff_add_card_inter B P
  have part₂ := Finset.card_erase_add_one ain
  have part₃ := Finset.card_sdiff_add_card_inter (D.erase a) A
  rw [inter] at part₃
  change X.card+C.card=(D.erase a).card at part₃
  have shell (z : V) (hz : z∈X) : G.dist a z=2 := by
    obtain ⟨hD,hA⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨ne,hd⟩ := Finset.mem_erase.mp hD
    have hzB := (Finset.mem_sdiff.mp hd).1
    exact two_step_metric ne.symm (fun hadj => hA ((G.mem_neighborFinset a z).mpr hadj)) ab
      ((G.mem_neighborFinset b z).mp hzB).symm
  have dis : Disjoint Q X := Finset.disjoint_left.mpr (by
    intro z hQ hX
    have dm := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hX).1).2
    exact (Finset.mem_sdiff.mp dm).2 (Finset.mem_filter.mp hQ).1)
  have incl : Q ∪ X ⊆ Finset.univ.filter (fun z => G.dist a z=2) := by
    intro z hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    rcases Finset.mem_union.mp hz with h | h
    · exact (Finset.mem_filter.mp h).2
    · exact shell z h
  have total := (Finset.card_le_card incl).trans quota
  rw [Finset.card_union_of_disjoint dis] at total
  change D.card+(B∩P).card=B.card at part₁
  change (A∩P).card+B.card ≤ k+2+C.card
  omega

/-- The path-contact degree and the adjacent vertex degree fit in the sum of the
metric capacity and the first vertex's off-path degree, with no high-degree assumption. -/
theorem rooted_contact_degree (p : G.Walk x y) (hp : p.IsPath)
    {root : V} (on : root∈p.support)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → root∈r.support → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k) :
    (G.neighborFinset a ∩ p.support.toFinset).card + G.degree b ≤
      k+1+(G.neighborFinset a \ p.support.toFinset).card := by
  classical
  let P := p.support.toFinset
  let A := G.neighborFinset a
  let B := G.neighborFinset b
  let C := (B \ P) ∩ A
  have bound := rooted_contact_degree_raw p hp on longest ha hb ab quota
  change (A∩P).card+G.degree b ≤ k+2+C.card at bound
  have absent : b∉C := by
    intro h
    have nb := (Finset.mem_sdiff.mp (Finset.mem_inter.mp h).1).1
    exact G.irrefl ((G.mem_neighborFinset _ _).mp nb)
  have share : insert b C ⊆ A \ P := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | h
    · exact Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr ab,
        fun h => hb (List.mem_toFinset.mp h)⟩
    · obtain ⟨hD,hA⟩ := Finset.mem_inter.mp h
      exact Finset.mem_sdiff.mpr ⟨hA,(Finset.mem_sdiff.mp hD).2⟩
  have count := Finset.card_le_card share
  rw [Finset.card_insert_of_notMem absent] at count
  change (A∩P).card+G.degree b ≤ k+1+(A \ P).card
  omega

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


/-- Every omitted vertex on a longest path containing the least-degree vertex has
at least floor(k/2) actual neighbors outside that path. -/
theorem rooted_half_exterior [Nontrivial V] (root : V) (least : G.degree root=G.minDegree)
    (p : G.Walk x y) (hp : p.IsPath) (on : root∈p.support)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → root∈r.support → r.length ≤ p.length)
    {a : V} (off : a∉p.support) (positive : 1≤G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) :
    G.secondSmallestDegree/2 ≤ (G.neighborFinset a \ p.support.toFinset).card := by
  classical
  let k := G.secondSmallestDegree
  have high (b : V) (hb : b ∉ p.support) : k ≤ G.degree b := by
    have different : b≠root := fun h => hb (h ▸ on)
    rcases degree_pair (G:=G) b root different with h|h
    · exact h
    · rw [least] at h
      exact h.trans (G.minDegree_le_degree b)
  have quota : (exactTwo G a).card≤k := exact_quota a (cap a)
  have neighbors := Finset.card_sdiff_add_card_inter (G.neighborFinset a) p.support.toFinset
  rw [G.card_neighborFinset_eq_degree] at neighbors
  have ha := high a off
  have existsEdge : ∃ b, G.Adj a b ∧ b∉p.support := by
    by_contra! allOn
    have inside : G.neighborFinset a ⊆ p.support.toFinset := fun b hb =>
      List.mem_toFinset.mpr (allOn b ((G.mem_neighborFinset _ _).mp hb))
    have counts := contact_card_neighbors p hp a
    rw [Finset.inter_eq_left.mpr inside,G.card_neighborFinset_eq_degree] at counts
    have pos : (contactPositions p a).Nonempty := Finset.card_pos.mp (by rw [counts]; omega)
    have charge := rooted_single_shift p hp on longest off pos
    have sub : p.support.toFinset.filter (fun v => G.dist a v=2) ⊆ exactTwo G a :=
      fun z hz => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hz).2⟩
    rw [counts] at charge
    have := (Finset.card_le_card sub).trans quota
    omega
  obtain ⟨b,ab,out⟩ := existsEdge
  have bound := rooted_contact_degree p hp on longest off out ab (k:=k) quota
  have hb := high b out
  change k/2 ≤ _
  omega

/-- Every path containing the least-degree vertex omits at least floor(k/2)+1
vertices in a nontraceable qualifying graph. -/
theorem rooted_omission [Nontrivial V] (root : V) (least : G.degree root = G.minDegree)
    (notTrace : ¬ ∃ a b, ∃ q : G.Walk a b, q.IsHamiltonian)
    (positive : 1 ≤ G.secondSmallestDegree) (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (p : G.Walk x y) (hp : p.IsPath) (on : root∈p.support) :
    p.support.length+G.secondSmallestDegree/2+1 ≤ Fintype.card V := by
  classical
  let Good (m : ℕ) := ∃ a b, ∃ q : G.Walk a b, q.IsPath ∧ root∈q.support ∧ q.length=m
  have base : Good 0 := ⟨root,root,.nil,by simp,by simp,rfl⟩
  obtain ⟨u,v,q,hq,kept,len⟩ := Nat.findGreatest_spec (Nat.zero_le (Fintype.card V)) base
  have longest {u v} (r : G.Walk u v) (hr : r.IsPath) (inside : root∈r.support) : r.length≤q.length := by
    rw [len]
    have h := r.length_support
    have bound := hr.support_nodup.length_le_card
    exact Nat.le_findGreatest (by omega) (show Good r.length from ⟨u,v,r,hr,inside,rfl⟩)
  obtain ⟨a,ha⟩ : ∃ a, a∉q.support := by
    by_contra! allIn
    exact notTrace ⟨u,v,q,hq.isHamiltonian_of_mem allIn⟩
  have half := rooted_half_exterior root least q hq kept longest ha positive cap
  let W := G.neighborFinset a \ q.support.toFinset
  have no : a∉W := fun h => G.irrefl ((G.mem_neighborFinset _ _).mp (mem_sdiff.mp h).1)
  have new := card_outside_add_path q hq (insert a W) (by
    intro v hv
    rcases mem_insert.mp hv with rfl|h
    · exact ha
    · exact fun hv => (mem_sdiff.mp h).2 (List.mem_toFinset.mpr hv))
  rw [card_insert_of_notMem no] at new
  change G.secondSmallestDegree/2 ≤ W.card at half
  have max := longest p hp on
  have qlen := q.length_support
  have plen := p.length_support
  omega

#print axioms rooted_half_exterior
#print axioms rooted_omission
end Graph189RootedSplice
