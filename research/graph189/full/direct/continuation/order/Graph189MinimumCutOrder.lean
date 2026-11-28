import Graph189MinimumCut
import Graph189WedgeOrder
import Mathlib.Tactic.Linarith

namespace Graph189CutSides
open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The order and cross-product inputs for a minimum-cut comparison, with the
single possible low vertex in any position and the populations ordered. -/
theorem order_at_minimum_cut (hc : G.Connected)
    (cap : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree) (S : Finset V)
    (survives : ∃ u, u ∉ S) (disc : ¬(G.induce {u : V | u ∉ S}).Connected)
    (smaller : ∀ T : Finset V, T.card < S.card → (G.induce {u : V | u ∉ T}).Connected) :
    (∀ z ∈ S, G.secondSmallestDegree + 1 ≤ G.degree z + S.card) ∧
      ∃ X Y : ℕ, X ≤ Y ∧ Fintype.card V ≤ S.card + 1 + X + Y ∧
        X * Y ≤ X * G.secondSmallestDegree + S.card * (G.secondSmallestDegree * G.secondSmallestDegree) := by
  classical
  obtain ⟨A,B,sides⟩ := exists_cutSides_of_disconnected S survives disc
  refine ⟨fun _ hz => sides.anchor_degree smaller cap hz,?_⟩
  let k := G.secondSmallestDegree
  let X := A.filter (fun v => k ≤ G.degree v)
  let Y := B.filter (fun v => k ≤ G.degree v)
  let L := univ.filter (fun v => G.degree v < k)
  have few : L.card ≤ 1 := by
    apply card_le_one.mpr
    intro u hu v hv
    by_contra ne
    obtain h | h := degree_pair (G := G) u v ne
    · exact (not_lt_of_ge h) (mem_filter.mp hu).2
    · exact (not_lt_of_ge h) (mem_filter.mp hv).2
  have cover : univ ⊆ ((S ∪ X) ∪ Y) ∪ L := by
    intro v _
    by_cases hi : k ≤ G.degree v
    · rcases sides.cover v with h | h | h
      · exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨h,hi⟩)))
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨h,hi⟩))
      · exact mem_union_left _ (mem_union_left _ (mem_union_left _ h))
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,Nat.lt_of_not_ge hi⟩)
  have count := card_le_card cover
  rw [card_univ] at count
  have h1 := card_union_le S X
  have h2 := card_union_le (S ∪ X) Y
  have h3 := card_union_le ((S ∪ X) ∪ Y) L
  by_cases hxy : X.card ≤ Y.card
  · exact ⟨X.card,Y.card,hxy,by omega,sides.high_product hc smaller cap⟩
  · exact ⟨Y.card,X.card,by omega,by omega,sides.swap.high_product hc smaller cap⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- A deletion smaller than the graph's vertex connectivity is connected.
This applies to every minimum separator, including a prescribed one containing
the possible low vertex. -/
theorem connected_after_smaller_deletion (T : Finset V) (ht : T.card < G.vertexConnectivity) :
    (G.induce {u : V | u ∉ T}).Connected := by
  classical
  by_contra bad
  have hn := Fintype.one_lt_card (α := V)
  have bound : G.vertexConnectivity ≤ T.card := by
    unfold vertexConnectivity
    rw [if_neg (by omega : ¬ Fintype.card V ≤ 1)]
    exact Nat.sInf_le ⟨T,rfl,Or.inl bad⟩
  omega

/-- The graph's own vertex connectivity supplies the separator and its
minimality as soon as the complete-graph convention cannot apply. -/
theorem order_at_vertexConnectivity (hc : G.Connected)
    (cap : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree)
    (range : G.vertexConnectivity < Fintype.card V - 1) :
    ∃ S : Finset V, S.card = G.vertexConnectivity ∧
      (∀ z ∈ S, G.secondSmallestDegree + 1 ≤ G.degree z + G.vertexConnectivity) ∧
      ∃ X Y : ℕ, X ≤ Y ∧ Fintype.card V ≤ G.vertexConnectivity + 1 + X + Y ∧
        X * Y ≤ X * G.secondSmallestDegree +
          G.vertexConnectivity * (G.secondSmallestDegree * G.secondSmallestDegree) := by
  classical
  let M : Set ℕ := {j | ∃ S : Finset V, S.card = j ∧
    (¬(G.induce ((S : Set V)ᶜ)).Connected ∨ S.card = Fintype.card V - 1)}
  have hn := Fintype.one_lt_card (α := V)
  have eq : G.vertexConnectivity = sInf M := by
    unfold vertexConnectivity
    rw [if_neg (by omega : ¬ Fintype.card V ≤ 1)]
  let a : V := Classical.arbitrary V
  have hcard : (univ.erase a).card = Fintype.card V - 1 := by
    rw [card_erase_of_mem (mem_univ a),card_univ]
  have inhabited : M.Nonempty := ⟨_,univ.erase a,hcard,Or.inr hcard⟩
  have chosen : G.vertexConnectivity ∈ M := by
    rw [eq]
    exact Nat.sInf_mem inhabited
  obtain ⟨S,sz,hd | he⟩ := chosen
  · have smaller (T : Finset V) (ht : T.card < S.card) : (G.induce {u : V | u ∉ T}).Connected := by
      exact connected_after_smaller_deletion T (by omega)
    have survives : ∃ u, u ∉ S := by
      by_contra! full
      have hall : S = univ := Finset.eq_univ_iff_forall.mpr full
      rw [hall,card_univ] at sz
      omega
    have result := order_at_minimum_cut hc cap S survives hd smaller
    exact ⟨S,sz,by simpa only [sz] using result⟩
  · omega

#print axioms order_at_minimum_cut
#print axioms order_at_vertexConnectivity
namespace CutSides
variable {A B S : Finset V} (sides : CutSides G A B S)
include sides

/-- When the low vertex is on the cut, the actual side orders obey the product
estimate, and the entire order is counted without an exceptional vertex. -/
theorem low_cut_product (hc : G.Connected)
    (smaller : ∀ T : Finset V, T.card < S.card → (G.induce {u : V | u ∉ T}).Connected)
    (cap : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree)
    {z : V} (hz : z ∈ S) (low : G.degree z < G.secondSmallestDegree) :
    Fintype.card V = S.card + A.card + B.card ∧
    A.card * B.card ≤ A.card * G.secondSmallestDegree +
      S.card * (G.secondSmallestDegree * G.secondSmallestDegree) := by
  classical
  have high {u : V} (ne : u ≠ z) := (degree_pair (G := G) u z ne).resolve_right (not_le.mpr low)
  have af : A.filter (fun v => G.secondSmallestDegree ≤ G.degree v) = A := filter_eq_self.mpr
    fun _ ha => high (fun e => disjoint_left.mp sides.left_cut (e ▸ ha) hz)
  have bf : B.filter (fun v => G.secondSmallestDegree ≤ G.degree v) = B := filter_eq_self.mpr
    fun _ hb => high (fun e => disjoint_left.mp sides.right_cut (e ▸ hb) hz)
  have all : (S ∪ A) ∪ B = univ := eq_univ_iff_forall.mpr fun v => by
    rcases sides.cover v with h | h | h
    · exact mem_union_left _ (mem_union_right _ h)
    · exact mem_union_right _ h
    · exact mem_union_left _ (mem_union_left _ h)
  have d : Disjoint (S ∪ A) B := disjoint_union_left.mpr ⟨sides.right_cut.symm,sides.apart⟩
  have count := congrArg Finset.card all
  rw [card_union_of_disjoint d,card_union_of_disjoint sides.left_cut.symm,card_univ] at count
  exact ⟨count.symm,by simpa only [af,bf] using sides.high_product hc smaller cap⟩

/-- A low separator vertex has high neighbors on opposite sides with a
controlled common-neighbor count. These are the first two finite-order
constraints on its degree deficit. -/
theorem low_cut_deficit (hc : G.Connected)
    (smaller : ∀ T : Finset V, T.card < S.card → (G.induce {u : V | u ∉ T}).Connected)
    (cap : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree)
    {z : V} (hz : z ∈ S) (low : G.degree z < G.secondSmallestDegree) :
    ∃ a ∈ A, ∃ b ∈ B, G.Adj a z ∧ G.Adj b z ∧ ∃ r : ℕ,
      r = (G.neighborFinset a ∩ G.neighborFinset b).card ∧
      1 ≤ r ∧ r ≤ S.card ∧ G.secondSmallestDegree - G.degree z + 1 ≤ r ∧
      Fintype.card V + G.secondSmallestDegree * (G.secondSmallestDegree - G.degree z) ≤
        2 * G.secondSmallestDegree + (G.secondSmallestDegree+1)*r := by
  classical
  let k := G.secondSmallestDegree
  obtain ⟨⟨a,ha,az⟩,⟨b,hb,bz⟩⟩ := sides.contacts_of_minimum smaller hz
  let R := G.neighborFinset a ∩ G.neighborFinset b
  let U := G.neighborFinset a ∪ G.neighborFinset b
  let W := G.neighborFinset z ∪ U
  have ah : k ≤ G.degree a := (degree_pair (G := G) a z az.ne).resolve_right (not_le.mpr low)
  have bh : k ≤ G.degree b := (degree_pair (G := G) b z bz.ne).resolve_right (not_le.mpr low)
  have neq : a ≠ b := fun e => disjoint_left.mp sides.apart (e ▸ ha) hb
  have ne := sides.no_cross a ha b hb
  have cap' (v : V) : G.distEven v ≤ k+1 := by simpa only [k,Nat.add_comm 1] using cap v
  have common := Graph189HighPredecessor.common_lower neq ne az.symm bz.symm (cap' z)
  have rpos : 0 < R.card := card_pos.mpr ⟨z,mem_inter.mpr
    ⟨(G.mem_neighborFinset _ _).mpr az,(G.mem_neighborFinset _ _).mpr bz⟩⟩
  have rsub : R ⊆ S := by
    intro v hv
    obtain ⟨av,bv⟩ := mem_inter.mp hv
    rcases sides.cover v with h | h | hs
    · exact (sides.no_cross v h b hb ((G.mem_neighborFinset _ _).mp bv).symm).elim
    · exact (sides.no_cross a ha v h ((G.mem_neighborFinset _ _).mp av)).elim
    · exact hs
  change G.degree a + G.degree b + 1 ≤ G.degree z + k + R.card at common
  change G.degree z < k at low
  refine ⟨a,ha,b,hb,az,bz,R.card,rfl,rpos,card_le_card rsub,?_,?_⟩
  · change k - G.degree z + 1 ≤ R.card
    omega
  · have aabs : a ∉ U := by
      intro h
      rcases mem_union.mp h with h|h
      · exact (G.loopless.irrefl a) ((G.mem_neighborFinset _ _).mp h)
      · exact ne ((G.mem_neighborFinset _ _).mp h).symm
    have babs : b ∉ U := by simp [U,G.mem_neighborFinset,ne]
    have anot : a ∉ insert b U := by simp [neq,aabs]
    have included : insert a (insert b U) ⊆ W := by
      intro v hv
      rcases mem_insert.mp hv with rfl | hv
      · exact mem_union_left _ ((G.mem_neighborFinset _ _).mpr az.symm)
      rcases mem_insert.mp hv with rfl | hv
      · exact mem_union_left _ ((G.mem_neighborFinset _ _).mpr bz.symm)
      · exact mem_union_right _ hv
    have size := card_le_card included
    rw [card_insert_of_notMem anot,card_insert_of_notMem babs] at size
    have ui := card_union_add_card_inter (G.neighborFinset a) (G.neighborFinset b)
    rw [G.card_neighborFinset_eq_degree,G.card_neighborFinset_eq_degree] at ui
    change U.card + R.card = G.degree a + G.degree b at ui
    have wad := Nat.mul_le_mul_left (k+1)
      (show G.degree a + G.degree b + 2 ≤ W.card + R.card by omega)
    have ew := Graph189WedgeOrder.wedge_order hc az.symm bz.symm ne cap'
    change Fintype.card V + (k+1)*W.card ≤
      3*k+2 + k*(G.degree z+G.distEven z) + G.degree a + G.degree b at ew
    have eps := Nat.mul_le_mul_left k (cap' z)
    have deg := Nat.mul_le_mul_left k (show 2*k ≤ G.degree a+G.degree b by omega)
    have dif := congrArg (fun t : ℕ => k*t) (show G.degree z+(k-G.degree z)=k by omega)
    change Fintype.card V + k*(k-G.degree z) ≤ 2*k+(k+1)*R.card
    nlinarith only [ew,wad,eps,deg,dif]

end CutSides
#print axioms CutSides.low_cut_product
#print axioms CutSides.low_cut_deficit
end Graph189CutSides
