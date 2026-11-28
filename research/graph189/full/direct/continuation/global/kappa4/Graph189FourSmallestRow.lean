import Graph189FullLabelExit
import Graph189PositiveEvenCut
import Graph189TwoRootRecut

open Finset SimpleGraph Graph189CutSides Graph189PositiveEvenCut
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

namespace Graph189FourSmallestRow

/-- The row check is a closed Boolean comparison. Its soundness uses exact
natural arithmetic, independently of the SMT solver. -/
def check (k y : ℕ) : Bool := decide (7*k < 2*y+2)

theorem checked_18_70 : check 18 70 = true := by decide

private theorem check_mono {k x y : ℕ} (ok : check k x = true) (h : x≤y) :
    check k y = true := by
  have bound : 7*k<2*x+2 := of_decide_eq_true ok
  unfold check
  exact decide_eq_true_eq.mpr (by omega)

private theorem arithmetic {k y p q r m : ℕ} (accepted : check k y = true)
    (missing : 1 ≤ m) (partition : p+q+r = y) (ports : p ≤ k)
    (avoid : q+m ≤ k) (incidences : q+2*r+m ≤ 4*k) : False := by
  have h : 7*k < 2*y+2 := of_decide_eq_true accepted
  omega

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B S : Finset V}

private theorem two_witness {v w : V} (hit : G.dist v w = 2) :
    w ∈ evenOthers G v := by
  have ne : w ≠ v := by rintro rfl; simp at hit
  exact mem_even_others ne (by rw [hit]; decide)

private theorem nearest_label (hc : G.Connected) (cut : CutSides G A B S)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) (anchors : ∀ i∈S,
      G.secondSmallestDegree ≤ G.degree i)
    (smaller : ∀ T : Finset V,T.card<S.card → (G.induce {v : V | v∉T}).Connected)
    {X : Finset V} (inside : X ⊆ A) (degreeX : ∀ v∈X,G.secondSmallestDegree ≤ G.degree v)
    (size : X.card+S.card=G.secondSmallestDegree)
    {z i v : V} (za : z∈A) (zx : z∉X) (is : i∈S) (zi : G.Adj z i)
    (vb : v∈B) (high : G.secondSmallestDegree ≤ G.degree v)
    (nonport : ∀ j∈S, ¬G.Adj v j) : ∃ j∈S,G.dist j v=2 := by
  classical
  by_contra! none
  have far {j : V} (js : j∈S) : 3≤G.dist v j := by
    have ne : v≠j := fun e => disjoint_left.mp cut.right_cut vb (e ▸ js)
    have more := (hc v j).one_lt_dist_of_ne_of_not_adj ne (nonport j js)
    have notTwo : G.dist v j≠2 := by rw [dist_comm]; exact none j js
    omega
  have opposite {w : V} (wa : w∈A) : 4≤G.dist v w := by
    obtain ⟨j,js,dist⟩ := separator_distance hc cut.swap vb wa
    have ne : j≠w := fun e => disjoint_left.mp cut.left_cut (e ▸ wa) js
    have nonzero : G.dist j w≠0 := fun h => ne (hc.dist_eq_zero_iff.mp h)
    have more := far js
    omega
  have fourX (w : V) (wx : w∈X) : G.dist v w=4 := by
    have hi := high_distance_four hc (fun u => by simpa [Nat.add_comm] using cap u)
      high (degreeX w wx)
    have lo := opposite (inside wx)
    omega
  have nearS {j : V} (js : j∈S) : G.dist v j=3 := by
    have hi := high_distance_four hc (fun u => by simpa [Nat.add_comm] using cap u)
      high (anchors j js)
    have lo := far js
    by_contra ne
    have four : G.dist v j=4 := by omega
    have off : j∉X := fun jx => disjoint_left.mp cut.left_cut (inside jx) js
    have bound := four_layer_quota hc smaller (by omega : S.card≤G.secondSmallestDegree)
      (cap v) (insert j X) (by
        intro w hw
        rcases mem_insert.mp hw with rfl | wx
        · exact four
        · exact fourX w wx)
    rw [card_insert_of_notMem off] at bound
    omega
  have zFour : G.dist v z=4 := by
    have lo := opposite za
    have hi := hc.dist_triangle (u:=v) (v:=i) (w:=z)
    rw [nearS is,dist_eq_one_iff_adj.mpr zi.symm] at hi
    omega
  have bound := four_layer_quota hc smaller (by omega : S.card≤G.secondSmallestDegree)
    (cap v) (insert z X) (by
      intro w hw
      rcases mem_insert.mp hw with rfl | wx
      · exact zFour
      · exact fourX w wx)
  rw [card_insert_of_notMem zx] at bound
  omega

private theorem incidence_bound (cut : CutSides G A B S)
    (cap : ∀ v,G.distEven v≤G.secondSmallestDegree+1) (four : S.card=4)
    {z : V} (za : z∈A) (D Q R M : Finset V) (db : D⊆B) (ms : M⊆S)
    (qr : Q∪R=D) (dis : Disjoint Q R) (zm : ∀ i∈M,G.dist i z=2)
    (one : ∀ v∈Q,1≤(S.filter fun i => G.dist i v=2).card)
    (two : ∀ v∈R,2≤(S.filter fun i => G.dist i v=2).card) :
    Q.card+2*R.card+M.card≤4*G.secondSmallestDegree := by
  classical
  let k := G.secondSmallestDegree
  let count (v : V) := (S.filter fun i => G.dist i v=2).card
  have payQ : Q.card ≤ ∑ v ∈ Q, count v := by
    simpa [sum_const,nsmul_eq_mul] using (Finset.sum_le_sum one)
  have payR : 2*R.card ≤ ∑ v ∈ R, count v := by
    simpa [sum_const,nsmul_eq_mul,Nat.mul_comm] using (Finset.sum_le_sum two)
  have summed : Q.card+2*R.card≤∑ v ∈ D,count v := by
    rw [←qr,sum_union dis]
    omega
  have swap : (∑ v ∈ D, count v) = ∑ i ∈ S, (D.filter fun v => G.dist i v=2).card := by
    simp only [count,card_eq_sum_ones,Finset.sum_filter]
    exact Finset.sum_comm
  rw [swap] at summed
  have rows (i : V) (_ : i∈S) :
      (D.filter fun v => G.dist i v=2).card+(if i∈M then 1 else 0)≤k := by
    let row := D.filter fun v => G.dist i v=2
    have sub : row⊆evenOthers G i := fun v hv => two_witness (mem_filter.mp hv).2
    by_cases h : i∈M
    · have off : z∉row := fun hr => disjoint_left.mp cut.apart za (db (mem_filter.mp hr).1)
      have incl : insert z row⊆evenOthers G i := by
        intro v hv
        rcases mem_insert.mp hv with rfl | vrow
        · exact two_witness (zm i h)
        · exact sub vrow
      have bound := (card_le_card incl).trans (even_others_card (cap i))
      rw [card_insert_of_notMem off] at bound
      simpa [row,h] using bound
    · simpa [row,h] using ((card_le_card sub).trans (even_others_card (cap i)))
  have missing : (∑ i ∈ S, if i∈M then 1 else 0) = M.card := by
    rw [←Finset.sum_filter]
    have eq : S.filter (fun i => i∈M)=M := by
      ext i
      exact ⟨fun h => (mem_filter.mp h).2,fun hi => mem_filter.mpr ⟨ms hi,hi⟩⟩
    rw [eq,card_eq_sum_ones]
  have budget := Finset.sum_le_sum rows
  rw [Finset.sum_add_distrib,missing] at budget
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,four] at budget
  omega

/-- The exact smallest-population row gives a private port with enough
opposite contacts, via a reflected arithmetic check and original distances. -/
theorem eligible (hc : G.Connected) (cut : CutSides G A B S)
    (cap : ∀ v,G.distEven v≤G.secondSmallestDegree+1) (four : S.card=4)
    (anchors : ∀ i∈S,G.secondSmallestDegree≤G.degree i)
    (smaller : ∀ T : Finset V,T.card<S.card → (G.induce {v : V | v∉T}).Connected)
    (positive : (A.filter fun a => G.secondSmallestDegree≤G.degree a).Nonempty)
    (tight : (A.filter fun a => G.secondSmallestDegree≤G.degree a).card+S.card=G.secondSmallestDegree)
    (accept : check G.secondSmallestDegree B.card = true) :
    ∃ i ∈ S, ∃ b ∈ B, G.secondSmallestDegree≤G.degree b ∧ S.filter (G.Adj b)={i} ∧
      G.secondSmallestDegree+1≤S.card+(A∩G.neighborFinset i).card := by
  classical
  let k := G.secondSmallestDegree
  let X := A.filter fun a => k≤G.degree a
  change X.card+S.card=k at tight
  obtain ⟨a,ax⟩ := positive
  obtain ⟨aa,ah⟩ := mem_filter.mp ax
  have closed := Graph189FullLabelExit.closed_size cut aa
  obtain ⟨z,za,low⟩ : ∃ z∈A, ¬k≤G.degree z := by
    by_contra! noLow
    have all : X=A := by
      ext w
      exact ⟨fun h => (mem_filter.mp h).1,fun wa => mem_filter.mpr ⟨wa,noLow w wa⟩⟩
    rw [all] at tight
    omega
  have high {w : V} (ne : w≠z) : k≤G.degree w :=
    (degree_pair (G := G) w z ne).resolve_right low
  have xsub : X⊆A := filter_subset _ _
  have exactA : insert z X=A := by
    ext w
    constructor
    · intro h
      rcases mem_insert.mp h with rfl | wx
      · exact za
      · exact xsub wx
    · intro wa
      by_cases e : w=z
      · exact mem_insert.mpr (Or.inl e)
      · exact mem_insert_of_mem (mem_filter.mpr ⟨wa,high e⟩)
  have zx : z∉X := fun h => low (mem_filter.mp h).2
  have sizeA := congrArg card exactA
  rw [card_insert_of_notMem zx] at sizeA
  have size : A.card+S.card=k+1 := by omega
  have fullA {w : V} (wa : w∈A) (hw : k≤G.degree w) (i : V) (is : i∈S) :
      G.Adj w i :=
    Graph189FullLabelExit.tight_full cut size wa hw i (mem_union_right _ is)
      (fun eq => disjoint_left.mp cut.left_cut wa (eq ▸ is))
  have az : G.Adj a z :=
    Graph189FullLabelExit.tight_full cut size aa ah z (mem_union_left _ za) (fun eq => low (eq ▸ ah))
  obtain ⟨i,is,zi⟩ : ∃ i∈S,G.Adj z i := by
    by_contra! none
    have bound := Graph189PrivatePredecessor.nonport_full_neighbor hc cut cap aa za az.symm (fullA aa ah) none
    have big : 7*k<2*B.card+2 := of_decide_eq_true accept
    omega
  have near {v : V} (vb : v∈B) (np : ∀ j∈S, ¬G.Adj v j) : ∃ j∈S,G.dist j v=2 :=
    nearest_label hc cut cap anchors smaller xsub (fun w wx => (mem_filter.mp wx).2)
      tight za zx is zi vb (high (fun eq => disjoint_left.mp cut.apart za (eq ▸ vb))) np
  let P := B.filter fun v => ∃ j∈S,G.Adj v j
  let D := B \ P
  let Q := D.filter fun v => ¬∃ j∈S,G.Adj z j ∧ G.dist j v=2
  let R := D \ Q
  let M := S.filter fun j => ¬G.Adj z j
  have bPort : P.card≤k := by
    have sub : P⊆evenOthers G a := by
      intro v vp
      obtain ⟨vb,j,js,vj⟩ := mem_filter.mp vp
      exact two_witness (Graph189PortDifference.cross_two hc cut aa vb (fullA aa ah j js) vj.symm)
    exact (card_le_card sub).trans (even_others_card (cap a))
  have zUpper {j : V} (js : j∈S) : G.dist z j≤2 := by
    have h := hc.dist_triangle (u:=z) (v:=a) (w:=j)
    rw [dist_eq_one_iff_adj.mpr az.symm,dist_eq_one_iff_adj.mpr (fullA aa ah j js)] at h
    omega
  have zMiss {j : V} (jm : j∈M) : G.dist z j=2 := by
    obtain ⟨js,zj⟩ := mem_filter.mp jm
    have ne : z≠j := fun eq => disjoint_left.mp cut.left_cut (eq ▸ za) js
    have lo := (hc z j).one_lt_dist_of_ne_of_not_adj ne zj
    have hi := zUpper js
    omega
  have mPos : 1≤M.card := by
    by_contra! empty
    have all (j : V) (js : j∈S) : G.Adj z j := by
      by_contra miss
      have positive := card_pos.mpr (show M.Nonempty from ⟨j,mem_filter.mpr ⟨js,miss⟩⟩)
      omega
    have sub : X∪S⊆G.neighborFinset z := by
      intro w hw
      apply (G.mem_neighborFinset z w).mpr
      rcases mem_union.mp hw with wx | ws
      · obtain ⟨wa,wh⟩ := mem_filter.mp wx
        exact (Graph189FullLabelExit.tight_full cut size wa wh z (mem_union_left _ za)
          (fun eq => low (eq ▸ wh))).symm
      · exact all w ws
    have h := card_le_card sub
    rw [card_union_of_disjoint (cut.left_cut.mono_left xsub),G.card_neighborFinset_eq_degree] at h
    omega
  have missPort {v : V} (vd : v∈D) : ∀ j∈S, ¬G.Adj v j := by
    intro j js vj
    exact (mem_sdiff.mp vd).2 (mem_filter.mpr ⟨(mem_sdiff.mp vd).1,j,js,vj⟩)
  have dsub : D⊆B := sdiff_subset
  have qsub : Q⊆D := filter_subset _ _
  have qFour {v : V} (vq : v∈Q) : G.dist z v=4 := by
    obtain ⟨vd,avoid⟩ := mem_filter.mp vq
    obtain ⟨j,js,dist⟩ := separator_distance hc cut za (dsub vd)
    have ne : j≠v := fun eq => disjoint_left.mp cut.right_cut (dsub vd) (eq ▸ js)
    have lower := (hc j v).one_lt_dist_of_ne_of_not_adj ne (fun h => missPort vd j js h.symm)
    have lo : 4≤G.dist z v := by
      by_cases zj : G.Adj z j
      · have nz : G.dist j v≠2 := fun e => avoid ⟨j,js,zj,e⟩
        rw [dist_eq_one_iff_adj.mpr zj] at dist
        omega
      · rw [zMiss (mem_filter.mpr ⟨js,zj⟩)] at dist
        omega
    obtain ⟨h,hs,hv⟩ := near (dsub vd) (missPort vd)
    have hi := hc.dist_triangle (u:=z) (v:=h) (w:=v)
    have zu := zUpper hs
    omega
  have qBudget : Q.card+M.card≤k := by
    have dis : Disjoint Q M := (cut.right_cut.mono_left (qsub.trans dsub)).mono_right (filter_subset _ _)
    have sub : Q∪M⊆evenOthers G z := by
      intro v hv
      rcases mem_union.mp hv with vq | vm
      · have h := qFour vq
        exact mem_even_others (by rintro rfl; simp at h) (by rw [h]; decide)
      · exact two_witness (zMiss vm)
    have b := (card_le_card sub).trans (even_others_card (cap z))
    rw [card_union_of_disjoint dis] at b
    exact b
  by_contra absent
  have one (v : V) (vq : v∈Q) : 1≤(S.filter fun j => G.dist j v=2).card := by
    obtain ⟨j,js,jv⟩ := near (dsub (qsub vq)) (missPort (qsub vq))
    exact card_pos.mpr ⟨j,mem_filter.mpr ⟨js,jv⟩⟩
  have two (v : V) (vr : v∈R) : 2≤(S.filter fun j => G.dist j v=2).card := by
    obtain ⟨vd,off⟩ := mem_sdiff.mp vr
    have meet : ∃ j∈S,G.Adj z j ∧ G.dist j v=2 := by
      by_contra miss
      exact off (mem_filter.mpr ⟨vd,miss⟩)
    obtain ⟨j,js,zj,jv⟩ := meet
    by_contra! little
    have sole (u : V) (us : u∈S) (uv : G.dist u v=2) : u=j :=
      card_le_one_iff.mp (show (S.filter fun i => G.dist i v=2).card≤1 by omega)
        (mem_filter.mpr ⟨us,uv⟩) (mem_filter.mpr ⟨js,jv⟩)
    obtain ⟨b,bb,bh,_,jb,only⟩ := Graph189PrivatePredecessor.high_private hc cut cap
      js (dsub vd) jv (missPort vd) sole
    have support : S.filter (G.Adj b)={j} := by
      ext u
      constructor
      · intro bu
        obtain ⟨us,edge⟩ := mem_filter.mp bu
        exact mem_singleton.mpr (only u us edge.symm)
      · intro hu
        obtain rfl := mem_singleton.mp hu
        exact mem_filter.mpr ⟨js,jb.symm⟩
    have contact : A∩G.neighborFinset j=A := by
      apply inter_eq_left.mpr
      intro w wa
      apply (G.mem_neighborFinset j w).mpr
      by_cases eq : w=z
      · exact eq ▸ zj.symm
      · exact (fullA wa (high eq) j js).symm
    exact absent ⟨j,js,b,bb,bh,support,by rw [contact]; omega⟩
  have dis : Disjoint Q R := disjoint_left.mpr (fun _ hq hr => (mem_sdiff.mp hr).2 hq)
  have qr : Q∪R=D := by
    ext v
    constructor
    · intro h
      exact (mem_union.mp h).elim qsub sdiff_subset
    · intro h
      by_cases q : v∈Q
      · exact mem_union_left _ q
      · exact mem_union_right _ (mem_sdiff.mpr ⟨h,q⟩)
  have incidences := incidence_bound cut cap four za D Q R M dsub (filter_subset _ _) qr dis
    (fun j jm => by rw [dist_comm]; exact zMiss jm) one two
  have p := card_sdiff_add_card_eq_card (filter_subset (fun v => ∃ j∈S,G.Adj v j) B)
  have q := card_sdiff_add_card_eq_card qsub
  change D.card+P.card=B.card at p
  change R.card+Q.card=D.card at q
  exact arithmetic accept mPos (by omega) bPort qBudget incidences

theorem degree18_row_14_70 (hc : G.Connected) (cut : CutSides G A B S)
    (cap : ∀ v,G.distEven v≤G.secondSmallestDegree+1) (four : S.card=4)
    (anchors : ∀ i∈S,G.secondSmallestDegree≤G.degree i)
    (smaller : ∀ T : Finset V,T.card<S.card → (G.induce {v : V | v∉T}).Connected)
    (degree : G.secondSmallestDegree=18)
    (small : (A.filter fun a => G.secondSmallestDegree≤G.degree a).card=14)
    (large : (B.filter fun b => G.secondSmallestDegree≤G.degree b).card=70) :
    ∃ i ∈ S, ∃ b ∈ B, G.secondSmallestDegree≤G.degree b ∧ S.filter (G.Adj b)={i} ∧
      G.secondSmallestDegree+1≤S.card+(A∩G.neighborFinset i).card := by
  classical
  have base := card_filter_le B (fun b => G.secondSmallestDegree≤G.degree b)
  rw [large] at base
  have accept : check G.secondSmallestDegree B.card = true := by
    rw [degree]
    exact check_mono checked_18_70 base
  exact eligible hc cut cap four anchors smaller
    (card_pos.mp (by omega)) (by omega) accept


/-- The row cannot occur once every reoriented minimum cut gives at least
two common high labels, precisely the outer recut premise of the replay. -/
theorem exclude_degree18_row_14_70 (hc : G.Connected) (cut : CutSides G A B S)
    (cap : ∀ v,G.distEven v≤G.secondSmallestDegree+1) (four : S.card=4)
    (anchors : ∀ i∈S,G.secondSmallestDegree≤G.degree i)
    (minimum : S.card=G.vertexConnectivity)
    (degree : G.secondSmallestDegree=18)
    (small : (A.filter fun a => G.secondSmallestDegree≤G.degree a).card=14)
    (large : (B.filter fun b => G.secondSmallestDegree≤G.degree b).card=70)
    (uniform : ∀ W F T : Finset V, CutSides G W F T → T.card=G.vertexConnectivity →
      (W.filter (fun q => G.secondSmallestDegree≤G.degree q)).card ≤
        (F.filter (fun q => G.secondSmallestDegree≤G.degree q)).card →
      ∀ q∈W,G.secondSmallestDegree≤G.degree q → 2≤(T.filter (G.Adj q)).card) :
    False := by
  classical
  have smaller (T : Finset V) (ht : T.card<S.card) :=
    Graph189CutSides.connected_after_smaller_deletion (G:=G) T (ht.trans_eq minimum)
  obtain ⟨i,_,b,bb,bh,support,many⟩ :=
    degree18_row_14_70 hc cut cap four anchors smaller degree small large
  let X := A.filter fun a => G.secondSmallestDegree≤G.degree a
  have cards := card_le_univ (X∪B)
  rw [card_union_of_disjoint (cut.apart.mono_left (filter_subset _ _))] at cards
  have base := card_filter_le B (fun b => G.secondSmallestDegree≤G.degree b)
  change X.card=14 at small
  rw [large] at base
  have room : 4*G.secondSmallestDegree+S.card+1≤Fintype.card V := by omega
  exact Graph189FourCut.private_recut hc cut minimum
    (fun v => by simpa [Nat.add_comm] using cap v) room bb bh support many uniform

#print axioms Graph189FourSmallestRow.checked_18_70
#print axioms Graph189FourSmallestRow.degree18_row_14_70
#print axioms Graph189FourSmallestRow.exclude_degree18_row_14_70

end Graph189FourSmallestRow
