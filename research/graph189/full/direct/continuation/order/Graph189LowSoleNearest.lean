import Graph189MarkedLowCut
import Graph189TwoSoleNearest
import Graph189PairLinearGap

open SimpleGraph Finset Graph189SoleNearestSides Graph189DenseSideRoute
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189LowSoleNearest
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V}

/-- A side containing the unique low vertex still admits a path starting at the
common nearest anchor and omitting at most five side vertices. -/
theorem low_route (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (con : (G.induce (A:Set V)).Connected) (sc : S.card≤G.vertexConnectivity)
    (two : S.card=2) (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    (large : 7≤G.secondSmallestDegree) {z x i y : V} (za : z∈A) (low : G.degree z<G.secondSmallestDegree)
    (left : Witness G A S x i) (right : Witness G B S y i) : Route G A i 5 := by
  classical
  let k := G.secondSmallestDegree
  let R := A.erase z
  let J := G.induce (A:Set V)
  let z' : A := ⟨z,za⟩
  change 7≤k at large
  change G.degree z<k at low
  have sz : R.card+1=A.card := card_erase_add_one za
  have high {v : V} (ne : v≠z) : k≤G.degree v :=
    (degree_pair (G:=G) v z ne).resolve_right (Nat.not_le.mpr low)
  have boundary {v u : V} (va : v∈A) (vu : G.Adj v u) (ua : u∉A) : u∈S := by
    rcases sides.cover u with h|h|h
    · exact (ua h).elim
    · exact (sides.no_cross v va u h vu).elim
    · exact h
  obtain ⟨contacts,misses⟩ := debit hc sides.swap sc cap right
  change (A.filter (G.Adj i)).card+S.card≤k+1 at contacts
  have sub : R.filter (fun v => ¬G.Adj i v)⊆
      ((A.filter (fun v => G.secondSmallestDegree≤G.degree v)).filter (fun v => ¬G.Adj i v)) := by
    intro v hv
    obtain ⟨vr,non⟩ := mem_filter.mp hv
    obtain ⟨ne,va⟩ := mem_erase.mp vr
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨va,high ne⟩,non⟩
  have remote : (R.filter (fun v => ¬G.Adj i v)).card+S.card≤k :=
    (Nat.add_le_add_right (card_le_card sub) _).trans misses
  have ports := card_le_card (filter_subset_filter (G.Adj i) (erase_subset z A))
  change (R.filter (G.Adj i)).card≤(A.filter (G.Adj i)).card at ports
  have counts := card_filter_add_card_filter_not (s:=R) (p:=G.Adj i)
  have nR : R.card≤2*k-3 := by omega
  have minR (v : R) : k-3≤(G.induce (R:Set V)).degree v := by
    have bd := retained (G:=G) R (insert z S) (fun v vr u vu ur => by
      by_cases h : u=z
      · exact mem_insert.mpr (Or.inl h)
      · apply mem_insert_of_mem
        exact boundary (mem_erase.mp vr).2 vu (fun ua => ur (mem_erase.mpr ⟨h,ua⟩))) v
    have szT := card_insert_le z S
    have hv := high (mem_erase.mp v.property).1
    omega
  have xn : G.neighborFinset x ⊆ A.erase x := by
    intro v hv
    have adj := (G.mem_neighborFinset _ _).mp hv
    refine mem_erase.mpr ⟨adj.ne.symm,?_⟩
    by_contra non
    exact left.nonport v (boundary left.side adj non) adj.symm
  have lower := card_le_card xn
  rw [G.card_neighborFinset_eq_degree] at lower
  have xl := left.high
  change k≤G.degree x at xl
  have er := card_erase_add_one left.side
  have enough : 0<(R.filter (G.Adj i)).card := by omega
  obtain ⟨v,mv⟩ := card_pos.mp enough
  by_cases ok : R.card≤2*(k-3)+1 ∨ (G.induce (R:Set V)).Connected
  · obtain ⟨a,b,p,hp,ia,inside,near⟩ := from_region R i (d:=k-3) (t:=2) (b:=2) (by omega)
      minR (by omega) (by omega) ok ⟨v,(mem_filter.mp mv).1,(mem_filter.mp mv).2⟩ (by omega) (by omega)
    exact ⟨a,b,p,hp,ia,fun w hw => (mem_erase.mp (inside w hw)).2,by omega⟩
  push_neg at ok
  have growth := ok.1
  letI : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_coe]; omega)
  let P := (A.filter (G.Adj i)).subtype (fun v => v∈A)
  have cardP : P.card=(A.filter (G.Adj i)).card := by
    rw [show P=(A.filter (G.Adj i)).subtype (fun v => v∈A) from rfl,card_subtype,
      filter_eq_self.mpr (fun v h => (mem_filter.mp h).1)]
  have marks : 3≤(P.erase z').card := by
    by_cases zP : z'∈P
    · have er := card_erase_add_one zP
      omega
    · rw [erase_eq_of_notMem zP]
      omega
  have disc : ¬(J.induce {v : A | v∉({z'}:Finset A)}).Connected := by
    intro connected
    let f : (J.induce {v : A | v∉({z'}:Finset A)}) →g G.induce (R:Set V) :=
      { toFun := fun v => ⟨v.val.val,mem_erase.mpr ⟨fun eq => v.property (mem_singleton.mpr (Subtype.ext eq)),v.val.property⟩⟩
        map_rel' := fun h => h }
    apply ok.2 (SimpleGraph.Connected.map f (fun v => ?_) connected)
    have vr := mem_erase.mp v.property
    refine ⟨⟨⟨v.val,vr.2⟩,fun eq => vr.1 (congrArg Subtype.val (mem_singleton.mp eq))⟩,rfl⟩
  have minJ (v : A) (ne : v≠z') : (k-3)+1≤J.degree v := by
    have h := high (v:=v.val) (fun eq => ne (Subtype.ext eq))
    have bd := retained (G:=G) A S (fun _ va _ vu ua => boundary va vu ua) v
    change G.degree v.val≤J.degree v+S.card at bd
    omega
  obtain ⟨a,aP,b,q,hq⟩ := Graph189MarkedLowCut.of_cut (G:=J) con z' P (d:=k-3) (by omega)
    minJ (by change Fintype.card A≤3*(k-3); rw [Fintype.card_coe]; omega) marks disc
  let f := (Embedding.induce (G:=G) (A:Set V)).toHom
  let r := q.map f
  have aports : a.val∈A.filter (G.Adj i) := mem_subtype.mp aP
  refine ⟨_,_,r,hq.isPath.map Subtype.val_injective,(mem_filter.mp aports).2,?_,?_⟩
  · intro v hv
    rw [show r.support=q.support.map f from Walk.support_map _ _] at hv
    obtain ⟨v',_,rfl⟩ := List.mem_map.mp hv
    exact v'.property
  · have eq : r.support.length=q.support.length := by simp [r]
    rw [eq,hq.length_support]
    change A.card≤Fintype.card A+5
    rw [Fintype.card_coe]
    omega

/-- At two connected sides of an original two-cut, a singly nearest high
nonport on both sides forces an original spanning path, wherever the low
vertex lies. -/
theorem traceable (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (sides : Graph189CutSides.CutSides G A B S) (sc : S.card≤G.vertexConnectivity)
    (two : S.card=2) (large : 10≤G.secondSmallestDegree)
    (aCon : (G.induce (A:Set V)).Connected) (bCon : (G.induce (B:Set V)).Connected)
    {x i y j : V} (left : Witness G A S x i) (right : Witness G B S y j) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have eq := Graph189TwoSoleNearest.same_anchor hc sides point left right
  subst j
  have low_case {A B : Finset V} {x y : V} (sides : Graph189CutSides.CutSides G A B S)
      (con : (G.induce (A:Set V)).Connected) (left : Witness G A S x i) (right : Witness G B S y i)
      (z : V) (za : z∈A) (low : G.degree z<G.secondSmallestDegree) :
      ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
    have hB (v : V) (vb : v∈B) : G.secondSmallestDegree≤G.degree v := by
      have nz : v≠z := fun eq => Finset.disjoint_left.mp sides.apart za (eq ▸ vb)
      exact (degree_pair (G:=G) v z nz).resolve_right (Nat.not_le.mpr low)
    obtain ⟨a,b,p,hp,near⟩ := Graph189TwoSoleNearest.join_routes sides left.anchor
      (low_route hc sides con sc two point (by omega) za low left right)
      (Graph189TwoSoleNearest.high_route hc sides.swap sc two point (by omega) hB left)
    exact Graph189PairLinearGap.traceable hc cap (by omega) (by omega)
      (Graph189PairLinearGap.order hc sides sc two point left right) p hp (by omega)
  by_cases hA : ∀v∈A, G.secondSmallestDegree≤G.degree v
  · by_cases hB : ∀v∈B, G.secondSmallestDegree≤G.degree v
    · exact Graph189TwoSoleNearest.all_high hc sides sc two point (by omega) hA hB left right
    · push_neg at hB
      obtain ⟨z,zb,hz⟩ := hB
      exact low_case sides.swap bCon right left z zb hz
  · push_neg at hA
    obtain ⟨z,za,hz⟩ := hA
    exact low_case sides aCon left right z za hz

#print axioms low_route
#print axioms traceable
end Graph189LowSoleNearest
