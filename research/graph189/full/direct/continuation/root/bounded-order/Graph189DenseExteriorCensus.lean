import Graph189DenseMatching
import Graph189DenseExteriorOrder
import Graph189ExtraPort

open SimpleGraph Finset Graph189OptimalExterior Graph189ExteriorGap
namespace Graph189ExteriorLeaf
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The contact matching accounts for all but three vertices outside the
path and the selected component. Any such vertex has degree below k. -/
theorem dense_exterior_census {a b : V} {p : G.Walk a b} {C : Finset V} {k : ℕ}
    (h : Chosen p C k) (r : ComponentRoutes p C) (small : C.card+2≤k)
    (lo : 7≤k) (upper : Fintype.card V≤5*k-5)
    (quota : ∀v,(univ.filter (fun z => G.dist v z=2)).card≤k)
    (minimum : ∀v,3≤G.degree v) (uniqueLow : ∀u v,G.degree u<k → G.degree v<k → u=v)
    (gap : p.support.length+(k+1)/2+1<Fintype.card V) :
    let H := C.filter (fun v => k≤G.degree v)
    let s := k+1-C.card
    let E := p.support.toFinsetᶜ
    s<H.card ∧ E.card≤C.card+3 ∧ (∀v∈E, v∉C → G.degree v<k) ∧
    5*k-8≤Fintype.card V ∧ Fintype.card V+1<(s+3)*C.card+s+1 := by
  classical
  let H := C.filter (fun v => k≤G.degree v)
  let m := C.card
  let s := k+1-m
  let E := p.support.toFinsetᶜ
  change s<H.card ∧ E.card≤m+3 ∧ _ ∧ _ ∧ _
  have LH : (C \ H).card≤1 := card_le_one_iff.mpr (by
    intro u v hu hv
    have low {w : V} (hw : w∈C \ H) : G.degree w<k :=
      Nat.lt_of_not_ge (fun high => (mem_sdiff.mp hw).2 (mem_filter.mpr ⟨(mem_sdiff.mp hw).1,high⟩))
    exact uniqueLow _ _ (low hu) (low hv))
  have Hsub : H⊆C := filter_subset _ _
  have parts := card_sdiff_add_card_eq_card Hsub
  change (C \ H).card+H.card=m at parts
  obtain ⟨x,xc,xh⟩ := h.high
  have half := xh.trans (internal_half h xc xh (quota _) minimum uniqueLow)
  have lowQ : (G.neighborFinset x∩C).card<m := by
    have sub : G.neighborFinset x∩C ⊆ C.erase x := fun v hv => mem_erase.mpr
      ⟨((G.mem_neighborFinset _ _).mp (mem_inter.mp hv).1).ne.symm,(mem_inter.mp hv).2⟩
    have := card_le_card sub
    have := card_erase_add_one xc
    dsimp [m]; omega
  change m+2≤k at small
  have sum : m+s=k+1 := by dsimp [s]; omega
  have many : s≤H.card := by omega
  have three : 3≤s := by omega
  have pos : 5≤m := by omega
  let links (v : V) := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] v)
  have rows (v : V) (vh : v∈H) : s≤(links v).card := by
    have hv := mem_filter.mp vh
    have bound := Graph189DenseExteriorOrder.neighbors_on_path p C
      (fun x xc y e out => by by_contra miss; exact out (h.closed x xc y e miss)) hv.1
    change G.degree v+1≤m+(links v).card at bound
    omega
  obtain ⟨M,count,f,edges⟩ := Graph189ExteriorAttachment.marks_of_many_neighbors p H s many rows
  let inc : H ↪ C := ⟨fun v => ⟨v.val,Hsub v.property⟩,fun u v eq => Subtype.ext (congrArg (fun q:C => q.val) eq)⟩
  have off (v : V) (ve : v∈E) : v∉p.support := fun on => (mem_compl.mp ve) (List.mem_toFinset.mpr on)
  have need := near_match_with_omissions h r E off M (card_pos.mp (by omega)) (f.trans inc) edges
  rw [count] at need
  change E.card+(s+1)*m+s≤Fintype.card V+1 at need
  have inE : C⊆E := fun v vc => mem_compl.mpr (fun on => h.outside _ vc (List.mem_toFinset.mp on))
  have CE : m≤E.card := card_le_card inE
  have arith : 5*k≤(s+2)*m+s+7 := by
    have prod' := Int.mul_nonneg (show 0≤(s:ℤ)-3 by omega) (show 0≤(m:ℤ)-4 by omega)
    zify at sum ⊢
    nlinarith only [sum,prod']
  have pack : E.card≤m+3 ∧ 5*k-8≤Fintype.card V ∧ Fintype.card V+1<(s+3)*m+s+1 := by
    simp only [Nat.add_mul,Nat.one_mul] at need arith ⊢
    omega
  have spare := card_sdiff_add_card_eq_card inE
  have tiny : (E \ C).card≤3 := by change (E \ C).card+m=E.card at spare; omega
  have noExtra (v : V) (ve : v∈E) (vc : v∉C) : G.degree v<k := by
    by_contra! high
    have halfV := (high_exterior_half p h.path h.longest (off _ ve) (quota _) high minimum uniqueLow).2
    have sub : G.neighborFinset v \ p.support.toFinset ⊆ E \ C := by
      intro w hw
      have m := mem_sdiff.mp hw
      have adj := (G.mem_neighborFinset _ _).mp m.1
      exact mem_sdiff.mpr ⟨mem_compl.mpr m.2,fun wc => vc (h.closed w wc v adj.symm (off _ ve))⟩
    have := card_le_card sub
    omega
  refine ⟨?_,pack.1,noExtra,pack.2⟩
  by_contra! fail
  have all : E=C := by
    apply Subset.antisymm _ inE
    intro w we
    by_contra wc
    obtain ⟨v,vs⟩ := card_pos.mp (show 0<(C \ H).card by omega)
    have low : G.degree v<k := Nat.lt_of_not_ge (fun vh => (mem_sdiff.mp vs).2
      (mem_filter.mpr ⟨(mem_sdiff.mp vs).1,vh⟩))
    exact wc ((uniqueLow w v (noExtra w we wc) low).symm ▸ (mem_sdiff.mp vs).1)
  have total := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup h.path.support_nodup] at total
  change p.support.length+E.card=Fintype.card V at total
  rw [all] at total
  change p.support.length+m=Fintype.card V at total
  omega

end Graph189ExteriorLeaf
#print axioms Graph189ExteriorLeaf.dense_exterior_census
