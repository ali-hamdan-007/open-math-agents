import Graph189FourFiveFloor
import Graph189MatchedFloor
import Graph189FiveConnectivity19
import Graph189ThirdLayerDegreeCeiling

open SimpleGraph Finset
namespace Graph189WidthSectors

private def test (b k e : ℕ) : Bool :=
  let w := Graph189RootWidth.width b k (k+e)
  let L := b-(k+e)-k-2
  decide (w*L≤k*(k+e) ∧ (w-k)*L≤k*k ∧ b≤3*k+1+(k-2)*e)

private def clearAt (b k : ℕ) : Bool :=
  (List.range (2*k+1-(if 5*k+2<b then 3 else 0))).all fun e => !(test b k e)

private def base4 (k : ℕ) := 6*k-(if 24≤k then 19 else 20)
private def base5 (k : ℕ) := 7*k-31
private def base6 (k : ℕ) := 7*k-29

private theorem checked :
    ([20,21,22,23,24,25,26,27,28].all fun k => clearAt (base4 k) k)=true ∧
    ([15,16,17].all fun k => clearAt (base5 k) k)=true ∧
    ([14,15,16,17].all fun k => clearAt (base6 k) k)=true := by decide

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem exclude (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (bad : ¬∃ a b,∃p : G.Walk a b,p.IsHamiltonian)
    {b : ℕ} (ord : b≤Fintype.card V) (hk : 3≤G.secondSmallestDegree)
    (table : clearAt b G.secondSmallestDegree=true) : False := by
  let k := G.secondSmallestDegree
  let e := G.maxDegree-k
  have fit := Graph189MatchedFloor.necessary hc cap bad ord hk
  change Graph189MatchedFloor.Fits b k e at fit
  obtain ⟨first,second,ore,_⟩ := fit
  have w := (Graph189MatchedRootWidth.width_admissible b k (k+e)).1
  have v := (Nat.mul_le_mul_right (b-(k+e)-k-2) w).trans first
  have v' := (Nat.mul_le_mul_right (b-(k+e)-k-2) (Nat.sub_le_sub_right w k)).trans second
  have oreN : b≤3*k+1+(k-2)*e := by
    have h : ((k-2:ℕ):ℤ)=(k:ℤ)-2 := by change 3≤k at hk; omega
    exact_mod_cast (show (b:ℤ)≤3*(k:ℤ)+1+((k-2:ℕ):ℤ)*(e:ℤ) by rwa [h])
  have testYes : test b k e=true := decide_eq_true ⟨v,v',oreN⟩
  have lim := Graph189DegreeCeiling.maxDegree_le_three_mul_secondSmallestDegree hc
    (fun v => (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap)
  have idx : e<2*k+1-(if 5*k+2<b then 3 else 0) := by
    dsimp only [e]
    change G.maxDegree≤3*k at lim
    split_ifs with big
    · have h := Graph189ThirdLayerDegreeCeiling.max_degree hc cap (big.trans_le ord)
      change G.maxDegree+3≤3*k at h
      omega
    omega
  have no := List.all_eq_true.mp table e (List.mem_range.mpr idx)
  change (!test b k e)=true at no
  simp [testYes] at no

/-- The original statement at every order for minimum four-cuts in the indicated interval. -/
theorem four (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (conn : G.vertexConnectivity=4) (lo : 20≤G.secondSmallestDegree) (hi : G.secondSmallestDegree≤28) :
    ∃a b,∃p : G.Walk a b,p.IsHamiltonian := by
  by_contra bad
  let k := G.secondSmallestDegree
  have f := (Graph189FourFiveFloor.order hc cap bad (Or.inl ⟨conn,by omega⟩)).1 conn
  change 6*k≤Fintype.card V+20 ∧ _ at f
  have lower : base4 k≤Fintype.card V := by unfold base4; split_ifs with h <;> grind
  apply exclude hc cap bad lower (by omega)
  apply List.all_eq_true.mp checked.1 k
  change 20≤k at lo
  change k≤28 at hi
  simp; omega

/-- Original graph conclusion for arbitrary connectivity at least five from degree fifteen. -/
theorem five (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (conn : 5≤G.vertexConnectivity) (lo : 15≤G.secondSmallestDegree) :
    ∃a b,∃p : G.Walk a b,p.IsHamiltonian := by
  by_cases high : 18≤G.secondSmallestDegree
  · exact Graph189FiveConnectivity.traceable_ge18 hc cap high conn
  by_contra bad
  let k := G.secondSmallestDegree
  change 15≤k at lo
  change ¬18≤k at high
  by_cases eq : G.vertexConnectivity=5
  · have f := (Graph189FourFiveFloor.order hc cap bad (Or.inr ⟨eq,lo⟩)).2 eq
    apply exclude hc cap bad (b:=base5 k) (by unfold base5; omega) (by change 3≤k; omega)
    apply List.all_eq_true.mp checked.2.1 k
    simp; omega
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have f := Graph189RotationLinked.base_order bad point (l:=6) (by decide) (by omega) (by change 13≤k; omega)
  change 7*(k-6+2)≤Fintype.card V+1 at f
  apply exclude hc cap bad (b:=base6 k) (by unfold base6; omega) (by change 3≤k; omega)
  apply List.all_eq_true.mp checked.2.2 k
  simp; omega

end Graph189WidthSectors
#print axioms Graph189WidthSectors.four
#print axioms Graph189WidthSectors.five
