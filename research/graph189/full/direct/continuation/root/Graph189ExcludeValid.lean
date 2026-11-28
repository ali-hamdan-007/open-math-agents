import Graph189CommonTerminal
import Graph189MissingLabels
import Graph189GraphPopulation
import Graph189ResidualTerminal
import Graph189FullLabelExit

open Finset SimpleGraph Graph189FiniteDomain
namespace Graph189ExcludeValid
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- An arbitrary valid band contradicts the separator structure of an actual two-connected
graph satisfying the original even-distance cap, provided its order reaches the band. -/
theorem impossible (hc : G.Connected) (cap : ∀ v, G.distEven v ≤ 1+G.secondSmallestDegree)
    (deletion : ∀ z : V, (G.induce {v : V | v ≠ z}).Connected)
    {r : Band} (ok : valid r = true) (rs : r.s = G.vertexConnectivity) (rk : r.k = G.secondSmallestDegree)
    (low : r.low ≤ Fintype.card V) : False := by
  classical
  let k := G.secondSmallestDegree
  let H (P : Finset V) := P.filter (fun v => k ≤ G.degree v)
  let core (P T : Finset V) := T.filter (fun i => ∀ a ∈ P, k ≤ G.degree a → G.Adj a i)
  have num := ok
  simp only [valid,decide_eq_true_eq] at num
  obtain ⟨s5,degree,_⟩ := num
  have higher := (Graph189CutSides.valid_recut_order ok).trans low
  rw [rs,rk] at higher
  have room : G.vertexConnectivity < Fintype.card V-1 := by omega
  have uniform {W F T : Finset V} (cut : Graph189CutSides.CutSides G W F T)
      (eq : T.card = G.vertexConnectivity) (small : (H W).card ≤ (H F).card) :
      3 ≤ (core W T).card :=
    Graph189CommonTerminal.three_common hc cut deletion eq cap small ok (by omega) rk low
  have allTwo (W F T : Finset V) (cut : Graph189CutSides.CutSides G W F T)
      (eq : T.card = G.vertexConnectivity) (small : (H W).card ≤ (H F).card)
      (y : V) (yw : y ∈ W) (yh : k ≤ G.degree y) : 2 ≤ (T.filter (G.Adj y)).card := by
    have sub : core W T ⊆ T.filter (G.Adj y) := by
      intro i hi
      obtain ⟨it,common⟩ := mem_filter.mp hi
      exact mem_filter.mpr ⟨it,common y yw yh⟩
    have sz := uniform cut eq small
    have b := card_le_card sub
    omega
  obtain ⟨U,F,S,minimum,sides⟩ := Graph189GraphPopulation.minimum_sides (G:=G) room
  have select : ∃ A B : Finset V, Graph189CutSides.CutSides G A B S ∧ (H A).card ≤ (H B).card := by
    rcases le_total (H U).card (H F).card with h | h
    · exact ⟨U,F,sides,h⟩
    · exact ⟨F,U,sides.swap,h⟩
  obtain ⟨A,B,cut,orient⟩ := select
  let C := core A S
  have cs : C ⊆ S := filter_subset _ _
  have c3 : 3 ≤ C.card := uniform cut minimum orient
  have ss : 2 ≤ S.card := by omega
  have small (T : Finset V) (lt : T.card < S.card) :=
    Graph189CutSides.connected_after_smaller_deletion (G:=G) T (lt.trans_eq minimum)
  have common (a : V) (aa : a ∈ A) (ah : k ≤ G.degree a) (j : V) (jc : j ∈ C) :=
    (mem_filter.mp jc).2 a aa ah
  obtain ⟨_,big,order,_⟩ := Graph189CommonTerminal.cut_bounds hc cut minimum cap orient ok (by omega) rk low
  have cap' (v : V) : G.distEven v ≤ k+1 := by simpa [k,Nat.add_comm] using cap v
  have contact {j : V} (js : j∈S) : ∃ a∈A, k≤G.degree a ∧ G.Adj a j :=
    Graph189HighLabel.all_labels_in_order_range hc cut deletion small cap'
      (big.trans_le (card_le_card (filter_subset _ _))) order js
  obtain ⟨i,ic⟩ := card_pos.mp (show 0<C.card by omega)
  by_cases full : ∃ a ∈ A, k≤G.degree a ∧ ∀ j ∈ S, G.Adj a j
  · obtain ⟨a,aa,ah,whole⟩ := full
    obtain ⟨j,_,b,hb,bh,support,many⟩ := Graph189FullLabelExit.full_exit hc cut cap' ss big aa ah whole
      (cs ic) (fun v va vh => common v va vh i ic)
    exact cut.private_port_terminal_band hc cap minimum ok (by omega) rk low allTwo hb bh support many
  push Not at full
  have each (j : V) (js : j∈S) : ∃ x∈H A, G.Adj x j := by
    obtain ⟨x,xa,xh,edge⟩ := contact js
    exact ⟨x,mem_filter.mpr ⟨xa,xh⟩,edge⟩
  obtain ⟨a,ax,_⟩ := each i (cs ic)
  have notFull (x : V) (hx : x ∈ H A) : ¬∀ j ∈ S, G.Adj x j := by
    obtain ⟨j,js,lack⟩ := full x (mem_filter.mp hx).1 (mem_filter.mp hx).2
    exact fun all => lack (all j js)
  have two := Graph189MissingLabels.two_residual (show (H A).Nonempty from ⟨a,ax⟩) each
    (fun x hx => common x (mem_filter.mp hx).1 (mem_filter.mp hx).2) notFull
  have D_eq : S.filter (fun i => ∃ a∈H A, ¬G.Adj a i) = S \ C := by
    ext i
    constructor
    · intro hi
      obtain ⟨si,x,hx,miss⟩ := mem_filter.mp hi
      exact mem_sdiff.mpr ⟨si,fun ci => miss (common x (mem_filter.mp hx).1 (mem_filter.mp hx).2 i ci)⟩
    · intro hi
      obtain ⟨si,nc⟩ := mem_sdiff.mp hi
      have lack : ¬∀ x∈A, k≤G.degree x → G.Adj x i := fun h => nc (mem_filter.mpr ⟨si,h⟩)
      push Not at lack
      obtain ⟨a,aa,ah,miss⟩ := lack
      exact mem_filter.mpr ⟨si,a,mem_filter.mpr ⟨aa,ah⟩,miss⟩
  have singles (x : V) (xa : x ∈ A) (xh : k ≤ G.degree x) :
      (Graph189PortLabels.support G S x \ C).card ≤ 1 := by
    have hx : x∈H A := mem_filter.mpr ⟨xa,xh⟩
    rcases Graph189CutFamilies.singleton_or_two_missing hc cut small deletion cap big order with left | few
    · have row : Graph189PortLabels.support G S x \ C =
          (Graph189PortLabels.support G S x).filter (fun i => ∃ y∈H A, ¬G.Adj y i) := by
        ext i
        constructor
        · intro hi
          obtain ⟨sup,nc⟩ := mem_sdiff.mp hi
          have mm : i∈S.filter (fun j => ∃ y∈H A, ¬G.Adj y j) := D_eq.symm ▸ mem_sdiff.mpr ⟨(mem_filter.mp sup).1,nc⟩
          exact mem_filter.mpr ⟨sup,(mem_filter.mp mm).2⟩
        · intro hi
          obtain ⟨sup,y,hy,miss⟩ := mem_filter.mp hi
          exact mem_sdiff.mpr ⟨sup,fun ci => miss (common y (mem_filter.mp hy).1 (mem_filter.mp hy).2 i ci)⟩
      rw [row]
      exact left x hx
    · change (S.filter (fun i => ∃ a∈H A, ¬G.Adj a i)).card ≤ 2 at few
      rw [D_eq] at few
      exact Graph189MissingLabels.at_most_one (common x xa xh) (notFull x hx) few
  exact Graph189ResidualPrivatePort.terminal_of_missing_label hc cut cap minimum ok (by omega) rk low
    C cs c3 two (fun j hj => contact (mem_sdiff.mp hj).1) common singles
    ⟨a,(mem_filter.mp ax).1,(mem_filter.mp ax).2,full a (mem_filter.mp ax).1 (mem_filter.mp ax).2⟩ big allTwo

#print axioms impossible
end Graph189ExcludeValid
