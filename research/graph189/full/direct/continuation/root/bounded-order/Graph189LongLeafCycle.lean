import Graph189ExteriorCycleSpan
import Graph189ShortLeafOrder

open SimpleGraph Finset Graph189OptimalExterior Graph189ExteriorGap
namespace Graph189ExteriorLeaf
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem large_leaf_arithmetic {k q m n c s : ℕ} (lo : 7≤k) (hi : k≤21)
    (half : k≤2*q) (leaf : 2*q+(k+1)/2≤m+1) (cycle : 2*q≤c+1)
    (links : m+2*c+2*((c+1)/2)+5≤n) (ord : n≤5*k-5)
    (core : 3*q+3≤2*k → m+s+(s+1)*q≤n ∧ 2*k≤s+3*q+1) : False := by
  let b := 2*q-1+(k+1)/2
  let t := 2*k-(3*q+1)
  have table : (List.range 15).all (fun j => let k := 7+j
    (List.range (k+1)).all (fun q =>
      let b := 2*q-1+(k+1)/2
      let t := 2*k-(3*q+1)
      decide (k≤2*q → 5*k-5 < b+2*(2*q-1)+2*q+5 ∨
        3*q+3≤2*k ∧ 5*k-5 < b+t+(t+1)*q)))=true := by decide
  have row := List.all_eq_true.mp table (k-7) (List.mem_range.mpr (by omega))
  rw [show 7+(k-7)=k by omega] at row
  have idx : q<k+1 := by omega
  have cell := List.all_eq_true.mp row q (List.mem_range.mpr idx)
  have v := of_decide_eq_true cell half
  change 5*k-5 < b+2*(2*q-1)+2*q+5 ∨ 3*q+3≤2*k ∧ 5*k-5 < b+t+(t+1)*q at v
  have bm : b≤m := by dsimp [b]; omega
  rcases v with v|⟨dense,v⟩
  · omega
  obtain ⟨bound,ts⟩ := core dense
  have low : t≤s := by dsimp [t]; omega
  have prod := Nat.mul_le_mul_right q (show t+1≤s+1 by omega)
  omega

/-- In the large-leaf branch even one cycle of the required Fan length is
incompatible with the graph hypotheses throughout the remaining range. -/
theorem no_long_leaf_cycle {a b : V} {p : G.Walk a b} {C D : Finset V} {w x : V} {k : ℕ}
    (h : Chosen p C k) (L : Limb G C D w) (conn : 3≤G.vertexConnectivity)
    (xd : x∈D) (high : k≤G.degree x) (noncut : (G.induce (C.erase x:Set V)).Preconnected)
    (large : 2*(G.neighborFinset x∩C).card≤D.card+2)
    {z : V} (Z : G.Walk z z) (cycle : Z.IsCycle) (inside : ∀v∈Z.support,v∈C)
    (long : 2*(G.neighborFinset x∩C).card≤Z.length+1)
    (lo : 7≤k) (hi : k≤21) (order : Fintype.card V≤5*k-5)
    (quota : ∀v,(univ.filter (fun z => G.dist v z=2)).card≤k)
    (minimum : ∀v,3≤G.degree v) (uniqueLow : ∀u v,G.degree u<k → G.degree v<k → u=v) : False := by
  classical
  let q := (G.neighborFinset x∩C).card
  let r := (C.filter (fun y => G.dist x y=2)).card
  let s := min q (k-q-r)
  have half := high.trans (internal_half h (L.sub xd) high (quota _) minimum uniqueLow)
  have ra := (remainder_route h L (by omega) quota minimum uniqueLow).1
  change (k+1)/2≤(C \ insert w D).card at ra
  have compare := card_sdiff_add_card_eq_card (insert_subset L.gate L.sub)
  rw [card_insert_of_notMem L.fresh] at compare
  apply large_leaf_arithmetic (s:=s) lo hi half (by omega) long (cycle_span h conn Z cycle inside) order
  exact fun dense => noncut_order h (L.sub xd) high noncut minimum uniqueLow (quota _) (by omega) dense

end Graph189ExteriorLeaf
#print axioms Graph189ExteriorLeaf.no_long_leaf_cycle
