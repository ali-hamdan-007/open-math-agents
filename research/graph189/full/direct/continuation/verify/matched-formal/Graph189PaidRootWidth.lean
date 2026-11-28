import Graph189MatchedRootWidth
import Graph189RootDegreeSavings

open SimpleGraph Finset OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189PaidRootWidth
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Charge both retained degree shortfalls in the maximum-root width argument,
at any certified lower bound b on the actual order. -/
theorem bound (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    {b w t m : ℕ} (order : b≤Fintype.card V) (W : w≤Graph189RootWidth.width b G.secondSmallestDegree G.maxDegree)
    (fit : m+t≤w+1) (spend : m≤G.maxDegree-G.secondSmallestDegree)
    (floor : 2*G.secondSmallestDegree+(G.secondSmallestDegree+1)*(t-1)<b) :
    (G.secondSmallestDegree*w+m*t)*(b-G.maxDegree-G.secondSmallestDegree-2)≤
      G.secondSmallestDegree*(G.secondSmallestDegree*G.maxDegree) := by
  classical
  let k := G.secondSmallestDegree
  let n := Fintype.card V
  obtain ⟨x,hx⟩ := G.exists_maximal_degree_vertex
  let A := G.neighborFinset x
  let B := univ.filter (fun j => G.dist x j=2)
  let C := Graph189HighThirdLayer.highThird G x
  have large : k≤G.degree x := by
    obtain ⟨p,q,ne⟩ := exists_pair_ne V
    rw [←hx]
    rcases degree_pair (G:=G) p q ne with h|h
    · exact h.trans (G.degree_le_maxDegree p)
    · exact h.trans (G.degree_le_maxDegree q)
  have top (a : V) : G.degree a≤G.degree x := hx ▸ G.degree_le_maxDegree a
  have point (a : V) : G.distEven a≤1+k := (le_max' _ _ (mem_image_of_mem _ (mem_univ a))).trans cap
  have cp (a : V) : G.distEven a≤k+1 := by simpa only [Nat.add_comm 1] using point a
  have layerB (j : V) (hj : j∈B) : G.dist x j=2 := (mem_filter.mp hj).2
  have allB (j : V) (hj : G.dist x j=2) : j∈B := mem_filter.mpr ⟨mem_univ _,hj⟩
  have pred (j : V) (hj : j∈B) : ∃i,G.Adj x i ∧ G.Adj i j := by
    obtain ⟨i,di,ij⟩ := Graph189MatchedRootWidth.predecessor (j:=1) (layerB j hj)
    exact ⟨i,dist_eq_one_iff_adj.mp di,ij⟩
  have layerC (y : V) (hy : y∈C) : G.dist x y=3 := (mem_filter.mp hy).2.1
  have high (y : V) (hy : y∈C) : k≤G.degree y := (mem_filter.mp hy).2.2
  have linear : w≤Graph189RootWidth.width n k (G.degree x) := by
    rw [hx] at W
    change w≤Graph189RootWidth.width b k (G.degree x) at W
    apply W.trans
    unfold Graph189RootWidth.width
    exact Nat.div_le_div_right (by change b≤n at order; omega)
  have paths (y : V) (hy : y∈C) : ∃j∈B,∃i,G.Adj x i ∧ G.Adj i j ∧ G.Adj j y ∧
      w≤(A∩G.neighborFinset j).card+(G.neighborFinset y∩G.neighborFinset i).card := by
    obtain ⟨j,dj,jy⟩ := Graph189MatchedRootWidth.predecessor (j:=2) (layerC y hy)
    obtain ⟨i,xi,ij⟩ := pred j (allB j dj)
    exact ⟨j,allB j dj,i,xi,ij,jy,linear.trans
      (Graph189MatchedRootWidth.geodesic_admissible hc xi ij jy (layerC y hy) point large (high y hy)).1⟩
  have width (y : V) (hy : y∈C) : w≤(A.filter (fun a => G.dist a y=2)).card+
        (B.filter (fun j => G.Adj j y)).card := by
    obtain ⟨j,_,i,xi,ij,jy,h⟩ := paths y hy
    exact h.trans (Graph189ColumnCancel.geodesic_cost hc x i j y B allB xi ij jy (layerC y hy))
  have pick (y : V) (hy : y∈C) : ∃j∈B,G.Adj j y ∧
      w≤(A∩G.neighborFinset j).card+(B.filter (fun j => G.Adj j y)).card := by
    obtain ⟨j,jb,i,xi,ij,jy,h⟩ := paths y hy
    refine ⟨j,jb,jy,h.trans (Nat.add_le_add_left (card_le_card ?_) _)⟩
    intro u hu
    obtain ⟨yu,iu⟩ := mem_inter.mp hu
    have uy := ((G.mem_neighborFinset _ _).mp yu).symm
    apply mem_filter.mpr ⟨allB u ?_,uy⟩
    have low := hc.dist_triangle (u:=x) (v:=u) (w:=y)
    have up := hc.dist_triangle (u:=x) (v:=i) (w:=u)
    rw [dist_eq_one_iff_adj.mpr uy,layerC y hy] at low
    rw [dist_eq_one_iff_adj.mpr xi,dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset _ _).mp iu)] at up
    omega
  have col (j : V) (jb : j∈B) : (C.filter (fun y => G.Adj j y)).card≤k := by
    obtain ⟨i,xi,ij⟩ := pred j jb
    have h := Graph189ColumnCancel.column hc x j i C large xi ij layerC (cp i)
    have l := card_le_card (filter_subset (fun a => G.dist a j≤2) (G.neighborFinset x))
    rw [G.card_neighborFinset_eq_degree] at l
    omega
  have row (i : V) (hi : i∈A) : (C.filter (fun y => G.dist i y=2)).card≤k := by
    have h := Graph189ColumnCancel.row_bound hc x i B C ((G.mem_neighborFinset _ _).mp hi) (top i) layerB layerC (cp i)
    omega
  have sum := Graph189RootDegreeSavings.budget hc x B C top large layerB pred layerC cp width
  have extra := Graph189RootDegreeSavings.charge hc x B C top cp layerC high allB pick col row fit (floor.trans_le order)
  have cmp := Nat.mul_le_mul_right B.card spend
  rw [hx] at cmp
  change m*B.card≤(G.degree x-k)*B.card at cmp
  let D := ∑a∈A,(G.degree x-G.degree a)
  change w*C.card+(G.degree x-k)*B.card+D≤k*G.degree x at sum
  change m*t*C.card≤k*(m*B.card+D) at extra
  have balance : w*C.card+(m*B.card+D)≤k*G.degree x := by omega
  have paid := Nat.mul_le_mul_left k balance
  have layer := Graph189HighThirdLayer.card_highThird_at_max hc cap x hx.symm
  have L : b-G.maxDegree-k-2≤C.card := (show b-G.maxDegree-k-2≤n-G.maxDegree-k-2 by dsimp [n]; omega).trans layer
  apply (Nat.mul_le_mul_left (k*w+m*t) L).trans
  rw [hx]
  change (k*w+m*t)*C.card≤k*(k*G.degree x)
  nlinarith only [paid,extra]

end Graph189PaidRootWidth
#print axioms Graph189PaidRootWidth.bound
