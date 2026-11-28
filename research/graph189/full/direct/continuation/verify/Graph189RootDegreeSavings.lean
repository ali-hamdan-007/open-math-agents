import Graph189SecondLayerBudget
import Graph189RetainedWidth

open Finset SimpleGraph
namespace Graph189RootDegreeSavings
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem flip (A B : Finset V) (r : V → V → Prop) [DecidableRel r] :
    (∑ a∈A,(B.filter (fun b => r a b)).card)=∑ b∈B,(A.filter (fun a => r a b)).card := by
  simp only [card_eq_sum_ones,sum_filter]
  exact sum_comm

/-- The cancelled row and column inequalities retain the shortfall in each
first neighbor's degree and one maximum-degree excess per second-layer vertex. -/
theorem budget (hc : G.Connected) (x : V) (B C : Finset V) {k w : ℕ}
    (maxd : ∀a,G.degree a≤G.degree x) (large : k≤G.degree x)
    (hB : ∀b∈B,G.dist x b=2) (pred : ∀b∈B,∃i,G.Adj x i ∧ G.Adj i b)
    (hC : ∀y∈C,G.dist x y=3) (cap : ∀a,G.distEven a≤k+1)
    (width : ∀y∈C,w≤((G.neighborFinset x).filter (fun a => G.dist a y=2)).card+
      (B.filter (fun b => G.Adj b y)).card) :
    w*C.card + (G.degree x-k)*B.card + (∑a∈G.neighborFinset x,(G.degree x-G.degree a))≤k*G.degree x := by
  classical
  let A := G.neighborFinset x
  have row (a : V) (ha : a∈A) := Graph189ColumnCancel.row_bound_with_deficit hc x a B C
    ((G.mem_neighborFinset _ _).mp ha) (maxd a) hB hC (cap a)
  have col (b : V) (hb : b∈B) :
      (C.filter (fun y => G.Adj b y)).card+(G.degree x-k)≤(A.filter (fun a => G.dist a b≤2)).card := by
    obtain ⟨i,hi,hb'⟩ := pred b hb
    exact Graph189ColumnCancel.column hc x b i C large hi hb' hC (cap i)
  have wr := sum_le_sum width
  have rr := sum_le_sum row
  have cr := sum_le_sum col
  simp only [sum_add_distrib,sum_const,smul_eq_mul] at wr rr cr
  rw [←flip A C (fun a y => G.dist a y=2),←flip B C G.Adj] at wr
  rw [←flip A B (fun a b => G.dist a b≤2)] at cr
  have finish : C.card*w+B.card*(G.degree x-k)+(∑a∈A,(G.degree x-G.degree a))≤A.card*k := by omega
  simpa only [A,G.card_neighborFinset_eq_degree,Nat.mul_comm] using finish


private theorem target_wedge (hc : G.Connected) {i j y x : V} {k : ℕ}
    (ji : G.Adj j i) (jy : G.Adj j y) (iy : i≠y) (miss : ¬G.Adj i y)
    (top : ∀a,G.degree a≤G.degree x) (high : k≤G.degree y) (cap : ∀a,G.distEven a≤k+1) :
    Fintype.card V≤2*k+(k+1)*(G.neighborFinset i∩G.neighborFinset y).card+
      k*(G.degree x-G.degree i) := by
  have wedge := Graph189WedgeOrder.wedge_order hc ji jy miss cap
  have union := Nat.mul_le_mul_left (k+1) (Graph189RetainedWidth.union_lower ji jy iy miss)
  have even := Nat.mul_le_mul_left k (cap j)
  have max := Nat.mul_le_mul_left k (top j)
  have dy := Nat.mul_le_mul_left k high
  have id := congrArg (fun u : ℕ => k*u) (Nat.sub_add_cancel (top i))
  nlinarith only [wedge,union,even,max,dy,id]

/-- The second wedge at every predecessor charges missing second neighbors
of a target to degree shortfalls of distinct first neighbors. -/
theorem charge (hc : G.Connected) (x : V) (B C : Finset V) {k w m t : ℕ}
    (top : ∀a,G.degree a≤G.degree x) (cap : ∀a,G.distEven a≤k+1)
    (hC : ∀y∈C,G.dist x y=3) (high : ∀y∈C,k≤G.degree y)
    (allB : ∀b,G.dist x b=2 → b∈B)
    (pick : ∀y∈C,∃j∈B,G.Adj j y ∧
      w≤(G.neighborFinset x∩G.neighborFinset j).card+(B.filter (fun b => G.Adj b y)).card)
    (col : ∀b∈B,(C.filter (fun y => G.Adj b y)).card≤k)
    (row : ∀a∈G.neighborFinset x,(C.filter (fun y => G.dist a y=2)).card≤k)
    (space : m+t≤w+1) (floor : 2*k+(k+1)*(t-1)<Fintype.card V) :
    m*t*C.card≤k*(m*B.card+(∑a∈G.neighborFinset x,(G.degree x-G.degree a))) := by
  classical
  let A := G.neighborFinset x
  let d (a : V) := G.degree x-G.degree a
  let q (y : V) := (B.filter (fun b => G.Adj b y)).card
  let D (y : V) := A.filter (fun a => G.dist a y=2)
  have charge (y : V) (hy : y∈C) : m*t≤m*q y+∑a∈D y,d a := by
    by_cases sat : t≤q y
    · exact (Nat.mul_le_mul_left m sat).trans (Nat.le_add_right _ _)
    obtain ⟨j,_,jy,width⟩ := pick y hy
    let H := G.neighborFinset x∩G.neighborFinset j
    change w≤H.card+q y at width
    have hxy := hC y hy
    have sub : H⊆D y := by
      intro i hi
      obtain ⟨xi,ji⟩ := mem_inter.mp hi
      refine mem_filter.mpr ⟨xi,?_⟩
      have low := hc.dist_triangle (u:=x) (v:=i) (w:=y)
      have up := hc.dist_triangle (u:=i) (v:=j) (w:=y)
      rw [dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset _ _).mp xi)] at low
      rw [dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset _ _).mp ji).symm,dist_eq_one_iff_adj.mpr jy] at up
      omega
    have short (i : V) (hi : i∈H) : t-q y≤d i := by
      have ii := (mem_filter.mp (sub hi)).2
      obtain ⟨xi,ji⟩ := mem_inter.mp hi
      have wedge := target_wedge hc ((G.mem_neighborFinset _ _).mp ji) jy
        (fun eq => by rw [eq,dist_self] at ii; contradiction)
        (fun h => by rw [dist_eq_one_iff_adj.mpr h] at ii; contradiction) top (high y hy) cap
      have common : G.neighborFinset i∩G.neighborFinset y⊆B.filter (fun b => G.Adj b y) := by
        intro b hb
        obtain ⟨ib,yb⟩ := mem_inter.mp hb
        have by' := ((G.mem_neighborFinset _ _).mp yb).symm
        apply mem_filter.mpr ⟨allB b ?_,by'⟩
        have low := hc.dist_triangle (u:=x) (v:=b) (w:=y)
        have up := hc.dist_triangle (u:=x) (v:=i) (w:=b)
        rw [dist_eq_one_iff_adj.mpr by'] at low
        rw [dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset _ _).mp xi),dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset _ _).mp ib)] at up
        omega
      have cmp := Nat.mul_le_mul_left (k+1) (card_le_card common)
      change _≤(k+1)*q y at cmp
      change _≤2*k+_+k*d i at wedge
      by_contra! fail
      have mul := Nat.mul_le_mul_left (k+1) (show q y+d i≤t-1 by omega)
      nlinarith only [mul,wedge,floor,cmp,Nat.zero_le (d i)]
    have bound := sum_le_sum short
    simp only [sum_const,smul_eq_mul] at bound
    have subset := sum_le_sum_of_subset_of_nonneg sub (fun a _ _ => Nat.zero_le (d a))
    have many := Nat.mul_le_mul_right (t-q y) (show m≤H.card by omega)
    have eq := congrArg (fun u : ℕ => m*u) (Nat.sub_add_cancel (by omega : q y≤t))
    nlinarith only [many,bound,subset,eq]
  have totals := sum_le_sum charge
  simp only [sum_const,smul_eq_mul,sum_add_distrib,←mul_sum] at totals
  have qtotal : (∑y∈C,q y)≤B.card*k := by
    have h := sum_le_sum col
    simp only [sum_const,smul_eq_mul] at h
    rwa [flip B C G.Adj] at h
  have colD (a : V) (ha : a∈A) : (C.filter (fun y => G.dist a y=2)).card*d a≤k*d a :=
    Nat.mul_le_mul_right _ (row a ha)
  have dtotal := sum_le_sum colD
  rw [←mul_sum] at dtotal
  have ex : (∑y∈C,∑a∈D y,d a)=∑a∈A,(C.filter (fun y => G.dist a y=2)).card*d a := by
    simp only [D,sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    rw [←sum_filter,sum_const,smul_eq_mul]
  rw [ex] at totals
  have mQ := Nat.mul_le_mul_left m qtotal
  change m*t*C.card≤k*(m*B.card+∑a∈A,d a)
  nlinarith only [totals,mQ,dtotal]

end Graph189RootDegreeSavings
#print axioms Graph189RootDegreeSavings.budget
#print axioms Graph189RootDegreeSavings.charge
