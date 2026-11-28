import Graph189TwofoldCover

open Finset SimpleGraph
namespace Graph189PrivateRepresentativeBound
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B S : Finset V} {p q : V}

/-- The two possible crossing vertices give the exact ambient distance,
including when deletion of the separator leaves multiple components in B. -/
theorem cross_dist (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (pair : S={p,q}) {x y : V} (xa : x∈A) (yb : y∈B) :
    G.dist x y=min (G.dist x p+G.dist p y) (G.dist x q+G.dist q y) := by
  apply le_antisymm (le_min (hc.dist_triangle (v:=p)) (hc.dist_triangle (v:=q)))
  obtain ⟨w,len⟩ := (hc x y).exists_walk_length_eq_dist
  obtain ⟨i,si,hit⟩ := sides.meets xa yb w
  have sum := congrArg Walk.length (Walk.take_spec w hit)
  rw [Walk.length_append,len] at sum
  have lower := G.dist_le (w.takeUntil i hit)
  have upper := G.dist_le (w.dropUntil i hit)
  have cost : G.dist x i+G.dist i y≤G.dist x y := by omega
  rcases (show i=p ∨ i=q by simpa only [pair,mem_insert,mem_singleton] using si) with rfl|rfl
  · exact (min_le_left _ _).trans cost
  · exact (min_le_right _ _).trans cost

private theorem weights (a b : ℕ) (ha : 1≤a) (hb : 1≤b) :
    1+(if a=1 ∧ b=1 then 1 else 0) ≤
      (if Even (min (1+a) (2+b)) then 1 else 0)+
      (if Even (min (2+a) (1+b)) then 1 else 0)+
      (if a=2 ∧ b=2 then 1 else 0)+(if 3≤a ∧ 3≤b then 1 else 0) := by
  simp only [Nat.even_iff]
  split_ifs <;> omega

private theorem quota (cap : ∀v,G.distEven v≤G.secondSmallestDegree+1)
    (sides : Graph189CutSides.CutSides G A B S) {x c : V}
    (xa : x∈A) (cs : c∈S) (ed : G.dist x c=2) :
    (B.filter (fun y => Even (G.dist x y))).card+1≤G.secondSmallestDegree := by
  classical
  let T := B.filter (fun y => Even (G.dist x y))
  have no : c∉T := fun h => Finset.disjoint_left.mp sides.right_cut (mem_filter.mp h).1 cs
  have self : x∉insert c T := by
    intro h
    rcases mem_insert.mp h with rfl|hx
    · exact Finset.disjoint_left.mp sides.left_cut xa cs
    · exact Finset.disjoint_left.mp sides.apart xa (mem_filter.mp hx).1
  have bound := Graph189TwofoldCover.outside_quota cap (insert c T) self
  rw [filter_eq_self.mpr (by
    intro w hw
    rcases mem_insert.mp hw with rfl|hw
    · simp [ed]
    · exact (mem_filter.mp hw).2),card_insert_of_notMem no] at bound
  exact bound

/-- The private-representative bound from the local counts paragraph of
unrestricted-two-cuts.md. A common port costs an additional incidence;
the two uncharged classes are nonports at depth two from both anchors
and vertices at depth at least three from both. -/
theorem order (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (pair : S={p,q}) (cap : ∀v,G.distEven v≤G.secondSmallestDegree+1)
    {u v : V} (ua : u∈A) (up : G.dist u p=1) (uq : G.dist u q=2)
    (va : v∈A) (vp : G.dist v p=2) (vq : G.dist v q=1) :
    B.card+(B.filter (fun y => G.dist p y=1 ∧ G.dist q y=1)).card+2 ≤
      2*G.secondSmallestDegree+(B.filter (fun y => G.dist p y=2 ∧ G.dist q y=2)).card+
      (B.filter (fun y => 3≤G.dist p y ∧ 3≤G.dist q y)).card := by
  classical
  have ps : p∈S := by simp [pair]
  have qs : q∈S := by simp [pair]
  have pos (i : V) (si : i∈S) (y : V) (yb : y∈B) : 1≤G.dist i y := by
    have diff : G.dist i y≠0 := fun eq => Finset.disjoint_left.mp sides.right_cut yb
      ((hc.dist_eq_zero_iff.mp eq) ▸ si)
    omega
  have unit (y : V) (yb : y∈B) := weights (G.dist p y) (G.dist q y) (pos p ps y yb) (pos q qs y yb)
  have atY (y : V) (yb : y∈B) :
      1+(if G.dist p y=1 ∧ G.dist q y=1 then 1 else 0) ≤
        (if Even (G.dist u y) then 1 else 0)+(if Even (G.dist v y) then 1 else 0)+
        (if G.dist p y=2 ∧ G.dist q y=2 then 1 else 0)+(if 3≤G.dist p y ∧ 3≤G.dist q y then 1 else 0) := by
    rw [cross_dist hc sides pair ua yb,cross_dist hc sides pair va yb,up,uq,vp,vq]
    exact unit y yb
  have total := Finset.sum_le_sum atY
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.sum_boole,smul_eq_mul,mul_one,Nat.cast_id] at total
  have U := quota cap sides ua qs uq
  have W := quota cap sides va ps vp
  omega

#print axioms order
end Graph189PrivateRepresentativeBound
