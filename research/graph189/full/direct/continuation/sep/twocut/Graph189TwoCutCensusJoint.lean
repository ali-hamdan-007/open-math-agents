import Graph189PositiveEvenCut

namespace Graph189TwoCutCensusArithmetic

/-- The common-free-side census leaves room for the apex route and the one
unused separator vertex. The flag j indicates a common port in B. -/
theorem common_free {k a b w l la t j : ℕ} (large : 7≤k) (big : 2*k≤b)
    (smallLower : k≤a) (low : l+la≤1) (flag : j≤1) (commonDebit : j≤t)
    (privateRows : b+2+t≤2*k+w+l)
    (anchorRows : a+2*w+2*j≤2*k+la) :
    a+la≤2*k-2 ∧ b+la+1≤(2*k-1-2*j)+(k+1)/2+1 := by
  constructor
  · omega
  · omega

/-- Bounds on the side orders from the two private rows, both anchor rows,
and the common ports in the nonadjacent-anchor case. -/
theorem both_private {k a b c w v t l la lb : ℕ}
    (big : 2*k≤b) (low : la+lb≤1) (lowNonport : l≤lb)
    (twoTypes : c+2≤a) (aPorts : a+c≤2*k+la)
    (bPorts : b≤k+v+w+lb)
    (privateRows : b+2+t≤2*k+w+l)
    (anchorRows : a+v+2*w+2≤2*k+c+la) :
    2*a+t+2≤3*k ∧ 2*b+t+6≤5*k+la+lb+l := by
  constructor <;> omega

/-- In all orders from degree seven, the apex path and the Dirac or Ore side
path leave at most the original graph's allowed omissions. -/
theorem both_private_omissions {k b t l la lb miss : ℕ} (k7 : 7≤k) (big : 2*k≤b)
    (low : la+lb≤1) (lowNonport : l≤lb)
    (bound : 2*b+t+6≤5*k+la+lb+l) (missLe : miss≤la)
    (whole : 9≤k ∨ (8≤k ∧ 1≤t) → miss=0) :
    b+miss+1≤(if t=0 then 2*k-1 else 2*k-3)+(k+1)/2+1 := by
  by_cases empty : t=0
  · rw [if_pos empty]
    by_cases high : 9≤k
    · have := whole (Or.inl high)
      omega
    · omega
  · rw [if_neg empty]
    by_cases high : 8≤k
    · have := whole (Or.inr ⟨high,by omega⟩)
      omega
    · omega

#print axioms common_free
#print axioms both_private
#print axioms both_private_omissions
end Graph189TwoCutCensusArithmetic

namespace Graph189TwoCutParity
open Finset SimpleGraph Graph189PositiveEvenCut
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable {A B : Finset V} {p q x z : V}

/-- A common port and a vertex two steps from both anchors see opposite
parities across the cut. The latter also reserves two places for the anchors. -/
theorem complementary_rows (hc : G.Connected)
    (sides : Graph189CutSides.CutSides G A B {p,q}) (diff : p≠q)
    (xA : x∈A) (zA : z∈A) (xp : G.dist x p=1) (xq : G.dist x q=1)
    (zp : G.dist z p=2) (zq : G.dist z q=2)
    {k : ℕ} (xcap : G.distEven x≤k+1) (zcap : G.distEven z≤k+1) :
    B.card+2≤2*k := by
  classical
  let X := B.filter (fun y => Even (G.dist x y))
  let Z := B.filter (fun y => Even (G.dist z y))
  have opposite (y : V) (yb : y∈B) : G.dist z y=G.dist x y+1 := by
    obtain ⟨i,hi,xi⟩ := separator_distance hc sides xA yb
    obtain ⟨j,hj,zj⟩ := separator_distance hc sides zA yb
    have xAnchor (a : V) (ha : a∈({p,q}:Finset V)) : G.dist x a=1 := by
      rcases (show a=p ∨ a=q by simpa using ha) with rfl|rfl <;> assumption
    have zAnchor (a : V) (ha : a∈({p,q}:Finset V)) : G.dist z a=2 := by
      rcases (show a=p ∨ a=q by simpa using ha) with rfl|rfl <;> assumption
    have upper := hc.dist_triangle (u:=z) (v:=i) (w:=y)
    have lower := hc.dist_triangle (u:=x) (v:=j) (w:=y)
    rw [xAnchor i hi] at xi
    rw [zAnchor j hj] at zj
    rw [zAnchor i hi] at upper
    rw [xAnchor j hj] at lower
    omega
  have cover : B⊆X∪Z := by
    intro y yb
    by_cases ex : Even (G.dist x y)
    · exact mem_union_left _ (mem_filter.mpr ⟨yb,ex⟩)
    have ez : Even (G.dist z y) := by
      rw [Nat.even_iff] at ex ⊢
      have := opposite y yb
      omega
    exact mem_union_right _ (mem_filter.mpr ⟨yb,ez⟩)
  have rowX : X⊆evenOthers G x := by
    intro y hy
    obtain ⟨yb,xe⟩ := mem_filter.mp hy
    exact mem_even_others (fun eq => disjoint_left.mp sides.apart xA (eq ▸ yb)) xe
  have rowZ : Z⊆evenOthers G z := by
    intro y hy
    obtain ⟨yb,ze⟩ := mem_filter.mp hy
    exact mem_even_others (fun eq => disjoint_left.mp sides.apart zA (eq ▸ yb)) ze
  have ps : p∈({p,q}:Finset V) := by simp
  have qs : q∈({p,q}:Finset V) := by simp
  have pe : p∈evenOthers G z :=
    mem_even_others (fun eq => disjoint_left.mp sides.left_cut (eq.symm ▸ zA) ps)
      (by rw [zp]; exact ⟨1,rfl⟩)
  have qe : q∈evenOthers G z :=
    mem_even_others (fun eq => disjoint_left.mp sides.left_cut (eq.symm ▸ zA) qs)
      (by rw [zq]; exact ⟨1,rfl⟩)
  have np : p∉Z := fun hp => disjoint_left.mp sides.right_cut (mem_filter.mp hp).1 ps
  have nq : q∉insert p Z := by
    intro h
    rcases mem_insert.mp h with eq|h
    · exact diff eq.symm
    · exact disjoint_left.mp sides.right_cut (mem_filter.mp h).1 qs
  have add : insert q (insert p Z)⊆evenOthers G z := by
    intro v hv
    rcases mem_insert.mp hv with rfl|hv
    · exact qe
    rcases mem_insert.mp hv with rfl|hv
    · exact pe
    · exact rowZ hv
  have kX := (card_le_card rowX).trans (even_others_card xcap)
  have kZ := (card_le_card add).trans (even_others_card zcap)
  rw [card_insert_of_notMem nq,card_insert_of_notMem np] at kZ
  have total := (card_le_card cover).trans (card_union_le X Z)
  omega

#print axioms complementary_rows
end Graph189TwoCutParity
