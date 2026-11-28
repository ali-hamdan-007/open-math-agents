import Graph189LowMixedCut
import Mathlib.Tactic.Linarith

namespace Graph189EffectiveDeficit
open SimpleGraph Finset Graph189CutSides
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A genuine low vertex belongs to some minimum separating deletion. -/
def carriesLow : Prop :=
  ∃ A B S : Finset V, ∃ z : V, CutSides G A B S ∧ S.card=G.vertexConnectivity ∧
    z∈S ∧ G.degree z<G.secondSmallestDegree

noncomputable def effectiveDeficit : ℕ := by
  classical
  exact if carriesLow G then G.secondSmallestDegree-G.minDegree else 0

variable {G}

/-- All integer witnesses required for the scalar deficit branch arise on
one actual minimum separator, oriented with the smaller population first. -/
theorem low_witnesses (hc : G.Connected) (cap : ∀ v, G.distEven v≤1+G.secondSmallestDegree)
    (hs : 5≤G.vertexConnectivity) (hk : 3*G.vertexConnectivity<G.secondSmallestDegree) :
    let k : ℤ := G.secondSmallestDegree
    let n : ℤ := Fintype.card V
    let s : ℤ := G.vertexConnectivity
    let e : ℤ := (G.maxDegree-G.secondSmallestDegree : ℕ)
    let d : ℤ := effectiveDeficit G
    0<d → ∃ r x y : ℤ, r≤s ∧ d≤r-1 ∧ 0≤x ∧ x≤y ∧ x+y=n-s ∧
      x*(y-k)≤s*k*k ∧ k*d≤2*k+(k+1)*r-n ∧
      (r-1)*(k-s+1)≤(s+1)*k-n+x+s+r*(e+s-1) := by
  classical
  dsimp only
  intro hpos
  by_cases has : carriesLow G
  · have hchoice : effectiveDeficit G=G.secondSmallestDegree-G.minDegree := by simp [effectiveDeficit,has]
    obtain ⟨A,B,S,z,sides,sz,hz,low⟩ := has
    have zmin : G.degree z=G.minDegree := by
      obtain ⟨u,hu⟩ := G.exists_minimal_degree_vertex
      by_cases eu : u=z
      · subst u
        exact hu.symm
      · have h' := (degree_pair (G:=G) u z eu).resolve_right (not_le.mpr low)
        have hm := G.minDegree_le_degree z
        omega
    have defeq : effectiveDeficit G=G.secondSmallestDegree-G.degree z := by
      simpa only [zmin] using hchoice
    rw [defeq]
    have smaller (T : Finset V) (ht : T.card<S.card) :
        (G.induce {v : V | v∉T}).Connected :=
      connected_after_smaller_deletion T (by omega)
    let k := G.secondSmallestDegree
    let n := Fintype.card V
    let s := G.vertexConnectivity
    let e := G.maxDegree-k
    let d := k-G.degree z
    have oriented {U W : Finset V} (cuts : CutSides G U W S) (small : U.card≤W.card) :
        ∃ r x y : ℤ, r≤(s:ℤ) ∧ (d:ℤ)≤r-1 ∧ 0≤x ∧ x≤y ∧ x+y=(n:ℤ)-s ∧
          x*(y-k)≤(s:ℤ)*k*k ∧ (k:ℤ)*d≤2*(k:ℤ)+(k+1:ℤ)*r-n ∧
          (r-1)*((k:ℤ)-s+1)≤(s+1:ℤ)*k-n+x+s+r*((e:ℤ)+s-1) := by
      obtain ⟨_,_,_,_,_,_,r,_,rpos,rmax,dfloor,debit,mixed⟩ :=
        cuts.low_cut_three_bounds hc smaller cap hz low
      obtain ⟨total,cross⟩ := cuts.low_cut_product hc smaller cap hz low
      rw [sz] at rmax total cross mixed
      change n=s+U.card+W.card at total
      change U.card*W.card≤U.card*k+s*(k*k) at cross
      change n+k*d≤2*k+(k+1)*r at debit
      change n+(r-1)*(k+1-s)≤(s+1)*k+U.card+s+r*(e+s-1) at mixed
      change d+1≤r at dfloor
      have totalZ : (n:ℤ)=s+U.card+W.card := by exact_mod_cast total
      have crossZ : (U.card:ℤ)*W.card≤(U.card:ℤ)*k+(s:ℤ)*(k*k) := by exact_mod_cast cross
      have debitZ : (n:ℤ)+(k:ℤ)*d≤2*(k:ℤ)+(k+1:ℤ)*r := by exact_mod_cast debit
      have mixedZ : (n:ℤ)+((r-1:ℕ):ℤ)*((k+1-s:ℕ):ℤ)≤
          (s+1:ℤ)*k+U.card+s+(r:ℤ)*((e+s-1:ℕ):ℤ) := by exact_mod_cast mixed
      have hsk : s≤k+1 := by change G.vertexConnectivity≤G.secondSmallestDegree+1; omega
      have hes : 1≤e+s := by change 1≤e+G.vertexConnectivity; omega
      rw [Nat.cast_sub rpos,Nat.cast_sub hsk,Nat.cast_sub hes] at mixedZ
      push_cast at mixedZ
      refine ⟨r,U.card,W.card,by exact_mod_cast rmax,?_,by positivity,by exact_mod_cast small,
        by omega,by nlinarith only [crossZ],by linarith only [debitZ],by nlinarith only [mixedZ]⟩
      have hdZ : (d:ℤ)+1≤r := by exact_mod_cast dfloor
      omega
    rcases le_total A.card B.card with ha|hb
    · exact oriented sides ha
    · exact oriented sides.swap hb
  · simp [effectiveDeficit,has] at hpos

end Graph189EffectiveDeficit
#print axioms Graph189EffectiveDeficit.low_witnesses
