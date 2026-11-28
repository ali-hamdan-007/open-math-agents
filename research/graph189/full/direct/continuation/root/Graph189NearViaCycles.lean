import Graph189StructuralConclusion
import Graph189MinimumOrderViaCycles

namespace Graph189NearViaCycles
open Finset SimpleGraph Graph189EffectiveDeficit Graph189ExteriorDegreeCycle Graph189UniversalCycle
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem signed_order {l f n : ℕ} (lf : l≤f)
    (h : (l+1)*(f-l+2)-1≤n) : ((l:ℤ)+1)*((f:ℤ)-l+2)-1≤n := by
  have raw : (l+1)*(f-l+2)≤n+1 := by omega
  have cast : ((l:ℤ)+1)*((↑(f-l) : ℤ)+2)≤(n:ℤ)+1 := by exact_mod_cast raw
  rw [Nat.cast_sub lf] at cast
  omega

/-- Only the classical cycle-exclusion statement remains as a graph input to
near traceability in the structural range. Either the graph is traceable or
the deletion of a minimum-degree vertex is traceable. -/
theorem traceable_or_minimum_deletion (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (hs : 5≤G.vertexConnectivity) (hk : 26≤G.secondSmallestDegree)
    (ratio : 3*G.vertexConnectivity<G.secondSmallestDegree)
    (cycle : ∀ w : V, exteriorCycleExclusion (completeAt G w) G.vertexConnectivity ∧
      exteriorCycleExclusion (completeAt G w) (G.vertexConnectivity+1)) :
    (∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian) ∨
    ∃ z : V, G.degree z=G.minDegree ∧
      ∃ a b, ∃ p : (G.induce {v : V | v≠z}).Walk a b, p.IsHamiltonian := by
  classical
  let s := G.vertexConnectivity
  let k := G.secondSmallestDegree
  let f := G.minDegree
  let n := Fintype.card V
  let d := effectiveDeficit G
  have hsN : 5≤s := hs
  have hkN : 26≤k := hk
  have sr : 3*s<k := ratio
  obtain ⟨w,wm⟩ := G.exists_minimal_degree_vertex
  have minw : G.degree w=G.minDegree := wm.symm
  have maxk := (secondDegree_le_completeAt_minDegree (G:=G) w minw).trans
    ((completeAt G w).minDegree_le_degree w)
  rw [completeAt_degree_self] at maxk
  have room : s<n-1 := by change k≤n-1 at maxk; omega
  have deletion (z : V) : (G.induce {v : V | v≠z}).Connected := by
    have equal : {v : V | v∉({z} : Finset V)} = {v : V | v≠z} := by
      ext v
      simp only [Set.mem_ofPred_eq,Finset.mem_singleton]
    rw [← equal]
    exact Graph189CutSides.connected_after_smaller_deletion (G:=G) ({z} : Finset V)
      (by simp; omega : ({z} : Finset V).card<G.vertexConnectivity)
  have point (v : V) : G.distEven v≤k+1 := by
    have h := (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
    change _≤1+k at h
    omega
  by_cases trace : ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian
  · exact Or.inl trace
  by_cases H : ∃ a b, ∃ p : (G.induce {v : V | v≠w}).Walk a b, p.IsHamiltonian
  · exact Or.inr ⟨w,minw,H⟩
  left
  apply Graph189StructuralConclusion.traceable_of_structural_lower_bounds hc cap deletion hs hk ratio
  · have h := minimum_order_of_cycle_exclusion w minw trace H point (by omega)
        (completeAt_connectivity (G:=G) w) (by change s≤(k+1)/2; omega) (cycle w).1
    exact signed_order (by change s≤k; omega) h
  · change 3*(s:ℤ)<2*((k:ℤ)-d-1) → 2*(s:ℤ)≤(k:ℤ)-2*d-2 →
        4*(n:ℤ)<(k:ℤ)*(k-1) → ((s:ℤ)+2)*((k:ℤ)-d-s+1)-1≤n
    intro critical enough _
    by_cases matchLow : (k:ℤ)-d≤f
    · have c : 3*G.vertexConnectivity<2*(G.minDegree+1) := by change 3*s<2*(f+1); omega
      have e : G.secondSmallestDegree+2*G.vertexConnectivity+2≤2*G.minDegree := by
        change k+2*s+2≤2*f; omega
      have h := critical_order_of_cycle_exclusion trace (by omega) point (by omega) room c e
        (fun z => (cycle z).2)
      have lifted := signed_order (by change s+1≤f; omega) h
      change ((↑(s+1) : ℤ)+1)*((f:ℤ)-↑(s+1)+2)-1≤n at lifted
      push_cast at lifted
      have cmp := mul_le_mul_of_nonneg_left matchLow (show 0≤(s:ℤ)+2 by positivity)
      nlinarith only [lifted,cmp]
    · have low : f<k := by omega
      have absent : ¬carriesLow G := by
        intro witness
        have hd : d=k-f := by simp [d,effectiveDeficit,witness,k,f]
        omega
      have dz : d=0 := by simp [d,effectiveDeficit,absent]
      have free (T : Finset V) (sz : T.card=G.vertexConnectivity) (wt : w∈T) :
          (G.induce {v : V | v∉T}).Connected := by
        by_contra bad
        have survives : ∃ v, v∉T := by
          by_contra! all
          have eq := eq_univ_iff_forall.mpr all
          rw [eq,card_univ] at sz
          change s<n-1 at room
          change n=s at sz
          omega
        obtain ⟨A,B,sides⟩ := Graph189CutSides.exists_cutSides_of_disconnected T survives bad
        exact absent ⟨A,B,T,w,sides,sz,wt,by rw [minw]; exact low⟩
      have conn := completeAt_connectivity_add_one w room free
      have h := minimum_order_of_cycle_exclusion w minw trace H point (by omega) conn
        (by change s+1≤(k+1)/2; omega) (cycle w).2
      have lifted := signed_order (by change s+1≤k; omega) h
      change ((↑(s+1) : ℤ)+1)*((k:ℤ)-↑(s+1)+2)-1≤n at lifted
      push_cast at lifted
      rw [dz]
      push_cast
      nlinarith only [lifted]

#print axioms traceable_or_minimum_deletion
end Graph189NearViaCycles
