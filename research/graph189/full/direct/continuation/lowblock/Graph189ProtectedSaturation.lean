import Graph189TraceableDeletionOrder
import Graph189ProtectedRigidity

open Finset SimpleGraph
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- On every longest path through z, if 3 deg(z)<k, the original degree
cap and a Hamilton path after deletion force equality for the contact count.
The strict order bound excludes an additional matched contact. -/
theorem protected_saturation_data (hc : G.Connected) (z : V)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (nontrace : ¬ ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian)
    {x y : {v : V | v ≠ z}} (p : (G.induce {v : V | v ≠ z}).Walk x y) (hp : p.IsHamiltonian)
    {a b : V} (Q : G.Walk a b) (hQ : Q.IsPath) (t : Fin Q.support.length) (eq : Q.support[t.val]=z)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z ∈ r.support → r.length ≤ Q.length)
    (pos : 3 ≤ G.degree z) (ratio : 3*G.degree z < G.secondSmallestDegree) :
    let s := G.degree z
    let k := G.secondSmallestDegree
    let m := (Q.support.toFinsetᶜ : Finset V).card
    m=k+1-s ∧ s<m ∧ Fintype.card V < (s+2)*m+(s+1) ∧
      ∀ v ∈ (Q.support.toFinsetᶜ : Finset V), s ≤ ((univ : Finset (Fin Q.support.length)).filter
        (fun i => G.Adj Q.support[i.val] v)).card := by
  classical
  let s := G.degree z
  let k := G.secondSmallestDegree
  let m := (Q.support.toFinsetᶜ : Finset V).card
  let u := k+1-m
  let n := Fintype.card V
  change 3 ≤ s at pos
  change 3*s < k at ratio
  change m=k+1-s ∧ s<m ∧ n < (s+2)*m+(s+1) ∧ _
  have upper := Graph189LayerCutoff.order_of_small_degree G hc z k cap (by change 2*s ≤ k+1; omega)
  have gap := protected_size_of_traceable_deletion z (by change 0 < s; omega) p hp Q hQ maximal
  change n ≤ 1+s+k+s*(k+1-s) at upper
  change 1+s+(s+1)*m ≤ n at gap
  have room : m+s ≤ k+1 := by
    by_contra! bad
    have cmp := Nat.mul_le_mul_left (s+1) (show (k+1-s)+1 ≤ m by omega)
    rw [Nat.mul_succ,Nat.succ_mul] at cmp
    omega
  have omits : (Q.support.toFinsetᶜ : Finset V).Nonempty := by
    by_contra empty
    apply nontrace
    refine ⟨a,b,Q,hQ.isHamiltonian_of_mem (fun v => ?_)⟩
    by_contra absent
    exact empty ⟨v,by simpa using absent⟩
  have max' : ∀ {i j}, ∀ r : G.Walk i j, r.IsPath → Q.support[t.val] ∈ r.support → r.length ≤ Q.length :=
    fun r hr h => maximal r hr (eq ▸ h)
  have low : G.degree Q.support[t.val] < k := by rw [eq]; change s < k; omega
  obtain ⟨um,bound,rows⟩ := protected_contact_witness Q hQ t max' low cap omits pos (by omega) room
  change u ≤ m at um
  change (u+1)*m+u ≤ n at bound
  have sum : m+u=k+1 := by dsimp [u]; omega
  have su : s ≤ u := by dsimp [u]; omega
  obtain ⟨us,me,sm,noextra⟩ := Graph189ProtectedRigidity.saturated pos ratio sum su um bound upper
  exact ⟨me,sm,noextra,fun v hv => us.ge.trans (rows v hv)⟩

#print axioms protected_saturation_data
end Graph189ExteriorGap
