import Graph189ProtectedMatching
import Graph189ProtectedHamiltonConnected
import Graph189DenseExteriorOrder

open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}

/-- The omitted vertices have enough distinct contacts to force this order.
The cardinal bound and neighbor estimates also detect the equality case. -/
theorem protected_contact_witness (p : G.Walk a b) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {x y}, ∀ q : G.Walk x y, q.IsPath → p.support[t.val] ∈ q.support → q.length ≤ p.length)
    (low : G.degree p.support[t.val] < G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (omits : (p.support.toFinsetᶜ : Finset V).Nonempty)
    {s : ℕ} (s3 : 3 ≤ s) (small : 2*s ≤ G.secondSmallestDegree)
    (room : (p.support.toFinsetᶜ : Finset V).card+s ≤ G.secondSmallestDegree+1) :
    let m := (p.support.toFinsetᶜ : Finset V).card
    let u := G.secondSmallestDegree+1-m
    u ≤ m ∧ (u+1)*m+u ≤ Fintype.card V ∧
      ∀ v ∈ (p.support.toFinsetᶜ : Finset V), u ≤ ((univ : Finset (Fin p.support.length)).filter
        (fun i => G.Adj p.support[i.val] v)).card := by
  classical
  let E := p.support.toFinsetᶜ
  let m := E.card
  let k := G.secondSmallestDegree
  let u := k+1-m
  change m+s ≤ k+1 at room
  change 2*s ≤ k at small
  obtain ⟨v,hv⟩ := omits
  let w : E := ⟨v,hv⟩
  have half := protected_exterior_minimum p hp t longest low cap w
  have upper := (G.induce (E : Set V)).degree_lt_card_verts w
  change (G.induce (E : Set V)).degree w < Fintype.card E at upper
  rw [Fintype.card_coe] at upper
  change _ < m at upper
  change k/2 ≤ (G.induce (E : Set V)).degree w at half
  have enough : u ≤ m := by dsimp [u]; omega
  have su : s ≤ u := by dsimp [u]; omega
  have sm : s ≤ m := by omega
  have sum : m+u=k+1 := by dsimp [u]; omega
  have outside {v : V} (hv : v ∈ E) : v ∉ p.support :=
    fun h => (mem_compl.mp hv) (List.mem_toFinset.mpr h)
  have boundary (w : V) (_ : w ∈ E) (v : V) (_ : G.Adj w v) (hv : v ∉ E) : v ∈ p.support := by
    simpa [E] using hv
  have rows (v : V) (hv : v ∈ E) : u ≤ ((univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] v)).card := by
    have ne : v ≠ p.support[t.val] := fun eq => outside hv (eq ▸ List.getElem_mem _)
    have high := (degree_pair (G:=G) v _ ne).resolve_right (not_le.mpr low)
    have d := Graph189DenseExteriorOrder.neighbors_on_path p E boundary hv
    change k ≤ G.degree v at high
    change G.degree v+1 ≤ m+_ at d
    omega
  have bound := protected_order_of_contacts p hp (List.getElem_mem (l:=p.support) t.isLt) longest E
    (by change 1 < m; omega) (fun _ hv => outside hv)
    (protected_exterior_hamilton_connected p hp t longest low cap (by change m+2 ≤ k; omega))
    (by omega : 0 < u) enough rows
  exact ⟨enough,bound,rows⟩

/-- For a longest path through the unique low vertex, an upper bound on the
number of omitted vertices already gives the structural order bound.  The
matching and all routes through the exterior follow from the original graph. -/
theorem protected_order_of_exterior_size (p : G.Walk a b) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {x y}, ∀ q : G.Walk x y, q.IsPath → p.support[t.val] ∈ q.support → q.length ≤ p.length)
    (low : G.degree p.support[t.val] < G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (omits : (p.support.toFinsetᶜ : Finset V).Nonempty)
    {s : ℕ} (s3 : 3 ≤ s) (small : 2*s ≤ G.secondSmallestDegree)
    (room : (p.support.toFinsetᶜ : Finset V).card+s ≤ G.secondSmallestDegree+1) :
    (s+1)*(G.secondSmallestDegree-s+2) ≤ Fintype.card V+1 := by
  let m := (p.support.toFinsetᶜ : Finset V).card
  let k := G.secondSmallestDegree
  let u := k+1-m
  obtain ⟨enough,bound,_⟩ := protected_contact_witness p hp t longest low cap omits s3 small room
  change m+s ≤ k+1 at room
  change 2*s ≤ k at small
  change u ≤ m at enough
  change (u+1)*m+u ≤ Fintype.card V at bound
  have su : s ≤ u := by dsimp [u]; omega
  have sm : s ≤ m := by omega
  have sum : m+u=k+1 := by dsimp [u]; omega
  change (s+1)*(k-s+2) ≤ Fintype.card V+1
  zify [show s ≤ k by omega] at bound sum ⊢
  have x : 0 ≤ (m:ℤ)-s := by omega
  have y : 0 ≤ (u:ℤ)-s := by omega
  nlinarith only [bound,mul_nonneg x y,sum,congrArg (fun i : ℤ => (s:ℤ)*i) sum]

#print axioms protected_contact_witness
#print axioms protected_order_of_exterior_size
end Graph189ExteriorGap
