import Graph199Cut
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace Graph199
open SimpleGraph Finset

/-- A finite connected graph with no independent triple has a Hamiltonian path. -/
theorem hamiltonian_of_no_independent_triple {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : G.Connected)
    (hα : ∀ a b c : V, a ≠ b → a ≠ c → b ≠ c →
      ¬ G.Adj a b → ¬ G.Adj a c → ¬ G.Adj b c → False) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let T : Set ℕ := {n | ∃ a b : V, ∃ p : G.Walk a b, p.IsPath ∧ p.length = n}
  have hT : T.Finite := (Set.finite_le_nat (Fintype.card V)).subset (by
    rintro _ ⟨a,b,p,hp,rfl⟩
    exact hp.length_lt.le)
  let a₀ : V := Classical.choice hG.nonempty
  obtain ⟨n, hn, hmax₀⟩ := hT.exists_maximal
    ⟨0, a₀, a₀, Walk.nil, Walk.IsPath.nil, rfl⟩
  obtain ⟨a,b,p,hp,hpn⟩ := hn
  have hmax (a' b' : V) (p' : G.Walk a' b') (hp' : p'.IsPath) : p'.length ≤ p.length := by
    have h := hmax₀ ⟨a', b', p', hp', rfl⟩
    lia
  refine ⟨a, b, p, hp.isHamiltonian_of_mem ?_⟩
  intro x
  by_contra hx
  have nofirst (z : V) (hz : z ∉ p.support) : ¬ G.Adj a z := by
    intro he
    have h := hmax z b (p.cons he.symm) (hp.cons hz)
    simp at h
  have nolast (z : V) (hz : z ∉ p.support) : ¬ G.Adj b z := by
    intro he
    have h := hmax a z (p.concat he) (hp.concat hz he)
    simp at h
  have hs : p.support.toFinset ≠ univ := by
    intro he
    exact hx (List.mem_toFinset.mp (he ▸ mem_univ x))
  obtain ⟨z, hz, w, hw, hzw⟩ := hG.exists_adj_finset_compl
    (show p.support.toFinset.Nonempty from ⟨a, List.mem_toFinset.mpr p.start_mem_support⟩) hs
  have hzs : z ∉ p.support := fun hz' => hz (List.mem_toFinset.mpr hz')
  have hws : w ∈ p.support := List.mem_toFinset.mp hw
  have hab : a ≠ b := by
    intro he
    have hnil : p.Nil := hp.nil_iff_eq.mpr he
    have hw' : w = a := by simpa [Walk.nil_iff_support_eq.mp hnil] using hws
    exact nofirst z hzs (hw' ▸ hzw.symm)
  have hax : a ≠ x := fun h => hx (h ▸ p.start_mem_support)
  have hbx : b ≠ x := fun h => hx (h ▸ p.end_mem_support)
  have hab' : G.Adj a b := by
    by_contra he
    exact hα a b x hab hax hbx he (nofirst x hx) (nolast x hx)
  let c := p.concat hab'.symm
  have hcs : c.support = p.support ++ [a] := p.support_concat _
  have hcw : w ∈ c.support := by rw [hcs]; exact List.mem_append_left _ hws
  let r := c.rotate w hcw
  have hcnd : c.support.tail.Nodup := by
    apply (c.tail_support_perm_dropLast_support).nodup_iff.mpr
    rw [hcs, List.dropLast_append_cons, List.dropLast_singleton, List.append_nil]
    exact hp.support_nodup
  have hrnd : r.support.tail.Nodup := (c.support_rotate w hcw).perm.nodup_iff.mpr hcnd
  have hrnil : ¬ r.Nil := by
    rw [← Walk.length_eq_zero_iff, Walk.length_rotate, Walk.length_concat]
    omega
  have hrp : r.dropLast.IsPath := by
    apply Walk.IsPath.mk'
    rw [r.support_dropLast hrnil]
    exact r.tail_support_perm_dropLast_support.nodup_iff.mp hrnd
  have hzr : z ∉ r.dropLast.support := by
    intro h
    rw [r.support_dropLast hrnil] at h
    have hz' : z ∈ r.support := List.mem_of_mem_dropLast h
    rw [Walk.mem_support_rotate_iff, hcs, List.mem_append, List.mem_singleton] at hz'
    exact hz'.elim hzs (fun he => hzs (he.symm ▸ p.start_mem_support))
  have hlong := hmax z _ (r.dropLast.cons hzw) (hrp.cons hzr)
  rw [Walk.length_cons, Walk.length_dropLast_add_one hrnil] at hlong
  change (c.rotate w hcw).length ≤ p.length at hlong
  rw [Walk.length_rotate, Walk.length_concat] at hlong
  omega

/-- The independence-number-at-most-two case of Written on the Wall II #199. -/
theorem conjecture199_of_indepNum_le_two {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : G.Connected) (hα : G.indepNum ≤ 2) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  apply hamiltonian_of_no_independent_triple hG
  intro a b c hab hac hbc hna hnb hnc
  have hind : G.IsIndepSet ((↑({a,b,c} : Finset V)) : Set V) := by
    intro x hx y hy hne
    simp only [mem_coe, mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | exact hna | exact hnb | exact hnc | exact (fun h => hna h.symm)
            | exact (fun h => hnb h.symm) | exact (fun h => hnc h.symm) | contradiction
  have hc := hind.card_le_indepNum
  rw [card_insert_of_notMem (by simp [hab, hac]), card_insert_of_notMem (by simp [hbc]),
    card_singleton] at hc
  omega

#print axioms conjecture199_of_indepNum_le_two
#print axioms hamiltonian_of_no_independent_triple
end Graph199
