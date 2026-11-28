import Graph189LayerCover
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify

open SimpleGraph Finset
namespace Graph189LayerCutoff
variable {V : Type*} [Fintype V]

private theorem row_mono {a t k : ℕ} (hta : t ≤ a) (ha : 2*a ≤ k+1) :
    t*(k+1-t) ≤ a*(k+1-a) := by
  have ht : t ≤ k+1 := by omega
  have hak : a ≤ k+1 := by omega
  have hsum : a+t ≤ k+1 := by omega
  have h : 0 ≤ (a-t : ℤ) * ((k:ℤ)+1-a-t) :=
    mul_nonneg (by omega) (by omega)
  zify [ht, hak]
  nlinarith

theorem order_of_small_cover (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (z : V) (k : ℕ) (cap : ∀ v, G.distEven v ≤ k+1) (R : Finset V)
    (arms : ∀ a ∈ R, G.Adj z a)
    (covers : ∀ b ∈ Graph189LayerCover.layer G z 2, ∃ a ∈ R, G.Adj a b)
    (hs : 2*R.card ≤ k+1) :
    Fintype.card V ≤ 1+G.degree z+k+R.card*(k+1-R.card) := by
  obtain ⟨t, hta, _, horder⟩ := Graph189LayerCover.order_of_cover G hc z k cap R arms covers
  exact horder.trans (Nat.add_le_add_left (row_mono hta hs) _)

theorem order_of_small_degree (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (z : V) (k : ℕ) (cap : ∀ v, G.distEven v ≤ k+1) (hs : 2*G.degree z ≤ k+1) :
    Fintype.card V ≤ 1+G.degree z+k+G.degree z*(k+1-G.degree z) := by
  classical
  have covers : ∀ b ∈ Graph189LayerCover.layer G z 2, ∃ a ∈ G.neighborFinset z, G.Adj a b := by
    intro b hb
    have two := Graph189LayerCover.in_layer.mp hb
    obtain ⟨walk, hlen⟩ := (hc b z).exists_walk_length_eq_dist
    have hdist : G.dist b z = 2 := by rwa [dist_comm]
    rw [hdist] at hlen
    cases walk with
    | nil => simp at hlen
    | cons e walk =>
      rename_i a
      have hlen' : walk.length = 1 := by rw [Walk.length_cons] at hlen; omega
      have hle : G.dist z a ≤ 1 := by rw [dist_comm]; exact hlen' ▸ G.dist_le walk
      have had := e.diff_dist_adj (u := z)
      exact ⟨a, (G.mem_neighborFinset z a).mpr (dist_eq_one_iff_adj.mp (by omega)), e.symm⟩
  simpa only [G.card_neighborFinset_eq_degree] using
    (order_of_small_cover G hc z k cap (G.neighborFinset z)
      (fun a ha => (G.mem_neighborFinset z a).mp ha) covers (by simpa using hs))

end Graph189LayerCutoff
