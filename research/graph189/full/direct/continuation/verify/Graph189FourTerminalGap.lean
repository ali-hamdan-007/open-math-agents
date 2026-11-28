import Graph189ExteriorDegree
import Graph189R1Metric

open SimpleGraph Finset
namespace Graph189FourTerminalGap
open Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {a b : V}

/-- An unmarked three-vertex interval charged through a common neighbor
contradicts the four-witness quota for an exterior vertex with two marks.
The interval may be a tail or an interior gap. -/
theorem impossible_of_exact (p : G.Walk a b) (hp : p.IsPath) {x : V} (outside : x ∉ p.support)
    {i j lo hi : ℕ} (left : 0 < i) (spaced : i+2 ≤ j) (right : j+1 < p.support.length)
    (marks : contactPositions p x = {i,j})
    (bound : hi ≤ p.support.length) (size : lo+3=hi)
    (unmarked : ∀ h ∈ Ico lo hi, h ≠ i ∧ h ≠ j)
    (via : ∀ h ∈ Ico lo hi, ∃ w, G.Adj x w ∧ G.Adj (p.getVert h) w)
    (quota : (univ.filter (fun y => G.dist x y=2)).card ≤ 4) : False := by
  classical
  let J := Ico lo hi
  let W : Finset ℕ := {i-1,i+1,j-1,j+1}
  have skipI : ¬(lo ≤ i ∧ i < hi) := fun h => (unmarked i (mem_Ico.mpr h)).1 rfl
  have skipJ : ¬(lo ≤ j ∧ j < hi) := fun h => (unmarked j (mem_Ico.mpr h)).2 rfl
  have pair : ∃ u ∈ W, ∃ v ∈ W, u≠v ∧ u∉J ∧ v∉J := by
    by_cases before : hi ≤ i
    · refine ⟨j-1,by simp [W],j+1,by simp [W],by omega,?_,?_⟩ <;> simp [J] <;> omega
    by_cases after : j < lo
    · refine ⟨i-1,by simp [W],i+1,by simp [W],by omega,?_,?_⟩ <;> simp [J] <;> omega
    refine ⟨i-1,by simp [W],j+1,by simp [W],by omega,?_,?_⟩ <;> simp [J] <;> omega
  obtain ⟨u,hu,v,hv,ne,uout,vout⟩ := pair
  have mark {h : ℕ} (m : h=i ∨ h=j) : G.Adj x (p.getVert h) := by
    have hm : h ∈ contactPositions p x := by simpa [marks] using m
    exact ((mem_contactPositions p x h).mp hm).2.symm
  have charge (h : ℕ) (hh : h < p.support.length) (missing : h≠i ∧ h≠j)
      (link : ∃ w, G.Adj x w ∧ G.Adj (p.getVert h) w) : G.dist x (p.getVert h)=2 := by
    obtain ⟨w,hx,hw⟩ := link
    have different : x ≠ p.getVert h := fun eq => outside (eq ▸ p.getVert_mem_support h)
    apply two_step_metric different _ hx hw
    intro adj
    have hm := (mem_contactPositions p x h).mpr ⟨hh,adj.symm⟩
    rw [marks] at hm
    simp only [mem_insert,mem_singleton,missing.1,missing.2,or_self] at hm
  have shifts (h : ℕ) (hh : h∈W) : h < p.support.length ∧ G.dist x (p.getVert h)=2 := by
    have len := p.length_support
    have before (t : ℕ) (pos : 0 < t) (range : t < p.support.length) (hit : t=i ∨ t=j)
        (miss : t-1≠i ∧ t-1≠j) : G.dist x (p.getVert (t-1))=2 := by
      have step := p.adj_getVert_succ (i:=t-1) (by omega)
      rw [show t-1+1=t by omega] at step
      exact charge _ (by omega) miss ⟨_,mark hit,step⟩
    have after (t : ℕ) (range : t+1 < p.support.length) (hit : t=i ∨ t=j)
        (miss : t+1≠i ∧ t+1≠j) : G.dist x (p.getVert (t+1))=2 :=
      charge _ range miss ⟨_,mark hit,(p.adj_getVert_succ (i:=t) (by omega)).symm⟩
    simp only [W,mem_insert,mem_singleton] at hh
    rcases hh with rfl|rfl|rfl|rfl
    · exact ⟨by omega,before i left (by omega) (Or.inl rfl) (by omega)⟩
    · exact ⟨by omega,after i (by omega) (Or.inl rfl) (by omega)⟩
    · exact ⟨by omega,before j (by omega) (by omega) (Or.inr rfl) (by omega)⟩
    · exact ⟨right,after j right (Or.inr rfl) (by omega)⟩
  let T := insert u (insert v J)
  have good (h : ℕ) (hh : h ∈ T) : h < p.support.length ∧ G.dist x (p.getVert h)=2 := by
    rcases mem_insert.mp hh with rfl | hrest
    · exact shifts _ hu
    rcases mem_insert.mp hrest with rfl | member
    · exact shifts _ hv
    have r := (mem_Ico.mp member).2.trans_le bound
    exact ⟨r,charge _ r (unmarked _ member) (via _ member)⟩
  have count : T.card=5 := by
    have jcard : J.card=hi-lo := Nat.card_Ico _ _
    rw [show T=insert u (insert v J) from rfl,card_insert_of_notMem (by simpa [ne] using uout),
      card_insert_of_notMem vout,jcard]
    omega
  have inj : Set.InjOn p.getVert (T : Set ℕ) := by
    intro h hh e he eq
    have := (good _ hh).1
    have := (good _ he).1
    have := p.length_support
    exact hp.getVert_injOn (by change h ≤ p.length; omega) (by change e ≤ p.length; omega) eq
  have sub : T.image p.getVert ⊆ univ.filter (fun y => G.dist x y=2) := by
    intro w hw
    obtain ⟨e,he,rfl⟩ := mem_image.mp hw
    exact mem_filter.mpr ⟨mem_univ _,(good _ he).2⟩
  have large := (card_le_card sub).trans quota
  rw [card_image_of_injOn inj,count] at large
  omega

/-- The original even-distance formulation of the same terminal obstruction. -/
theorem impossible (p : G.Walk a b) (hp : p.IsPath) {x : V} (outside : x ∉ p.support)
    {i j lo hi : ℕ} (left : 0 < i) (spaced : i+2 ≤ j) (right : j+1 < p.support.length)
    (marks : contactPositions p x = {i,j})
    (bound : hi ≤ p.support.length) (size : lo+3=hi)
    (unmarked : ∀ h ∈ Ico lo hi, h ≠ i ∧ h ≠ j)
    (via : ∀ h ∈ Ico lo hi, ∃ w, G.Adj x w ∧ G.Adj (p.getVert h) w)
    (cap : G.distEven x ≤ 5) : False := by
  classical
  apply impossible_of_exact p hp outside left spaced right marks bound size unmarked via
  let T := univ.filter (fun y => G.dist x y=2)
  have missing : x ∉ T := by simp [T]
  have sub : insert x T ⊆ univ.filter (fun y => Even (G.dist x y)) := by
    intro w hw
    rcases mem_insert.mp hw with rfl|h
    · simp
    · exact mem_filter.mpr ⟨mem_univ _,by rw [(mem_filter.mp h).2]; decide⟩
  have count := card_le_card sub
  rw [card_insert_of_notMem missing] at count
  change T.card+1 ≤ G.distEven x at count
  change T.card ≤ 4
  omega

end Graph189FourTerminalGap
#print axioms Graph189FourTerminalGap.impossible_of_exact
#print axioms Graph189FourTerminalGap.impossible
