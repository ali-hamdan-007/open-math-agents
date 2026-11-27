import Graph199RankedConnector

open Finset SimpleGraph

namespace Graph199

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Connect consecutive centers using disjoint intermediate vertex sets.
Each intermediate set can meet only its two incident centers. -/
theorem connector_of_ordered_blocks {d : ℕ}
    (center : Fin (d+1) ↪ V) (block : Fin d → Set V)
    (havoid : ∀ i j, center i ∉ block j)
    (hdis : ∀ i j, i ≠ j → Disjoint (block i) (block j))
    (hcross : ∀ i j, i ≠ j → ∀ x ∈ block i, ∀ y ∈ block j, ¬ G.Adj x y)
    (hclose : ∀ i j, G.Adj (center i) (center j) →
      i.val ≤ j.val+1 ∧ j.val ≤ i.val+1)
    (hincident : ∀ i j, ∀ x ∈ block j, G.Adj (center i) x →
      i.val = j.val ∨ i.val = j.val+1)
    (hconnect : ∀ j : Fin d, G.Adj (center j.castSucc) (center j.succ) ∨
      ((G.induce (block j)).Connected ∧
        (∃ x ∈ block j, G.Adj (center j.castSucc) x) ∧
        (∃ x ∈ block j, G.Adj (center j.succ) x))) :
    ∃ B : Finset V, (∀ x ∈ B, (∃ i, x = center i) ∨ (∃ j, x ∈ block j)) ∧
      (∀ i, center i ∈ B) ∧ d+1 ≤ B.card ∧
      (G.induce (B : Set V)).IsTree := by
  classical
  let S : Set V := {x | (∃ i, x = center i) ∨ (∃ j, x ∈ block j)}
  let c : Fin (d+1) ↪ S :=
    ⟨fun i => ⟨center i,Or.inl ⟨i,rfl⟩⟩, fun i j he => center.injective (congrArg Subtype.val he)⟩
  let index (x : V) (n : ℕ) :=
    (∃ i : Fin (d+1), x = center i ∧ n = i.val) ∨
    (∃ j : Fin d, x ∈ block j ∧ n = j.val)
  have hex (x : S) : ∃ n, index x.val n := by
    rcases x.property with ⟨i,hi⟩ | ⟨j,hj⟩
    · exact ⟨i.val,Or.inl ⟨i,hi,rfl⟩⟩
    · exact ⟨j.val,Or.inr ⟨j,hj,rfl⟩⟩
  have huniq {x : V} {n m : ℕ} (hn : index x n) (hm : index x m) : n = m := by
    rcases hn with ⟨i,rfl,rfl⟩ | ⟨i,hi,rfl⟩
    · rcases hm with ⟨j,hj,rfl⟩ | ⟨j,hj,rfl⟩
      · rw [center.injective hj]
      · exact False.elim (havoid i j hj)
    · rcases hm with ⟨j,rfl,rfl⟩ | ⟨j,hj,rfl⟩
      · exact False.elim (havoid j i hi)
      · by_cases he : i = j
        · rw [he]
        · exact False.elim (Set.disjoint_left.mp (hdis i j he) hi hj)
  let rank (x : S) : ℕ := (hex x).choose
  have hindex (x : S) : index x.val (rank x) := (hex x).choose_spec
  have hc (i : Fin (d+1)) : rank (c i) = i.val :=
    huniq (hindex (c i)) (Or.inl ⟨i,rfl,rfl⟩)
  have hs x y (he : (G.induce S).Adj x y) (hlt : rank x < rank y) :
      rank y = rank x+1 ∧ ∃ i : Fin (d+1), rank y = i.val ∧ y = c i := by
    have he' : G.Adj x.val y.val := he
    rcases hindex x with ⟨i,hi,hir⟩ | ⟨i,hi,hir⟩ <;>
      rcases hindex y with ⟨j,hj,hjr⟩ | ⟨j,hj,hjr⟩
    · have hh := hclose i j (hi ▸ hj ▸ he')
      exact ⟨by omega, j,hjr,Subtype.ext hj⟩
    · have hh := hincident i j y.val hj (hi ▸ he')
      omega
    · have hh := hincident j i x.val hi (hj ▸ he'.symm)
      exact ⟨by omega, j,hjr,Subtype.ext hj⟩
    · have hne : i ≠ j := by
        intro heq
        subst j
        omega
      exact False.elim (hcross i j hne x.val hi y.val hj he')
  have hreachStep (j : Fin d) : (G.induce S).Reachable (c j.castSucc) (c j.succ) := by
    rcases hconnect j with he | ⟨hj,⟨a,ha,hea⟩,⟨b,hb,heb⟩⟩
    · exact (show (G.induce S).Adj (c j.castSucc) (c j.succ) from he).reachable
    · let e : G.induce (block j) →g G.induce S :=
        ⟨fun x => ⟨x.val,Or.inr ⟨j,x.property⟩⟩, fun h => h⟩
      have hr := (hj ⟨a,ha⟩ ⟨b,hb⟩).map e
      have hae : (G.induce S).Adj (c j.castSucc) (e ⟨a,ha⟩) := hea
      have hbe : (G.induce S).Adj (c j.succ) (e ⟨b,hb⟩) := heb
      exact hae.reachable.trans (hr.trans hbe.symm.reachable)
  have huu (i : Fin (d+1)) : (G.induce S).Reachable (c 0) (c i) := by
    induction i using Fin.induction with
    | zero => exact ⟨Walk.nil⟩
    | succ i ih => exact ih.trans (hreachStep i)
  exact ranked_connector rank c hc hs (huu (Fin.last d))

#print axioms connector_of_ordered_blocks

/-- The centers and blocks in a closed interval of an ordered connector
contain an induced tree through all interval centers. -/
theorem connector_of_ordered_interval {d : ℕ}
    (center : Fin (d+1) ↪ V) (block : Fin d → Set V)
    (havoid : ∀ i j, center i ∉ block j)
    (hdis : ∀ i j, i ≠ j → Disjoint (block i) (block j))
    (hcross : ∀ i j, i ≠ j → ∀ x ∈ block i, ∀ y ∈ block j, ¬ G.Adj x y)
    (hclose : ∀ i j, G.Adj (center i) (center j) →
      i.val ≤ j.val+1 ∧ j.val ≤ i.val+1)
    (hincident : ∀ i j, ∀ x ∈ block j, G.Adj (center i) x →
      i.val = j.val ∨ i.val = j.val+1)
    (hconnect : ∀ j : Fin d, G.Adj (center j.castSucc) (center j.succ) ∨
      ((G.induce (block j)).Connected ∧
        (∃ x ∈ block j, G.Adj (center j.castSucc) x) ∧
        (∃ x ∈ block j, G.Adj (center j.succ) x)))
    (l n : ℕ) (hlt : l+n ≤ d) :
    ∃ B : Finset V,
      (∀ x ∈ B, (∃ i, l ≤ i.val ∧ i.val ≤ l+n ∧ x = center i) ∨
        (∃ j, l ≤ j.val ∧ j.val < l+n ∧ x ∈ block j)) ∧
      (∀ i, l ≤ i.val → i.val ≤ l+n → center i ∈ B) ∧
      n+1 ≤ B.card ∧ (G.induce (B : Set V)).IsTree := by
  let ci (i : Fin (n+1)) : Fin (d+1) := ⟨l+i.val, by have hi := i.isLt; omega⟩
  let bi (j : Fin n) : Fin d := ⟨l+j.val, by have hj := j.isLt; omega⟩
  let c : Fin (n+1) ↪ V :=
    ⟨fun i => center (ci i),fun i j he => Fin.ext (by
      have h := Fin.ext_iff.mp (center.injective he)
      change l+i.val = l+j.val at h
      omega)⟩
  let b (j : Fin n) := block (bi j)
  have hinjb : Function.Injective bi := by
    intro i j he
    apply Fin.ext
    have h := Fin.ext_iff.mp he
    change l+i.val = l+j.val at h
    omega
  have hc j : (bi j).castSucc = ci (Fin.castSucc j) := Fin.ext rfl
  have hs j : (bi j).succ = ci (Fin.succ j) := Fin.ext (by simp [ci,bi,Nat.add_assoc])
  have hbnd i j (he : G.Adj (c i) (c j)) :
      i.val ≤ j.val+1 ∧ j.val ≤ i.val+1 := by
    have h := hclose (ci i) (ci j) he
    change l+i.val ≤ l+j.val+1 ∧ l+j.val ≤ l+i.val+1 at h
    omega
  have hinc i j x (hm : x ∈ b j) (he : G.Adj (c i) x) :
      i.val = j.val ∨ i.val = j.val+1 := by
    have h := hincident (ci i) (bi j) x hm he
    change l+i.val = l+j.val ∨ l+i.val = l+j.val+1 at h
    omega
  have hcon (j : Fin n) : G.Adj (c j.castSucc) (c j.succ) ∨
      ((G.induce (b j)).Connected ∧
        (∃ x ∈ b j, G.Adj (c j.castSucc) x) ∧
        (∃ x ∈ b j, G.Adj (c j.succ) x)) := by
    have h := hconnect (bi j)
    rw [hc,hs] at h
    exact h
  obtain ⟨B,hB,hcent,hcard,htree⟩ := connector_of_ordered_blocks c b
    (fun i j => havoid (ci i) (bi j))
    (fun i j he => hdis (bi i) (bi j) (fun hh => he (hinjb hh)))
    (fun i j he => hcross (bi i) (bi j) (fun hh => he (hinjb hh)))
    hbnd hinc hcon
  refine ⟨B,?_,?_,hcard,htree⟩
  · intro x hx
    rcases hB x hx with ⟨i,hi⟩ | ⟨j,hj⟩
    · have he := i.isLt
      exact Or.inl ⟨ci i, by change l ≤ l+i.val; omega,
        by change l+i.val ≤ l+n; omega, hi⟩
    · have he := j.isLt
      exact Or.inr ⟨bi j, by change l ≤ l+j.val; omega,
        by change l+j.val < l+n; omega, hj⟩
  · intro i hl hr
    let j : Fin (n+1) := ⟨i.val-l,by omega⟩
    have he : ci j = i := Fin.ext (by change l+(i.val-l) = i.val; omega)
    simpa only [show c j = center (ci j) from rfl,he] using hcent j

#print axioms connector_of_ordered_interval

end Graph199
