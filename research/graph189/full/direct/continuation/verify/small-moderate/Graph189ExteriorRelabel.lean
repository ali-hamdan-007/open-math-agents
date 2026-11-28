import Graph189ExteriorMask

namespace Graph189ExteriorMask

/-- An isomorphism witness from one labelled mask to a retained representative. -/
structure RelabelWitness where
  source : ℕ
  target : ℕ
  images : List ℕ

def RelabelWitness.image (w : RelabelWitness) (i : Fin b) : Fin b :=
  ⟨(w.images.getD i.val 0)%b,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

private def RelabelWitness.checkPair (w : RelabelWitness) (i j : Fin b) : Bool :=
  decide (w.image i=w.image j → i=j) &&
    decide ((graph b w.target).Adj (w.image i) (w.image j) ↔ (graph b w.source).Adj i j)

def RelabelWitness.check (b : ℕ) (reps : List ℕ) (w : RelabelWitness) : Bool :=
  decide (w.target ∈ reps) &&
    (List.finRange b).all (fun i => (List.finRange b).all (w.checkPair i))

theorem RelabelWitness.sound {b : ℕ} {reps : List ℕ} {w : RelabelWitness}
    (h : w.check b reps=true) :
    w.target ∈ reps ∧ Nonempty (graph b w.source ≃g graph b w.target) := by
  unfold RelabelWitness.check at h
  obtain ⟨member,all⟩ := Bool.and_eq_true_iff.mp h
  have pair (i j : Fin b) := Bool.and_eq_true_iff.mp
    (List.all_eq_true.mp (List.all_eq_true.mp all i (List.mem_finRange i)) j (List.mem_finRange j))
  have inj : Function.Injective (w.image (b := b)) := fun i j => of_decide_eq_true (pair i j).1
  let e := Equiv.ofBijective w.image ⟨inj,Finite.surjective_of_injective inj⟩
  exact ⟨of_decide_eq_true member,⟨⟨e,fun {i j} => of_decide_eq_true (pair i j).2⟩⟩⟩

private theorem extendMask_mod {b old star : ℕ} (h : old<2^edgeCount b) :
    extendMask b old star % 2^edgeCount b=old := by
  exact (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt h)

private theorem extendMask_div {b old star : ℕ} (h : old<2^edgeCount b) :
    extendMask b old star / 2^edgeCount b=star := by
  rw [extendMask,Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt h,Nat.zero_add]

@[simp] private theorem extend_adj_cast {b old star : ℕ} (h : old<2^edgeCount b) (i j : Fin b) :
    (graph (b+1) (extendMask b old star)).Adj i.castSucc j.castSucc ↔
      (graph b old).Adj i j := by
  simp only [graph_adj,ne_eq,Fin.castSucc_inj]
  by_cases ne : i=j
  · simp [ne]
  · have lt : slot i j<edgeCount b := by
      rcases lt_or_gt_of_ne ne with lt|gt
      · exact slot_lt lt
      · rw [slot_comm j i]
        exact slot_lt gt
    change i≠j ∧ (extendMask b old star).testBit (slot i j)=true ↔
      i≠j ∧ old.testBit (slot i j)=true
    have hb := Nat.testBit_mod_two_pow (extendMask b old star) (edgeCount b) (slot i j)
    rw [extendMask_mod h,decide_eq_true lt,Bool.true_and] at hb
    rw [hb]

@[simp] private theorem extend_adj_last {b old star : ℕ} (h : old<2^edgeCount b) (i : Fin b) :
    (graph (b+1) (extendMask b old star)).Adj i.castSucc (Fin.last b) ↔
      star.testBit i.val=true := by
  rw [graph_adj,slot_of_lt (Fin.castSucc_lt_last i)]
  change i.castSucc≠Fin.last b ∧
    (extendMask b old star).testBit (edgeCount b+i.val)=true ↔ star.testBit i.val=true
  rw [Nat.add_comm (edgeCount b) i.val,Nat.testBit_add,extendMask_div h]
  exact and_iff_right (Fin.castSucc_lt_last i).ne

private theorem extend_adj_last_symm {b old star : ℕ} (h : old<2^edgeCount b) (i : Fin b) :
    (graph (b+1) (extendMask b old star)).Adj (Fin.last b) i.castSucc ↔
      star.testBit i.val=true :=
  (SimpleGraph.adj_comm _ _ _).trans (extend_adj_last h i)

private def extendLabel {b : ℕ} (e : Fin b ≃ Fin b) : Fin (b+1) → Fin (b+1) :=
  Fin.lastCases (Fin.last b) (fun i => (e i).castSucc)

private def extendEquiv {b : ℕ} (e : Fin b ≃ Fin b) : Fin (b+1) ≃ Fin (b+1) where
  toFun := extendLabel e
  invFun := extendLabel e.symm
  left_inv := fun i => Fin.lastCases (by simp [extendLabel])
    (fun j => by simp [extendLabel]) i
  right_inv := fun i => Fin.lastCases (by simp [extendLabel])
    (fun j => by simp [extendLabel]) i

private def extendIso {b m r star : ℕ} (hm : m<2^edgeCount b) (hr : r<2^edgeCount b)
    (e : graph b m ≃g graph b r) :
    graph (b+1) (extendMask b m star) ≃g graph (b+1)
      (extendMask b r (packBits b (fun i => star.testBit (e.symm i).val))) where
  toEquiv := extendEquiv e.toEquiv
  map_rel_iff' := by
    intro i j
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · refine Fin.lastCases ?_ (fun j' => ?_) j
      · change (graph _ _).Adj (extendLabel e.toEquiv (Fin.last b))
            (extendLabel e.toEquiv (Fin.last b)) ↔ _
        simp [extendLabel]
      · change (graph _ _).Adj (extendLabel e.toEquiv (Fin.last b))
            (extendLabel e.toEquiv j'.castSucc) ↔ _
        simp only [extendLabel,Fin.lastCases_last,Fin.lastCases_castSucc,
          extend_adj_last_symm hr,extend_adj_last_symm hm,packBits_read]
        change star.testBit (e.symm (e j')).val=true ↔ star.testBit j'.val=true
        rw [RelIso.symm_apply_apply]
    · refine Fin.lastCases ?_ (fun j' => ?_) j
      · change (graph _ _).Adj (extendLabel e.toEquiv i'.castSucc)
            (extendLabel e.toEquiv (Fin.last b)) ↔ _
        simp only [extendLabel,Fin.lastCases_castSucc,Fin.lastCases_last,
          extend_adj_last hr,extend_adj_last hm,packBits_read]
        change star.testBit (e.symm (e i')).val=true ↔ star.testBit i'.val=true
        rw [RelIso.symm_apply_apply]
      · change (graph _ _).Adj (extendLabel e.toEquiv i'.castSucc)
            (extendLabel e.toEquiv j'.castSucc) ↔ _
        simp only [extendLabel,Fin.lastCases_castSucc,extend_adj_cast hr,extend_adj_cast hm]
        exact e.map_rel_iff' (a := i') (b := j')

/-- Bounded masks of a fixed order have a relabelling into the retained list. -/
def Covers (b : ℕ) (reps : List ℕ) : Prop :=
  ∀ m<2^edgeCount b, ∃ r∈reps, Nonempty (graph b m ≃g graph b r)

theorem covers_zero : Covers 0 [0] := by
  intro m hm
  have eq : m=0 := by simp [edgeCount] at hm; exact hm
  subst m
  exact ⟨0,by simp,⟨SimpleGraph.Iso.refl⟩⟩

/-- Each possible last-vertex adjacency pattern is tried exactly once per
representative of the previous order. -/
def extensions (b : ℕ) (reps : List ℕ) : List ℕ :=
  reps.flatMap (fun m => (List.range (2^b)).map (extendMask b m))

/-- Coverage propagates from one order to the next using the checked relabellings. -/
theorem covers_succ {b : ℕ} {old next : List ℕ} {ws : List RelabelWitness}
    (hold : Covers b old) (bound : old.all (fun m => decide (m<2^edgeCount b))=true)
    (sources : ws.map RelabelWitness.source=extensions b old)
    (checks : ws.all (RelabelWitness.check (b+1) next)=true) :
    Covers (b+1) next := by
  intro m hm
  obtain ⟨a,ha,star,_,rfl⟩ := split_mask hm
  obtain ⟨r,hr,⟨e⟩⟩ := hold a ha
  have hbound : r<2^edgeCount b := of_decide_eq_true (List.all_eq_true.mp bound r hr)
  let moved := packBits b (fun i => star.testBit (e.symm i).val)
  have hs : extendMask b r moved ∈ extensions b old :=
    List.mem_flatMap.mpr ⟨r,hr,List.mem_map.mpr ⟨moved,List.mem_range.mpr (packBits_lt _),rfl⟩⟩
  rw [← sources] at hs
  obtain ⟨w,hw,hws⟩ := List.mem_map.mp hs
  obtain ⟨hn,⟨iso⟩⟩ := RelabelWitness.sound (List.all_eq_true.mp checks w hw)
  refine ⟨w.target,hn,⟨(extendIso ha hbound e).trans ?_⟩⟩
  rwa [hws] at iso

theorem Covers.label {V : Type*} [Fintype V] {b : ℕ} {reps : List ℕ}
    (h : Covers b reps) (G : SimpleGraph V) (card : Fintype.card V=b) :
    ∃ m∈reps, Nonempty (G ≃g graph b m) := by
  obtain ⟨a,ha,⟨e⟩⟩ := exists_mask_labeling G card
  obtain ⟨m,hm,⟨f⟩⟩ := h a ha
  exact ⟨m,hm,⟨e.trans f⟩⟩

#print axioms covers_succ
end Graph189ExteriorMask
