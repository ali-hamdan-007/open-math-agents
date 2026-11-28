import Graph189DenseExteriorCensus

open SimpleGraph Finset Graph189OptimalExterior Graph189ExteriorGap
namespace Graph189ExteriorLeaf
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Once the order excludes a further disjoint contact, every high row is
identical. A low vertex cannot reach an extra mark, since it would augment
a full matching on high vertices. -/
theorem common_contacts {a b : V} {p : G.Walk a b} {C : Finset V} {k : ℕ}
    (h : Chosen p C k) (r : ComponentRoutes p C) {s : ℕ} (pos : 0<s)
    (H : Finset V) (sub : H⊆C) (many : s<H.card)
    (rows : ∀v∈H,s≤((univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] v)).card)
    (upper : Fintype.card V+1<(s+3)*C.card+s+1) :
    ∃A : Finset (Fin p.support.length), A.card=s ∧
      (∀v∈H,∀i : Fin p.support.length, G.Adj p.support[i.val] v ↔ i∈A) ∧
      (∀v∈C,∀i : Fin p.support.length, G.Adj p.support[i.val] v → i∈A) := by
  classical
  let N (v : V) := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] v)
  let A := H.biUnion N
  let inc : H ↪ C := ⟨fun v => ⟨v.val,sub v.property⟩,
    fun _ _ eq => Subtype.ext (congrArg (fun v:C => v.val) eq)⟩
  have exclude (M : Finset (Fin p.support.length)) (size : M.card=s+1) (f : M ↪ C)
      (edge : ∀i : M,G.Adj p.support[i.val.val] (f i).val) : False := by
    have bound := near_match_order h r M (card_pos.mp (by omega)) f edge
    rw [size,show s+1+2=s+3 by omega] at bound
    omega
  have small : A.card≤s := by
    by_contra! wide
    obtain ⟨M,size,f,edge⟩ := Graph189ExteriorAttachment.extra_port p H s many rows wide
    exact exclude M size (f.trans inc) edge
  have incl (v : V) (vh : v∈H) : N v⊆A := fun i hi => mem_biUnion.mpr ⟨v,vh,hi⟩
  have same (v : V) (vh : v∈H) : N v=A :=
    eq_of_subset_of_card_le (incl v vh) (small.trans (rows v vh))
  obtain ⟨w,wh⟩ := card_pos.mp (show 0<H.card by omega)
  have card : A.card=s := le_antisymm small ((rows w wh).trans (card_le_card (incl w wh)))
  have all (v : V) (vh : v∈H) (i : Fin p.support.length) : G.Adj p.support[i.val] v ↔ i∈A := by
    rw [←same v vh]; simp [N]
  refine ⟨A,card,all,?_⟩
  intro v vc i e
  by_contra out
  have vh : v∉H := fun hv => out ((all v hv i).mp e)
  obtain ⟨M,size,f,edge⟩ := Graph189ExteriorAttachment.marks_of_many_neighbors p H s many.le rows
  have ma : M⊆A := fun j hj => (all (f ⟨j,hj⟩).val (f ⟨j,hj⟩).property j).mp (edge ⟨j,hj⟩)
  have off : i∉M := fun mem => out (ma mem)
  let B := insert i M
  have rest (j : B) (ne : j.val≠i) : j.val∈M := (mem_insert.mp j.property).resolve_left ne
  let assign (j : B) : C := if eq : j.val=i then ⟨v,vc⟩ else inc (f ⟨j.val,rest j eq⟩)
  have inject : Function.Injective assign := by
    intro j l eq
    by_cases ji : j.val=i <;> by_cases li : l.val=i
    · exact Subtype.ext (ji.trans li.symm)
    · have vals := congrArg (fun t:C => t.val) eq
      simp only [assign,dif_pos ji,dif_neg li] at vals
      exact False.elim (vh (vals.symm ▸ (f ⟨l.val,rest l li⟩).property))
    · have vals := congrArg (fun t:C => t.val) eq
      simp only [assign,dif_neg ji,dif_pos li] at vals
      exact False.elim (vh (vals ▸ (f ⟨j.val,rest j ji⟩).property))
    · simp only [assign,dif_neg ji,dif_neg li] at eq
      exact Subtype.ext (congrArg (fun t:M => t.val) (f.injective (inc.injective eq)))
  apply exclude B (by simp [B,off,size]) ⟨assign,inject⟩
  intro j
  by_cases eq : j.val=i
  · change G.Adj p.support[j.val.val] (assign j).val
    simpa [assign,eq] using e
  change G.Adj p.support[j.val.val] (assign j).val
  simp only [assign,dif_neg eq]
  exact edge ⟨j.val,rest j eq⟩

end Graph189ExteriorLeaf
#print axioms Graph189ExteriorLeaf.common_contacts
