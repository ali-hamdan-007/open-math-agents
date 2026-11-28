import Graph189ThreeNearArithmetic

open Finset
namespace Graph189ThreeNearSupports

private theorem fork_bound {g : ℕ} {β : Type*} [DecidableEq β] (C D E : Finset β)
    (left : (C∪D).card≤(g+2)) (right : (C∪E).card≤(g+2)) (near : C.card=(g+1)) :
    (C∪D∪E).card≤(g+3) := by
  have same : (C∪D)∪(C∪E)=C∪D∪E := by ext v; simp only [mem_union]; tauto
  have c : C⊆(C∪D)∩(C∪E) := fun v hv => mem_inter.mpr ⟨mem_union_left D hv,mem_union_left E hv⟩
  have sz := card_union_add_card_inter (C∪D) (C∪E)
  rw [same] at sz
  have bound := card_le_card c
  omega

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Three possible shared-contact pairs suffice at the two three-cut boundaries.
A near opposite column forces each of the corresponding source contacts
to touch at least one further label. -/
theorem graph_cases {g : ℕ} {X A D E : Finset α} {B C F : Finset β}
    (subA : A⊆X) (subD : D⊆X) (subE : E⊆X)
    (xsize : X.card=(3*g/2))
    (bCap : B.card≤(g+1)) (cCap : C.card≤(g+1)) (fCap : F.card≤(g+1))
    (nearA : B.card=(g+1) → A.Nonempty ∧ A⊆D∪E)
    (nearD : C.card=(g+1) → D.Nonempty ∧ D⊆A∪E)
    (nearE : F.card=(g+1) → E.Nonempty ∧ E⊆A∪D)
    (ad : (A∩D).Nonempty → (B∪C).card≤(g+2))
    (ae : (A∩E).Nonempty → (B∪F).card≤(g+2))
    (de : (D∩E).Nonempty → (C∪F).card≤(g+2))
    (rank : F.card≤C.card ∧ C.card≤B.card) :
    let P := B∪C∪F
    (B.card=(g+1) → P.card≤(2*g+3)) ∧ (F.card=(g+1) → P.card≤(g+3)) ∧
      (C.card=(g+1) → F.card<(g+1) → E.card=g → P.card≤(g+3) ∨ A.card+D.card+E.card≤(2*g)) := by
  classical
  let P := B∪C∪F
  have flip : B∪F∪C=P := by dsimp only [P]; ac_rfl
  have second : C∪B∪F=P := by dsimp only [P]; ac_rfl
  have third : F∪B∪C=P := by dsimp only [P]; ac_rfl
  have first_center (j : (A∩D).Nonempty) (l : (A∩E).Nonempty) (near : B.card=(g+1)) : P.card≤(g+3) :=
    fork_bound B C F (ad j) (ae l) near
  have second_center (j : (A∩D).Nonempty) (l : (D∩E).Nonempty) (near : C.card=(g+1)) : P.card≤(g+3) := by
    rw [←second]
    exact fork_bound C B F (by simpa only [union_comm C B] using ad j) (de l) near
  have third_center (j : (A∩E).Nonempty) (l : (D∩E).Nonempty) (near : F.card=(g+1)) : P.card≤(g+3) := by
    rw [←third]
    exact fork_bound F B C (by simpa only [union_comm F B] using ae j)
      (by simpa only [union_comm F C] using de l) near
  have edge {T U W : Finset α} (non : T.Nonempty) (all : T⊆U∪W) :
      (T∩U).Nonempty ∨ (T∩W).Nonempty := by
    obtain ⟨a,ha⟩ := non
    rcases mem_union.mp (all ha) with x|x
    · exact Or.inl ⟨a,mem_inter.mpr ⟨ha,x⟩⟩
    · exact Or.inr ⟨a,mem_inter.mpr ⟨ha,x⟩⟩
  have avoid {T U W : Finset α} (all : T⊆U∪W) (no : ¬(T∩U).Nonempty) : T⊆W := by
    intro v hv
    exact (mem_union.mp (all hv)).resolve_left fun h => no ⟨v,mem_inter.mpr ⟨hv,h⟩⟩
  have dis {T U : Finset α} (no : ¬(T∩U).Nonempty) : Disjoint T U :=
    disjoint_left.mpr fun v ht hu => no ⟨v,mem_inter.mpr ⟨ht,hu⟩⟩
  change (B.card=(g+1) → P.card≤(2*g+3)) ∧ (F.card=(g+1) → P.card≤(g+3)) ∧ _
  refine ⟨?_,?_,?_⟩
  · intro near
    obtain ⟨non,all⟩ := nearA near
    rcases edge non all with ab|af
    · have h := card_union_le (B∪C) F
      have p := ad ab
      change (B∪C∪F).card≤(2*g+3)
      omega
    · rw [←flip]
      have h := card_union_le (B∪F) C
      have p := ae af
      omega
  · intro full
    have bn : B.card=(g+1) := by omega
    have cn : C.card=(g+1) := by omega
    by_cases j : (A∩D).Nonempty
    · obtain ⟨non,all⟩ := nearE full
      rcases edge non all with l|l
      · exact first_center j (by simpa only [inter_comm E A] using l) bn
      · exact second_center j (by simpa only [inter_comm E D] using l) cn
    · obtain ⟨a,aa⟩ := (nearA bn).1
      obtain ⟨d,dd⟩ := (nearD cn).1
      have aE := avoid (nearA bn).2 j aa
      have dE := avoid (nearD cn).2 (by simpa only [inter_comm D A] using j) dd
      exact third_center ⟨a,mem_inter.mpr ⟨aa,aE⟩⟩ ⟨d,mem_inter.mpr ⟨dd,dE⟩⟩ full
  · intro cn _ sized
    have bn : B.card=(g+1) := by omega
    by_cases j : (A∩D).Nonempty
    · by_cases l : (A∩E).Nonempty
      · exact Or.inl (first_center j l bn)
      by_cases l' : (D∩E).Nonempty
      · exact Or.inl (second_center j l' cn)
      right
      have boundA := card_le_card (union_subset subA subE)
      have boundD := card_le_card (union_subset subD subE)
      rw [card_union_of_disjoint (dis l)] at boundA
      rw [card_union_of_disjoint (dis l')] at boundD
      omega
    · right
      have toE := union_subset (avoid (nearA bn).2 j)
        (avoid (nearD cn).2 (by simpa only [inter_comm D A] using j))
      have bound := card_le_card toE
      rw [card_union_of_disjoint (dis j)] at bound
      omega

#print axioms graph_cases
end Graph189ThreeNearSupports
