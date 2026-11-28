import Graph189ThreeNearSupports
import Graph189ThreeCutSaturationFacts

open SimpleGraph Finset Graph189PositiveEvenCut
namespace Graph189ThreeNearGraph

private theorem largest {α : Type*} [DecidableEq α] {T : Finset α} (f : α→ℕ)
    (non : T.Nonempty) : ∃ i∈T,∀ j∈T,f j≤f i := by
  classical
  have n := non.image f
  obtain ⟨i,hi,top⟩ := mem_image.mp (max'_mem _ n)
  refine ⟨i,hi,fun j hj => ?_⟩
  rw [top]
  exact le_max' _ _ (mem_image_of_mem f hj)

private theorem order_three {α : Type*} [DecidableEq α] {S : Finset α}
    (f : α→ℕ) (three : S.card=3) :
    ∃ i j l : α,i≠j ∧ i≠l ∧ j≠l ∧ S={i,j,l} ∧ f l≤f j ∧ f j≤f i := by
  classical
  obtain ⟨i,ins,top⟩ := largest f (card_pos.mp (by omega : 0<S.card))
  have sc := card_erase_of_mem ins
  obtain ⟨j,js,middle⟩ := largest f (card_pos.mp (by omega : 0<(S.erase i).card))
  have tc := card_erase_of_mem js
  obtain ⟨l,single⟩ := card_eq_one.mp (by omega : ((S.erase i).erase j).card=1)
  have ls : l∈(S.erase i).erase j := single ▸ mem_singleton_self _
  have distinct := (mem_erase.mp ls).1
  have lrest := (mem_erase.mp ls).2
  have equal : S={i,j,l} := by
    calc
      S=insert i (S.erase i) := (insert_erase ins).symm
      _=insert i (insert j ((S.erase i).erase j)) := by rw [insert_erase js]
      _={i,j,l} := by rw [single]
  exact ⟨i,j,l,(mem_erase.mp js).1.symm,(mem_erase.mp lrest).1.symm,distinct.symm,
    equal,middle l lrest,top j (mem_erase.mp js).2⟩

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B S X Y : Finset V}

theorem excludes_population (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (smaller : ∀ T : Finset V, T.card<S.card → (G.induce {v : V | v∉T}).Connected)
    (three : S.card=3) (cap : ∀ v,G.distEven v≤1+G.secondSmallestDegree)
    (xs : X⊆A) (ys : Y⊆B) (xh : ∀ a∈X,G.secondSmallestDegree≤G.degree a)
    (yh : ∀ b∈Y,G.secondSmallestDegree≤G.degree b)
    (k24 : G.secondSmallestDegree=24) (x33 : X.card=33) (y72 : Y.card=72) : False := by
  classical
  let A1 (i : V) := X.filter (G.Adj i)
  let B1 (i : V) := Y.filter (G.Adj i)
  let A2 (i : V) := X.filter (fun a => G.dist i a=2)
  let B2 (i : V) := Y.filter (fun b => G.dist i b=2)
  have cp (v : V) : G.distEven v≤24+1 := by simpa only [k24] using cap v
  have aBound (i : V) (hi : i∈S) : (A1 i).card≤22 := by
    have t := Graph189ThreeCutSaturationFacts.first_column hc cut smaller three cap xs ys xh yh hi
    rw [k24,x33,y72] at t
    exact t.trans (by decide)
  have bBound (i : V) (hi : i∈S) : (B1 i).card≤23 := by
    have t := Graph189ThreeCutSaturationFacts.first_column hc cut.swap smaller three cap ys xs yh xh hi
    rw [k24,x33,y72] at t
    exact t.trans (by decide)
  have budget (i : V) := Graph189PrivateQuota.two_layer_budget G (cp i) (A2 i) (B2 i)
    (cut.apart.mono ((filter_subset _ _).trans xs) ((filter_subset _ _).trans ys))
    (fun a ha => (mem_filter.mp ha).2) (fun b hb => (mem_filter.mp hb).2)
  have near (i j l : V) (names : S={i,j,l}) (bc : (B1 i).card=23) :
      (A1 i).Nonempty ∧ A1 i⊆A1 j∪A1 l := by
    have ins : i∈S := by rw [names]; simp
    have high := Graph189AlmostFullColumn.opposite_population hc cut.swap smaller cp ys xs ins
      (t:=1) (by change 24≤(B1 i).card+1; omega) (by omega)
    change X.card≤24+(A1 i).card+1 at high
    refine ⟨card_pos.mp (by omega),?_⟩
    intro a ha
    obtain ⟨ax,ia⟩ := mem_filter.mp ha
    have col2 (b : V) (bcol : b∈B1 i) : G.dist a b=2 :=
      Graph189PortDifference.cross_two hc cut (xs ax) (ys (mem_filter.mp bcol).1)
        ia.symm (mem_filter.mp bcol).2
    have useB := Graph189BoundaryDebit.even_quota hc cut smaller cp
      (show B1 i⊆B from (filter_subset _ _).trans ys) (xs ax)
    have eq : (B1 i).filter (fun b => Even (G.dist a b))=B1 i :=
      filter_eq_self.mpr fun b hb => by simp [col2 b hb]
    rw [eq,three,bc] at useB
    by_contra missing
    have onlyi : Graph189PortLabels.support G S a⊆{i} := by
      intro w hw
      obtain ⟨ws,aw⟩ := mem_filter.mp hw
      have cases : w=i ∨ w=j ∨ w=l := by simpa only [names,mem_insert,mem_singleton] using ws
      rcases cases with e|e|e
      · exact mem_singleton.mpr e
      · exact False.elim (missing (mem_union_left _ (mem_filter.mpr ⟨ax,e ▸ aw.symm⟩)))
      · exact False.elim (missing (mem_union_right _ (mem_filter.mpr ⟨ax,e ▸ aw.symm⟩)))
    have bound := card_le_card onlyi
    simp only [card_singleton] at bound
    omega
  have pair (i j : V) (share : (A1 i∩A1 j).Nonempty) : (B1 i∪B1 j).card≤24 := by
    obtain ⟨a,ha⟩ := share
    obtain ⟨ai,aj⟩ := mem_inter.mp ha
    have ax := (mem_filter.mp ai).1
    have one (l : V) (ll : a∈A1 l) (b : V) (bl : b∈B1 l) : b∈evenOthers G a := by
      have bt := (mem_filter.mp bl).1
      have ne : b≠a := fun e => disjoint_left.mp cut.apart (xs ax) (e ▸ ys bt)
      have two := Graph189PortDifference.cross_two hc cut (xs ax) (ys bt)
        (mem_filter.mp ll).2.symm (mem_filter.mp bl).2
      exact mem_even_others ne (by simp [two])
    have sub : B1 i∪B1 j⊆evenOthers G a :=
      fun b hb => (mem_union.mp hb).elim (one i ai b) (one j aj b)
    exact (card_le_card sub).trans (even_others_card (cp a))
  obtain ⟨i,j,l,ij,il,jl,names,rank⟩ := order_three (fun w => (B1 w).card) three
  have members : i∈S ∧ j∈S ∧ l∈S := by simp [names]
  have jname : S={j,i,l} := by rw [names]; ext v; simp only [mem_insert,mem_singleton]; tauto
  have lname : S={l,i,j} := by rw [names]; ext v; simp only [mem_insert,mem_singleton]; tauto
  have cases := Graph189ThreeNearSupports.graph_cases (X:=X) (A:=A1 i) (D:=A1 j)
    (E:=A1 l) (B:=B1 i) (C:=B1 j) (F:=B1 l)
    (filter_subset _ _) (filter_subset _ _) (filter_subset _ _) x33
    (bBound i members.1) (bBound j members.2.1) (bBound l members.2.2)
    (near i j l names) (near j i l jname) (near l i j lname)
    (pair i j) (pair i l) (pair j l) rank
  let P := B1 i∪B1 j∪B1 l
  have cover : Y⊆P∪S.biUnion B2 := by
    intro b hb
    by_cases port : ∃ w∈S,G.Adj w b
    · obtain ⟨w,ws,wb⟩ := port
      have labels : w=i ∨ w=j ∨ w=l := by simpa only [names,mem_insert,mem_singleton] using ws
      have h : b∈B1 w := mem_filter.mpr ⟨hb,wb⟩
      apply mem_union_left
      change b∈B1 i∪B1 j∪B1 l
      rcases labels with e|e|e
      · exact mem_union_left _ (mem_union_left _ (e ▸ h))
      · exact mem_union_left _ (mem_union_right _ (e ▸ h))
      · exact mem_union_right _ (e ▸ h)
    · obtain ⟨w,ws,dist⟩ := Graph189ThreeColumns.nonport_second hc cut cap xs xh (by omega)
          (ys hb) (yh b hb) (fun w ws wb => port ⟨w,ws,wb⟩)
      exact mem_union_right _ (mem_biUnion.mpr ⟨w,ws,mem_filter.mpr ⟨hb,dist⟩⟩)
  have covered := (card_le_card cover).trans (card_union_le _ _)
  have used : (S.biUnion B2).card≤∑ w∈S,(B2 w).card := card_biUnion_le
  have sums (f : V→ℕ) : (∑ w∈S,f w)=f i+f j+f l := by
    simp [names,ij,il,jl,Nat.add_assoc]
  rw [sums] at used
  have raw := Graph189DebitedCutProduct.with_columns hc cut xs ys smaller cap xh yh
  have one (w : V) : X.filter (fun x => G.dist x w=1)=A1 w := by
    ext a
    simp only [A1,mem_filter,dist_eq_one_iff_adj]
    exact and_congr_right (fun _ => G.adj_comm a w)
  have two (w : V) : X.filter (fun x => G.dist x w=2)=A2 w := by
    ext a
    simp only [A2,mem_filter,dist_comm (u:=a) (v:=w)]
  have target (w : V) : Y.filter (fun b => G.dist w b=1)=B1 w := by
    simp only [B1,dist_eq_one_iff_adj]
  simp only [one,two,target,three,k24,x33,y72,sums] at raw
  have charge : 1683≤(A1 i).card+(A1 j).card+(A1 l).card+
      ((A1 i).card*(B2 i).card+(B1 i).card*(A2 i).card)+
      ((A1 j).card*(B2 j).card+(B1 j).card*(A2 j).card)+
      ((A1 l).card*(B2 l).card+(B1 l).card*(A2 l).card) := by
    dsimp only [B2]
    rw [Nat.mul_comm (B1 i).card,Nat.mul_comm (B1 j).card,Nat.mul_comm (B1 l).card]
    omega
  change ((B1 i).card=23 → P.card≤47) ∧ ((B1 l).card=23 → P.card≤25) ∧
    ((B1 j).card=23 → (B1 l).card<23 → (A1 l).card=22 →
      P.card≤25 ∨ (A1 i).card+(A1 j).card+(A1 l).card≤44) at cases
  apply Graph189ThreeNearArithmetic.impossible (aBound i members.1) (aBound j members.2.1)
    (aBound l members.2.2) (bBound i members.1) rank (budget i) (budget j) (budget l) charge
  · intro nearI
    have h := cases.1 nearI
    omega
  · intro nearL
    have h := cases.2.1 nearL
    omega
  · intro nearJ smallL fullL
    rcases cases.2.2 nearJ smallL fullL with h|h
    · left
      omega
    · exact Or.inr h

#print axioms excludes_population
end Graph189ThreeNearGraph
