import Graph189RootedOmission
import Mathlib.Data.Finset.Sort

namespace Graph189RootedSplice
open SimpleGraph Finset Graph189ExteriorGap
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {x y : V}

private theorem singleton_gap (p : G.Walk x y) (hp : p.IsPath) {z : V} (off : z∉p.support)
    (size : p.support.length+1=Fintype.card V) {m : ℕ}
    (miss : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z∈r.support → r.support.length+m ≤ Fintype.card V)
    (A J B : List V) (split : p.support=A++J++B) (left : ∀ t∈A.getLast?, G.Adj t z)
    (right : ∀ t∈B.head?, G.Adj z t) : m≤J.length := by
  obtain ⟨u,v,r,hr,supp⟩ := splice_path p hp A J B split (Walk.nil : G.Walk z z) (by simp)
    (by simpa [List.disjoint_left] using off) left right
  have contains : z∈r.support := by simp [supp]
  have gap := miss r hr contains
  rw [supp] at gap
  rw [split] at size
  simp only [Walk.support_nil,List.length_append,List.length_singleton] at gap size
  omega

private theorem singleton_prefix (p : G.Walk x y) (hp : p.IsPath)
    {z : V} (off : z∉p.support) (size : p.support.length+1=Fintype.card V) {m : ℕ}
    (miss : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z∈r.support → r.support.length+m ≤ Fintype.card V)
    (i : Fin p.support.length)
    (contact : G.Adj z p.support[i.val]) : m ≤ i.val := by
  let L := p.support
  have head : (L.drop i.val).head? = some L[i.val] := by
    simp [List.head?_drop]
  have gap := singleton_gap p hp off size miss [] (L.take i.val) (L.drop i.val)
    (by simp [L]) (by simp) (by
      intro z hz
      rw [head] at hz
      have eq : L[i.val] = z := by simpa using hz
      exact eq ▸ contact)
  have small := List.length_take_le i.val L
  omega

/-- An exterior detour starting at the last specified mark replaces the following suffix. -/
private theorem singleton_suffix (p : G.Walk x y) (hp : p.IsPath)
    {z : V} (off : z∉p.support) (size : p.support.length+1=Fintype.card V) {m : ℕ}
    (miss : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z∈r.support → r.support.length+m ≤ Fintype.card V)
    (i : Fin p.support.length)
    (contact : G.Adj p.support[i.val] z) : i.val + 1 + m ≤ p.support.length := by
  let L := p.support
  have last : (L.take (i.val+1)).getLast? = some L[i.val] := by
    exact (congrArg List.getLast? (List.take_succ_eq_append_getElem
      (l := L) (i := i.val) i.isLt)).trans List.getLast?_concat
  have gap := singleton_gap p hp off size miss (L.take (i.val+1)) (L.drop (i.val+1)) []
    (by simp [L]) (by
      intro z hz
      rw [last] at hz
      have eq : L[i.val] = z := by simpa using hz
      exact eq ▸ contact) (by simp)
  simp only [L,List.length_drop] at gap
  have hi := i.isLt
  omega

/-- Every pair of distinct marked positions bounds a gap able to absorb a disjoint detour. -/
private theorem singleton_interval (p : G.Walk x y) (hp : p.IsPath)
    {z : V} (off : z∉p.support) (size : p.support.length+1=Fintype.card V) {m : ℕ}
    (miss : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z∈r.support → r.support.length+m ≤ Fintype.card V)
    (i j : Fin p.support.length) (hij : i<j)
    (left : G.Adj p.support[i.val] z) (right : G.Adj z p.support[j.val]) :
    i.val+1+m ≤ j.val := by
  let L := p.support
  let gap := j.val-(i.val+1)
  have ij : i.val+1+gap=j.val := by
    change i.val < j.val at hij
    dsimp [gap]
    omega
  have split : L = L.take (i.val+1) ++ (L.drop (i.val+1)).take gap ++ L.drop j.val := by
    rw [←List.take_add,ij,List.take_append_drop]
  have last : (L.take (i.val+1)).getLast? = some L[i.val] := by
    exact (congrArg List.getLast? (List.take_succ_eq_append_getElem
      (l := L) (i := i.val) i.isLt)).trans List.getLast?_concat
  have head : (L.drop j.val).head? = some L[j.val] := by
    simp [List.head?_drop]
  have bound := singleton_gap p hp off size miss _ _ _ split (by
    intro z hz
    rw [last] at hz
    have eq : L[i.val] = z := by simpa using hz
    exact eq ▸ left) (by
    intro z hz
    rw [head] at hz
    have eq : L[j.val] = z := by simpa using hz
    exact eq ▸ right)
  have small := List.length_take_le gap (L.drop (i.val+1))
  omega


variable [DecidableEq V] [DecidableRel G.Adj]

/-- A path spanning the complement of the least-degree vertex gives one long
gap for each mark and one more for its second tail, at arbitrary minimum degree. -/
theorem order_of_rooted_gap (z : V) (positive : 1≤G.degree z) {m : ℕ}
    (miss : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z∈r.support → r.support.length+m≤Fintype.card V)
    {u v : {t : V | t≠z}} (q : (G.induce {t : V | t≠z}).Walk u v) (hq : q.IsHamiltonian) :
    (G.degree z+1)*(m+1) ≤ Fintype.card V := by
  classical
  let S := {t : V | t≠z}
  let f := (Embedding.induce (G:=G) S).toHom
  let p := q.map f
  have hp : p.IsPath := hq.isPath.map Subtype.val_injective
  have supp : p.support=List.map Subtype.val q.support := Walk.support_map f q
  have outside : z ∉ p.support := by
    rw [supp]
    rintro h
    obtain ⟨a,_,e⟩ := List.mem_map.mp h
    exact a.property e
  have on (a : V) (ha : a≠z) : a∈p.support := by
    rw [supp]
    exact List.mem_map.mpr ⟨⟨a,ha⟩,hq.mem_support _,rfl⟩
  have eq : insert z p.support.toFinset=univ := by
    ext a
    simp only [mem_insert, List.mem_toFinset, mem_univ, iff_true]
    exact em (a=z) |>.imp_right (on a)
  have size : p.support.length+1 = Fintype.card V := by
    have c := congrArg Finset.card eq
    rwa [card_insert_of_notMem (fun h => outside (List.mem_toFinset.mp h)),
      List.toFinset_card_of_nodup hp.support_nodup,card_univ] at c
  have sub : G.neighborFinset z ⊆ p.support.toFinset := fun a ha =>
    List.mem_toFinset.mpr (on a ((G.mem_neighborFinset z a).mp ha).ne.symm)
  let A := contactPositions p z
  have count : A.card=G.degree z := by
    rw [show A=contactPositions p z from rfl,contact_card_neighbors p hp z,inter_eq_left.mpr sub,
      G.card_neighborFinset_eq_degree]
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le positive
  have same : A.card=d+1 := by omega
  let mark := A.orderEmbOfFin same
  have contact (i : Fin (d+1)) : mark i < p.support.length ∧ G.Adj (p.getVert (mark i)) z :=
    (mem_contactPositions p z _).mp (A.orderEmbOfFin_mem same i)
  have first := singleton_prefix p hp outside size miss ⟨mark 0,(contact 0).1⟩
    (by simpa [get_at] using (contact 0).2.symm)
  have last := singleton_suffix p hp outside size miss ⟨mark (Fin.last d),(contact _).1⟩
    (by simpa [get_at] using (contact (Fin.last d)).2)
  have span (i : Fin (d+1)) : m+i.val*(m+1) ≤ mark i := by
    induction i using Fin.induction with
    | zero => simpa using first
    | succ i ih =>
      have gap := singleton_interval p hp outside size miss
        ⟨mark i.castSucc,(contact _).1⟩ ⟨mark i.succ,(contact _).1⟩ (mark.strictMono i.castSucc_lt_succ)
        (by simpa [get_at] using (contact i.castSucc).2)
        (by simpa [get_at] using (contact i.succ).2.symm)
      change mark i.castSucc+1+m ≤ mark i.succ at gap
      simp only [Fin.val_succ,Fin.val_castSucc,Nat.succ_mul] at ih ⊢
      omega
  have bound := span (Fin.last d)
  simp only [Fin.val_last] at bound
  change mark (Fin.last d)+1+m ≤ p.support.length at last
  have eqd : G.degree z+1=d+2 := by omega
  rw [eqd]
  nlinarith

theorem order_of_minimum_deletion_hamiltonian [Nontrivial V] (z : V) (least : G.degree z = G.minDegree)
    (notTrace : ¬ ∃ a b, ∃ q : G.Walk a b, q.IsHamiltonian)
    (positive : 1≤G.degree z) (kpos : 1≤G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    {u v : {t : V | t≠z}} (q : (G.induce {t : V | t≠z}).Walk u v) (hq : q.IsHamiltonian) :
    (G.degree z+1)*(G.secondSmallestDegree/2+2) ≤ Fintype.card V := by
  have bound := order_of_rooted_gap z positive (m:=G.secondSmallestDegree/2+1)
    (fun r hr on => by simpa [Nat.add_assoc] using rooted_omission z least notTrace kpos cap r hr on) q hq
  exact bound

/-- The same baseline or lifted order conclusion holds directly for traceable
minimum deletion when the original minimum degree is at least 2λ+1. -/
theorem cone_order_of_hamiltonian_minimum_deletion [Nontrivial V] (z : V) (least : G.degree z=G.minDegree)
    (notTrace : ¬ ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian)
    {l : ℕ} (room : 2*l+1≤G.degree z) (kpos : 1≤G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    {u v : {b : V | b≠z}} (q : (G.induce {b : V | b≠z}).Walk u v) (hq : q.IsHamiltonian) :
    (l+1)*(G.secondSmallestDegree-l+2)-1 ≤ Fintype.card V := by
  have bound := order_of_minimum_deletion_hamiltonian z least notTrace (by omega) kpos cap q hq
  have first : G.secondSmallestDegree-l+2 ≤ 2*(G.secondSmallestDegree/2+2) := by omega
  have steps := Nat.mul_le_mul_left (l+1) first
  have monotone := Nat.mul_le_mul_right (G.secondSmallestDegree/2+2) (show (l+1)*2≤G.degree z+1 by omega)
  rw [←Nat.mul_assoc] at steps
  omega

#print axioms cone_order_of_hamiltonian_minimum_deletion
#print axioms order_of_rooted_gap
#print axioms order_of_minimum_deletion_hamiltonian
end Graph189RootedSplice
