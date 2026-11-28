import Graph189NearFinal

open Finset SimpleGraph Graph189ExteriorGap

namespace Graph189RootedSplice

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Nontrivial V] [DecidableRel G.Adj] in
private theorem omitted_and_path_order {x y : V} (p : G.Walk x y) (path : p.IsPath) :
    (univ \ p.support.toFinset).card+p.support.length=Fintype.card V := by
  have h := card_sdiff_add_card_inter (univ : Finset V) p.support.toFinset
  rwa [univ_inter,List.toFinset_card_of_nodup path.support_nodup,card_univ] at h

/-- In a nontraceable graph with a Hamiltonian minimum deletion, the exterior
matching allowance of a rooted longest path strictly exceeds the minimum degree. -/
theorem strict_matching_allowance (connected : G.Connected) (z : V)
    (least : G.degree z=G.minDegree) (three : 3≤G.degree z) (k5 : 5≤G.secondSmallestDegree)
    (nontrace : ¬ ∃ a b, ∃ q : G.Walk a b, q.IsHamiltonian)
    (cap : ∀ w, G.distEven w≤G.secondSmallestDegree+1)
    {a b : {w : V | w≠z}} (r : (G.induce {w : V | w≠z}).Walk a b) (hr : r.IsHamiltonian)
    {x y : V} (q : G.Walk x y) (hq : q.IsPath) (on : z∈q.support)
    (longest : ∀ {c d}, ∀ p : G.Walk c d, p.IsPath → z∈p.support → p.length≤q.length) :
    G.degree z < G.secondSmallestDegree+1-(univ \ q.support.toFinset).card := by
  classical
  let k := G.secondSmallestDegree
  let d := G.degree z
  let n := Fintype.card V
  let m := (univ \ q.support.toFinset).card
  obtain ⟨half,budget,_⟩ := near_spanning_rooted_exterior connected z least three k5 nontrace cap r hr q hq on longest
  change 2*d≤k at half
  change m≤k+1-d at budget
  change d<k+1-m
  by_contra! upperBudget
  have sameSize : m=k+1-d := by omega
  have positive : 1≤m := by omega
  have exactSize : m+q.support.length=n := omitted_and_path_order q hq
  have allMax {u v} (t : G.Walk u v) (ht : t.IsPath) (hz : z∈t.support) :
      t.support.length+m≤n := by
    have bound := longest t ht hz
    have tl := t.length_support
    have ql := q.length_support
    omega
  have upper := Graph189LayerCutoff.order_of_small_degree G connected z k cap (by omega)
  change n≤1+d+k+d*(k+1-d) at upper
  rw [←sameSize] at upper
  have nBound : n≤(d+1)*m+2*d := by
    have eq : m+d=k+1 := by omega
    nlinarith only [upper,eq]
  let p := r.map (Embedding.induce (G:=G) {w : V | w≠z}).toHom
  have path : p.IsPath := hr.isPath.map Subtype.val_injective
  have supp : p.support=List.map Subtype.val r.support := Walk.support_map _ r
  have absent : z∉p.support := by
    rw [supp]
    intro hz
    obtain ⟨v,_,eq⟩ := List.mem_map.mp hz
    exact v.property eq
  have inside (w : V) (ne : w≠z) : w∈p.support := by
    rw [supp]
    exact List.mem_map.mpr ⟨⟨w,ne⟩,hr.mem_support _,rfl⟩
  have cover : insert z p.support.toFinset=univ := by
    ext w
    simp only [mem_insert,List.mem_toFinset,mem_univ,iff_true]
    exact (em (w=z)).imp_right (inside w)
  have near : p.support.length+1=n := by
    have sz := congrArg Finset.card cover
    rwa [card_insert_of_notMem (fun h => absent (List.mem_toFinset.mp h)),List.toFinset_card_of_nodup path.support_nodup,card_univ] at sz
  have marks : (contactPositions p z).card=d := by
    have sub : G.neighborFinset z⊆p.support.toFinset := fun w hw =>
      List.mem_toFinset.mpr (inside w ((G.mem_neighborFinset _ _).mp hw).ne.symm)
    rw [contact_card_neighbors p path z,inter_eq_left.mpr sub,G.card_neighborFinset_eq_degree]
  obtain ⟨g,h,disjoint⟩ := two_tight_contact_gaps p path z absent near m positive (by omega)
    (by rw [marks]; exact nBound) allMax
  have even := two_tight_gaps_force_cap p path z absent near g h disjoint (cap z) (by
    intro i j t ht member total
    have len : t.length=q.length := by
      have tl := t.length_support
      have ql := q.length_support
      change t.support.length+m=n at total
      omega
    have maximal {u v} (w : G.Walk u v) (hw : w.IsPath) (hz : z∈w.support) : w.length≤t.length := by
      rw [len]
      exact longest w hw hz
    have cardEq : (univ \ t.support.toFinset).card=m := by
      have h := omitted_and_path_order t ht
      omega
    have uniform := common_marks_of_large_exterior connected z least three k5 nontrace cap r hr t ht member maximal
    obtain ⟨T,_,same⟩ := uniform (by
      change k+1-(univ \ t.support.toFinset).card < (univ \ t.support.toFinset).card
      rw [cardEq]
      omega)
    intro a aOut b bOut w hw edge
    obtain ⟨j,valid,eq⟩ := List.mem_iff_getElem.mp hw
    have hit : t.getVert j=w := (get_at t valid).symm.trans eq
    have wa : a∈univ \ t.support.toFinset := mem_sdiff.mpr ⟨mem_univ _,fun h => aOut (List.mem_toFinset.mp h)⟩
    have wb : b∈univ \ t.support.toFinset := mem_sdiff.mpr ⟨mem_univ _,fun h => bOut (List.mem_toFinset.mp h)⟩
    have ai : j∈contactPositions t a := (mem_contactPositions t a j).mpr ⟨valid,hit ▸ edge⟩
    have ae : contactPositions t a=T := same ⟨a,wa⟩
    have be : contactPositions t b=T := same ⟨b,wb⟩
    rw [ae,←be] at ai
    have bi := ((mem_contactPositions t b j).mp ai).2
    rwa [hit] at bi)
  omega

/-- A Hamiltonian minimum deletion in a counterexample gives the order
bound at one index beyond the minimum degree, and every smaller index. -/
theorem order_of_hamiltonian_deletion_up_to_succ_degree (connected : G.Connected) (z : V)
    (least : G.degree z=G.minDegree) (three : 3≤G.degree z) (k5 : 5≤G.secondSmallestDegree)
    (nontrace : ¬ ∃ a b, ∃ q : G.Walk a b, q.IsHamiltonian)
    (cap : ∀ w, G.distEven w≤G.secondSmallestDegree+1)
    {a b : {w : V | w≠z}} (r : (G.induce {w : V | w≠z}).Walk a b) (hr : r.IsHamiltonian)
    (index : ℕ) (bound : index≤G.degree z+1) :
    (index+1)*(G.secondSmallestDegree-index+2)-1≤Fintype.card V := by
  obtain ⟨a,b,q,hq,on,longest⟩ := exists_longest_containing G z
  have strict := strict_matching_allowance connected z least three k5 nontrace cap r hr q hq on longest
  obtain ⟨_,_,order⟩ := rooted_matching_cone_order connected z least three k5 nontrace cap r hr q hq on longest
  exact order index (by omega)

/-- If a Hamiltonian minimum deletion omits a vertex of degree strictly
below a third of the second-smallest degree, the graph itself is traceable. -/
theorem traceable_of_small_degree_hamiltonian_deletion (connected : G.Connected) (z : V)
    (least : G.degree z=G.minDegree) (three : 3≤G.degree z)
    (small : 3*G.degree z<G.secondSmallestDegree)
    (cap : ∀ w, G.distEven w≤G.secondSmallestDegree+1)
    {a b : {w : V | w≠z}} (r : (G.induce {w : V | w≠z}).Walk a b) (hr : r.IsHamiltonian) :
    ∃ a b, ∃ q : G.Walk a b, q.IsHamiltonian := by
  by_contra nontrace
  let d := G.degree z
  let k := G.secondSmallestDegree
  let n := Fintype.card V
  change 3*d<k at small
  have k5 : 5≤k := by omega
  have lower := order_of_hamiltonian_deletion_up_to_succ_degree connected z least three k5 nontrace cap r hr
    (d+1) (by omega)
  have upper := Graph189LayerCutoff.order_of_small_degree G connected z k cap (by omega)
  change (d+2)*(k-(d+1)+2)-1≤n at lower
  change n≤1+d+k+d*(k+1-d) at upper
  have h : k-(d+1)+2=k+1-d := by omega
  rw [h,add_mul] at lower
  omega

#print axioms strict_matching_allowance
#print axioms order_of_hamiltonian_deletion_up_to_succ_degree
#print axioms traceable_of_small_degree_hamiltonian_deletion

end Graph189RootedSplice
