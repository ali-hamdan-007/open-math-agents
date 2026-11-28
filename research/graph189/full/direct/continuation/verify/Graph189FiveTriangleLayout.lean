import Graph189FiveTripleMatching
import Graph189DenseExteriorOrder
import Graph189ProtectedHamiltonConnected
import Graph189PrescribedBatch

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189FiveTriangleLayout
open Graph189FiveTripleMatching
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {u v : V}

private theorem matching_layout (p : G.Walk u v) (hp : p.IsPath) (t : Fin p.support.length)
    (mx : ∀ {a b}, ∀ q : G.Walk a b, q.IsPath → p.support[t.val]∈q.support → q.length≤p.length)
    (E : Finset V) (outside : ∀ a∈E, a∉p.support)
    (routes : ∀ a b : E, a≠b → ExteriorRoute p a.val b.val 3)
    (M : Finset (Fin p.support.length)) (count : M.card=3) (f : M ↪ E)
    (contacts : ∀ i : M, G.Adj p.support[i.val.val] (f i).val) (room : p.support.length≤13) :
    p.support.length=13 ∧ (t.val=0 ∨ t.val=4 ∨ t.val=8 ∨ t.val=12) ∧
    M.image Fin.val=marks t.val := by
  classical
  let A := M.orderEmbOfFin count
  let B := M.orderIsoOfFin count
  let T := fun i : Fin 3 => f (B i)
  have touch (i : Fin 3) : G.Adj p.support[(A i).val] (T i).val := contacts (B i)
  have inj : Function.Injective T := f.injective.comp B.injective
  have lt1 : (A 0).val < (A 1).val := A.strictMono (by decide : (0:Fin 3)<1)
  have lt2 : (A 1).val < (A 2).val := A.strictMono (by decide : (1:Fin 3)<2)
  have pre (safe : (A 0).val≤t.val) : 3≤(A 0).val := by
    obtain ⟨q,hq,dis,len⟩ := routes (T 1) (T 0) (inj.ne (by decide))
    exact len.trans (protected_prefix_of_detour p hp t mx _ safe q hq dis (touch 0).symm)
  have post (safe : t.val≤(A 2).val) : (A 2).val+4≤p.support.length := by
    obtain ⟨q,hq,dis,len⟩ := routes (T 2) (T 0) (inj.ne (by decide))
    have bound := protected_suffix_of_detour p hp t mx _ safe q hq dis (touch 2)
    omega
  have step (i j : Fin 3) (ij : i<j) (safe : (A j).val≤t.val ∨ t.val≤(A i).val) :
      (A i).val+4≤(A j).val := by
    obtain ⟨q,hq,dis,len⟩ := routes (T i) (T j) (inj.ne ij.ne)
    have bd := protected_interval_of_detour p hp t mx _ _ (A.strictMono ij) safe
      q hq dis (touch i) (touch j).symm
    omega
  have first := step 0 1 (by decide)
  have second := step 1 2 (by decide)
  have bound := (A 2).isLt
  obtain ⟨len,pos,pattern⟩ := layout (t:=t.val) room (by constructor <;> omega)
    (by constructor <;> omega) t.isLt pre post first second
  refine ⟨len,pos,?_⟩
  rw [←pattern]
  ext j
  constructor
  · intro h
    obtain ⟨i,hi,rfl⟩ := mem_image.mp h
    have ran : i∈Set.range A := by rwa [show Set.range A=(M : Set _) from M.range_orderEmbOfFin count]
    obtain ⟨q,rfl⟩ := ran
    fin_cases q <;> simp
  · intro h
    simp only [mem_insert,mem_singleton] at h
    rcases h with rfl|rfl|rfl <;> exact mem_image_of_mem _ (M.orderEmbOfFin_mem count _)

/-- Every contact row is the same determined three-element set, also
after replacing a safe gap and making another maximal protected path. -/
theorem data (p : G.Walk u v) (hp : p.IsPath) (t : Fin p.support.length)
    (mx : ∀ {a b}, ∀ q : G.Walk a b, q.IsPath → p.support[t.val]∈q.support → q.length≤p.length)
    (low : G.degree p.support[t.val]<G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    (k5 : G.secondSmallestDegree=5) (order : Fintype.card V≤16)
    (size : (p.support.toFinsetᶜ : Finset V).card=3) :
    let E := (p.support.toFinsetᶜ : Finset V)
    p.support.length=13 ∧ (t.val=0 ∨ t.val=4 ∨ t.val=8 ∨ t.val=12) ∧
    (∀ x y : E, x≠y → ∃ q : (G.induce (E : Set V)).Walk x y, q.IsHamiltonian) ∧
    ∀ x∈E, contactPositions p x=marks t.val := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  let F := G.induce (E : Set V)
  change E.card=3 at size
  have out (w : V) (h : w∈E) : w∉p.support := by simpa [E] using h
  have half (x : E) : 2≤F.degree x := by
    have h := protected_exterior_minimum p hp t mx low cap x
    simpa only [k5] using h
  have paths (x y : E) (ne : x≠y) : ∃ q : F.Walk x y, q.IsHamiltonian := by
    apply Graph189TerminalLeafClosure.prescribed_of_supergraph (G:=F) le_top _
      (Graph189TerminalLeafClosure.complete_prescribed x y ne)
    intro a b _ _
    change Fintype.card E+1≤F.degree a+F.degree b
    rw [Fintype.card_coe,size]
    have := half a
    have := half b
    omega
  have routes (x y : E) (ne : x≠y) : ExteriorRoute p x.val y.val 3 := by
    obtain ⟨q,hq⟩ := paths x y ne
    simpa only [size] using route_of_induced_hamilton p E out hq
  let N (x : V) := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] x)
  have many (w : V) (hw : w∈E) : 3≤(N w).card := by
    have hi := (OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G)
      w p.support[t.val] (fun eq => out w hw (eq ▸ List.getElem_mem _))).resolve_right (not_le.mpr low)
    have bound := Graph189DenseExteriorOrder.neighbors_on_path p E
      (fun _ _ v _ miss => by simpa [E] using miss) hw
    change G.degree w+1≤E.card+(N w).card at bound
    omega
  have total := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at total
  change p.support.length+E.card=Fintype.card V at total
  have classify (x : E) {j : Fin p.support.length} (h : j∈N x.val) :
      p.support.length=13 ∧ (t.val=0 ∨ t.val=4 ∨ t.val=8 ∨ t.val=12) ∧ j.val∈marks t.val := by
    obtain ⟨M,count,inside,f,edges⟩ := forced p E size x j (mem_filter.mp h).2
      (fun y _ => many _ y.property)
    obtain ⟨len,pos,eq⟩ := matching_layout p hp t mx E out routes M count f edges (by omega)
    exact ⟨len,pos,eq ▸ mem_image_of_mem Fin.val inside⟩
  obtain ⟨w,hw⟩ := card_pos.mp (show 0<E.card by omega)
  obtain ⟨i,hi⟩ := card_pos.mp (show 0<(N w).card by have := many w hw; omega)
  obtain ⟨len,pos,_⟩ := classify ⟨w,hw⟩ hi
  refine ⟨len,pos,paths,?_⟩
  intro x hx
  have image : (N x).image Fin.val=contactPositions p x := by
    ext j
    constructor
    · intro h
      obtain ⟨i,hi,rfl⟩ := mem_image.mp h
      exact (mem_contactPositions p x _).mpr ⟨i.isLt,by simpa [get_at] using (mem_filter.mp hi).2⟩
    · intro h
      obtain ⟨hj,edge⟩ := (mem_contactPositions p x j).mp h
      exact mem_image.mpr ⟨⟨j,hj⟩,mem_filter.mpr ⟨mem_univ _,by simpa [get_at] using edge⟩,rfl⟩
  rw [←image]
  apply eq_of_subset_of_card_le
  · intro j hj
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hj
    exact (classify ⟨x,hx⟩ hi).2.2
  · rw [card_image_of_injective _ Fin.val_injective]
    have count : (marks t.val).card=3 := by
      rcases pos with h|h|h|h <;> rw [h] <;> decide
    rw [count]
    exact many x hx

#print axioms data
end Graph189FiveTriangleLayout
