import Graph189ContactIntervals
import Graph189ProtectedIntervals
import Graph189NearFinal

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189ContactGroupCensus
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {x y : V}

/-- The private/shared grouping from lowblock/all-near-spanning.md gives the same marks in a longest protected path with little order
slack. This allows the critical case u=|E|. -/
theorem uniform_of_protected_census (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → p.support[t.val]∈r.support → r.length≤p.length)
    (E : Finset V) (outside : ∀ v∈E, v∉p.support)
    (routes : ∀ a b : E, a≠b → ∃ h : (G.induce (E : Set V)).Walk a b, h.IsHamiltonian)
    (u : ℕ) (two : 2≤u) (balanced : u≤E.card)
    (rows : ∀ v : E, u≤(contactPositions p v.val).card)
    (room : p.support.length+E.card+2≤(u+1)*(E.card+1)+u) :
    ∃ A : Finset ℕ, A.card=u ∧ ∀ v : E, contactPositions p v.val=A := by
  classical
  let A : Finset ℕ := univ.biUnion fun v : E => contactPositions p v.val
  let q := A.card
  let mark := A.orderEmbOfFin (show A.card=q from rfl)
  have find (j : ℕ) (hj : j∈A) : ∃ i, mark i=j := by
    let iso := A.orderIsoOfFin (show A.card=q from rfl)
    exact ⟨iso.symm ⟨j,hj⟩,congrArg Subtype.val (iso.apply_symm_apply ⟨j,hj⟩)⟩
  have real (i : Fin q) : mark i<p.support.length := by
    obtain ⟨v,_,hit⟩ := mem_biUnion.mp (A.orderEmbOfFin_mem rfl i)
    exact ((mem_contactPositions p v.val _).mp hit).1
  let F (i : Fin q) : Fin p.support.length := ⟨mark i,real i⟩
  let ports (i : Fin q) := (univ : Finset E).filter fun v => mark i∈contactPositions p v.val
  have present (i) : (ports i).Nonempty := by
    obtain ⟨v,_,hit⟩ := mem_biUnion.mp (A.orderEmbOfFin_mem rfl i)
    exact ⟨v,mem_filter.mpr ⟨mem_univ _,hit⟩⟩
  have touch {i} {a : E} (h : a∈ports i) : G.Adj p.support[(F i).val] a.val := by
    have e := ((mem_contactPositions p a.val _).mp (mem_filter.mp h).2).2
    change G.Adj p.support[mark i] a.val
    rwa [get_at p (real i)]
  have rowImage (v : E) : (univ.filter fun i => v∈ports i).image mark = contactPositions p v.val := by
    ext a
    constructor
    · intro h
      obtain ⟨i,hi,rfl⟩ := mem_image.mp h
      exact (mem_filter.mp (mem_filter.mp hi).2).2
    · intro h
      obtain ⟨i,val⟩ := find a (mem_biUnion.mpr ⟨v,mem_univ _,h⟩)
      exact mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,mem_filter.mpr ⟨mem_univ _,by simpa [val] using h⟩⟩,val⟩
  have counts (v : E) : u≤(univ.filter fun i => v∈ports i).card := by
    have size := congrArg Finset.card (rowImage v)
    rw [card_image_of_injective _ mark.injective] at size
    rw [size]
    exact rows v
  have exterior : 1<(univ : Finset E).card := by simpa using (show 1<E.card by omega)
  obtain ⟨one,_⟩ := card_pos.mp (by omega : 0<(univ : Finset E).card)
  have qpos : 0<q := by
    have := counts one
    have upper := card_le_card (subset_univ (univ.filter fun i => one∈ports i))
    simp only [card_univ,Fintype.card_fin] at upper
    omega
  have other (a : E) : ∃ b : E, b≠a := by
    obtain ⟨b,_,ne⟩ := exists_mem_ne exterior a
    exact ⟨b,ne⟩
  have route (a b : E) (ne : a≠b) : ExteriorRoute p a.val b.val E.card := by
    obtain ⟨r,hr⟩ := routes a b ne
    exact route_of_induced_hamilton p E outside hr
  let f : ℕ→ℕ
    | 0 => 0
    | i+1 => if h : i<q then mark ⟨i,h⟩+1 else p.support.length+1
  have ending : f (q+1)=p.support.length+1 := by simp [f]
  have strict (i j : ℕ) (lt : i<j) (le : j≤q+1) : f i<f j := by
    cases j with
    | zero => omega
    | succ j =>
      cases i with
      | zero =>
        simp only [f]
        split <;> omega
      | succ i =>
        have iq : i<q := by omega
        simp only [f,dif_pos iq]
        split <;> rename_i h
        · have lower := mark.strictMono (show (⟨i,iq⟩ : Fin q)<⟨j,h⟩ by change i<j; omega)
          omega
        · have lower := real ⟨i,iq⟩
          omega
  have detour (i : ℕ) (eligible : i∈insert q ((beginnings ports).image Fin.val))
      (keep : t.val<f i ∨ f (i+1)≤t.val+1) : E.card≤f (i+1)-f i-1 := by
    rcases mem_insert.mp eligible with rfl|start
    · let j : Fin q := ⟨q-1,by omega⟩
      have pos : f q=mark j+1 := by
        have next : q=q-1+1 := by omega
        conv_lhs => rw [next]
        simp [f,j,show q-1<q by omega]
      rw [pos,ending] at keep ⊢
      obtain ⟨a,hit⟩ := present j
      obtain ⟨b,ne⟩ := other a
      obtain ⟨r,hr,dis,len⟩ := route a b ne.symm
      have left : t≤F j := by change t.val≤mark j; have := t.isLt; omega
      have bound := protected_suffix_of_detour p hp t longest (F j) left r hr dis (touch hit)
      change mark j+1+r.support.length≤p.support.length at bound
      omega
    obtain ⟨k,inB,rfl⟩ := mem_image.mp start
    have right : f (k.val+1)=mark k+1 := by simp [f,k.isLt]
    rw [right] at keep ⊢
    by_cases first : k.val=0
    · have left : f k.val=0 := by simp [first,f]
      rw [left] at keep ⊢
      obtain ⟨a,hit⟩ := present k
      obtain ⟨b,ne⟩ := other a
      obtain ⟨r,hr,dis,len⟩ := route b a ne
      have inside : F k≤t := by change mark k≤t.val; omega
      have bound := protected_prefix_of_detour p hp t longest (F k) inside r hr dis (touch hit).symm
      change r.support.length≤mark k at bound
      omega
    let j : Fin q := ⟨k.val-1,by have := k.isLt; omega⟩
    have prev : j.val+1=k.val := by change k.val-1+1=k.val; omega
    have left : f k.val=mark j+1 := by
      rw [←prev]
      simp [f,j.isLt]
    rw [left] at keep ⊢
    obtain ⟨a,ha,b,hb,ne⟩ := (mem_filter.mp inB).2 j prev
    obtain ⟨r,hr,dis,len⟩ := route a b ne
    have ordered : F j<F k := mark.strictMono (show j<k by change j.val<k.val; omega)
    have safe : F k≤t ∨ t≤F j := by change mark k≤t.val ∨ t.val≤mark j; omega
    have bound := protected_interval_of_detour p hp t longest _ _ ordered safe r hr dis (touch ha) (touch hb).symm
    change mark j+1+r.support.length≤mark k at bound
    omega
  have chart := path_group_census ports f t.val rfl ending strict (by omega : 1≤E.card) detour
  have actual : Fintype.card E=E.card := Fintype.card_coe E
  obtain ⟨size,_⟩ := rows_uniform ports present u two (by rwa [actual]) counts (by rw [actual]; omega)
  refine ⟨A,size,?_⟩
  intro v
  apply eq_of_subset_of_card_le (fun i h => mem_biUnion.mpr ⟨v,mem_univ _,h⟩)
  change q≤_
  rw [size]
  exact rows v

end Graph189ContactGroupCensus
