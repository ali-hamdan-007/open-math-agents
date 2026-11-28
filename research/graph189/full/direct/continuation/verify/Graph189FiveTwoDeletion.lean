import Graph189FiveTriangleExchange
import Graph189FiveFourExterior
import Graph189TwoMarkExchange
import Graph189ProtectedUniform
import Graph189LayerCutoff

open SimpleGraph Finset Graph189ExteriorGap
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189FiveTwoDeletion
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem exterior_data {u v : V} (p : G.Walk u v) (hp : p.IsPath) (t : Fin p.support.length)
    (mx : ∀ {a b}, ∀ q : G.Walk a b, q.IsPath → p.support[t.val]∈q.support → q.length≤p.length)
    (low : G.degree p.support[t.val]<G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (k5 : G.secondSmallestDegree=5) (order : Fintype.card V≤16)
    (size : (p.support.toFinsetᶜ : Finset V).card+1=G.secondSmallestDegree) :
    let E := (p.support.toFinsetᶜ : Finset V)
    (∀ x y : E, x≠y → ∃ q : (G.induce (E : Set V)).Walk x y, q.IsHamiltonian) ∧
      ∃ M : Finset (Fin p.support.length), M.card=2 ∧
        ∀ w∈E, ∀ i : Fin p.support.length, G.Adj p.support[i.val] w ↔ i∈M := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  change E.card+1=G.secondSmallestDegree at size
  have out (w : V) (hw : w∈E) : w∉p.support := by simpa [E] using hw
  have routes := Graph189FiveFourExterior.paths p hp t mx low cap k5 order (by omega)
  refine ⟨routes,uniform_contacts_of_order p hp t mx E out (by omega) routes 2 (by omega) (by omega) ?_⟩
  intro w hw
  have high := (degree_pair (G:=G) w p.support[t.val] (fun e => out w hw (e ▸ List.getElem_mem _))).resolve_right (not_le.mpr low)
  have bound := Graph189DenseExteriorOrder.neighbors_on_path p E
    (fun _ _ x _ nx => by simpa [E] using nx) hw
  omega

/-- At second-smallest degree five, any Hamilton path after
deleting a vertex of degree two forces traceability of the original graph. -/
theorem traceable (hc : G.Connected) (z : V) (degree : G.degree z=2)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) (k5 : G.secondSmallestDegree=5)
    {a b : {v : V | v≠z}} (P : (G.induce {v : V | v≠z}).Walk a b) (hP : P.IsHamiltonian) :
    ∃ u v, ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  by_contra nontrace
  let k := G.secondSmallestDegree
  change k=5 at k5
  have order : Fintype.card V ≤ 3*k+1 := by
    have h := Graph189LayerCutoff.order_of_small_degree G hc z k cap (by rw [degree]; omega)
    rw [degree] at h
    omega
  obtain ⟨u,v,p,hp,t,eq,longest⟩ := exists_longest_through G z
  let E := (p.support.toFinsetᶜ : Finset V)
  have mx : ∀ {i j}, ∀ q : G.Walk i j, q.IsPath → p.support[t.val]∈q.support → q.length≤p.length :=
    fun q hq h => longest q hq (eq ▸ h)
  have low : G.degree p.support[t.val]<k := by rw [eq,degree]; omega
  have gap := protected_size_of_traceable_deletion z (by omega) P hP p hp longest
  rw [degree] at gap
  change 1+2+(2+1)*E.card ≤ Fintype.card V at gap
  have present : E.Nonempty := by
    by_contra empty
    apply nontrace
    refine ⟨u,v,p,hp.isHamiltonian_of_mem (fun w => ?_)⟩
    by_contra missing
    exact empty ⟨w,by simpa [E] using missing⟩
  obtain ⟨w,hw⟩ := present
  let witness : E := ⟨w,hw⟩
  have minimum := protected_exterior_minimum p hp t mx low cap witness
  change k/2 ≤ (G.induce (E : Set V)).degree witness at minimum
  have room := (G.induce (E : Set V)).degree_lt_card_verts witness
  change (G.induce (E : Set V)).degree witness<Fintype.card E at room
  rw [Fintype.card_coe] at room
  by_cases triangle : E.card=3
  · exact Graph189FiveTriangleExchange.exclude p hp t mx low cap k5 (by omega) triangle
  have size : E.card+1=k := by omega
  obtain ⟨routes,M,sz,links⟩ := exterior_data p hp t mx low cap k5 (by omega) size
  have total := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at total
  change p.support.length+E.card=Fintype.card V at total
  have common {i j} (r : G.Walk i j) (hr : r.IsPath) (retained : p.support[t.val]∈r.support)
      (same : r.length=p.length) (w : V) (hw : w∈r.support) (x : V) (hx : x∉r.support)
      (y : V) (hy : y∉r.support) (wx : G.Adj w x) : G.Adj w y := by
    have count := card_add_card_compl r.support.toFinset
    rw [List.toFinset_card_of_nodup hr.support_nodup] at count
    have len : r.support.length=p.support.length := by rw [r.length_support,same,←p.length_support]
    obtain ⟨j,hj,atZ⟩ := List.mem_iff_getElem.mp (show z∈r.support from eq ▸ retained)
    let T : Fin r.support.length := ⟨j,hj⟩
    have lo : G.degree r.support[T.val] < k := by change G.degree r.support[j]<k; rw [atZ,degree]; omega
    have mx' : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → r.support[T.val]∈q.support → q.length≤r.length := by
      intro _ _ q hq ht
      rw [same]
      apply longest q hq
      simpa only [T,atZ] using ht
    obtain ⟨_,_,_,both⟩ := exterior_data r hr T mx' lo cap k5 (by omega)
      (by change (r.support.toFinsetᶜ : Finset V).card+1=k; omega)
    obtain ⟨l,hl,ev⟩ := List.mem_iff_getElem.mp hw
    rw [←ev] at wx ⊢
    exact (both y (by simpa using hy) ⟨l,hl⟩).mpr ((both x (by simpa using hx) ⟨l,hl⟩).mp wx)
  apply two_mark_exchange p hp t mx E (by omega) (fun {v} h => by simpa [E] using h)
    routes M sz links common (by omega)
  intro x _
  have h := cap x
  change G.distEven x ≤ k+1 at h
  omega

#print axioms traceable
end Graph189FiveTwoDeletion
