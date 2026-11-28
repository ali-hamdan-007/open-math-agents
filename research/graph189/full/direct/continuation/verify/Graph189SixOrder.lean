import Graph189SixExterior
import Graph189UpstreamShortOrder
import Graph189LayerCutoff

open Finset SimpleGraph Graph189ExteriorGap
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R2
namespace Graph189SixOrder
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The short-order path lower bound of @carl2sheriff and the five-vertex
exterior exchange give the original conjecture at degree six through order nineteen. -/
theorem of_deletions (hc : G.Connected)
    (bound : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (six : G.secondSmallestDegree=6) (order : Fintype.card V≤19)
    (hn : 2*G.secondSmallestDegree+3≤Fintype.card V) (uncut : ∀ c : V, (G.induce {v : V | v≠c}).Connected) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have upper (v : V) : G.distEven v≤1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans bound
  have cap (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by simpa only [Nat.add_comm] using upper v
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  have hmin (v : V) : G.degree z≤G.degree v := by rw [←hz]; exact G.minDegree_le_degree v
  have high := b25_hx0 (G:=G) hmin
  obtain ham | ⟨l,hne,hnd,hch,hmem,hhd,hlast,hmax,hlt⟩ := Cadre.exists_cadre hc upper hn hmin
  · exact ham
  exfalso
  have minLength := Cadre.m_ge hc uncut upper hmin high (h11 hc upper hn) hne hnd hch hmem hhd hlast hmax hlt
  let p := Walk.ofSupport l hne hch
  have supp : p.support=l := Walk.support_ofSupport hne hch
  have hp : p.IsPath := Walk.IsPath.mk' (by rwa [supp])
  have contains : z∈p.support := by rwa [supp]
  obtain ⟨i,hi,atZ⟩ := List.mem_iff_getElem.mp contains
  let t : Fin p.support.length := ⟨i,hi⟩
  have eq : p.support[t.val]=z := atZ
  have longest {a b} (q : G.Walk a b) (hq : q.IsPath) (seen : z∈q.support) : q.length≤p.length := by
    have h := hmax q.support hq.support_nodup q.isChain_adj_support seen
    rw [←supp,q.length_support,p.length_support] at h
    omega
  have mx : ∀ {a b}, ∀ q : G.Walk a b, q.IsPath → p.support[t.val]∈q.support → q.length≤p.length :=
    fun q hq h => longest q hq (eq ▸ h)
  let E := (p.support.toFinsetᶜ : Finset V)
  have total := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at total
  change p.support.length+E.card=Fintype.card V at total
  rw [←supp] at minLength hlt
  have nonempty : E.Nonempty := card_pos.mp (by omega)
  obtain ⟨size,routes,M,sz,links⟩ := Graph189SixExterior.data p hp t mx six order cap
    (fun miss => high _ (fun e => miss (by simpa only [e] using contains))) nonempty (by change E.card≤5; omega)
  change E.card=5 at size
  have common {i j} (r : G.Walk i j) (hr : r.IsPath) (retained : p.support[t.val]∈r.support)
      (same : r.length=p.length) (w : V) (hw : w∈r.support) (x : V) (hx : x∉r.support)
      (y : V) (hy : y∉r.support) (wx : G.Adj w x) : G.Adj w y := by
    have count := card_add_card_compl r.support.toFinset
    rw [List.toFinset_card_of_nodup hr.support_nodup] at count
    have len : r.support.length=p.support.length := by rw [r.length_support,same,←p.length_support]
    have keep : z∈r.support := eq ▸ retained
    obtain ⟨j,hj,atZ⟩ := List.mem_iff_getElem.mp keep
    let T : Fin r.support.length := ⟨j,hj⟩
    have mx' : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → r.support[T.val]∈q.support → q.length≤r.length := by
      intro _ _ q hq ht
      rw [same]
      apply longest q hq
      simpa only [T,atZ] using ht
    obtain ⟨_,_,_,_,both⟩ := Graph189SixExterior.data r hr T mx' six order cap
      (fun miss => high _ (fun e => miss (by simpa only [e] using keep))) (card_pos.mp (by omega)) (by omega)
    obtain ⟨l,hl,ev⟩ := List.mem_iff_getElem.mp hw
    rw [←ev] at wx ⊢
    exact (both y (by simpa using hy) ⟨l,hl⟩).mpr ((both x (by simpa using hx) ⟨l,hl⟩).mp wx)
  exact two_mark_exchange p hp t mx E (by omega) (fun {v} h => by simpa [E] using h)
    routes M sz links common (by omega) (by intro v _; have := cap v; omega)

/-- The short-order path lower bound of @carl2sheriff and the five-vertex
exterior exchange give the original conjecture at degree six through order nineteen. -/
theorem traceable (hc : G.Connected)
    (bound : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (six : G.secondSmallestDegree=6) (order : Fintype.card V≤19) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have upper (v : V) : G.distEven v≤1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans bound
  by_cases short : Fintype.card V≤2*G.secondSmallestDegree+2
  · exact OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.theorem_C hc upper short
  have hn : 2*G.secondSmallestDegree+3≤Fintype.card V := by omega
  by_cases uncut : ∀ c : V, (G.induce {v : V | v≠c}).Connected
  swap
  · push Not at uncut
    exact Graph189CutH1.cut_vertex_case G hc upper hn uncut
  exact of_deletions hc bound six order hn uncut

/-- A degree-two vertex forces the order into this entire verified range. -/
theorem traceable_degree_two (hc : G.Connected)
    (bound : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (six : G.secondSmallestDegree=6) (z : V) (deg : G.degree z=2) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have cap (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    have upper := (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans bound
    omega
  have order := Graph189LayerCutoff.order_of_small_degree G hc z _ cap (by omega)
  rw [six,deg] at order
  exact traceable hc bound six (by omega)

#print axioms traceable
#print axioms traceable_degree_two
end Graph189SixOrder
