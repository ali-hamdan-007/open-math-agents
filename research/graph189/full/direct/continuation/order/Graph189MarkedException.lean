import Graph189MarkedRotation
import Graph189MarkedLowCut
import Graph189SidePathDegree

open SimpleGraph Finset
namespace Graph189MarkedException
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Start at a genuine mark on a side with one exceptional degree. If its
deletion disconnects the side, the marked two-piece lemma covers the side.
Otherwise at most two vertices in the high part, and the exception, are lost. -/
theorem route (hc : G.Connected) (z : V) (P : Finset V) {d : ℕ} (large : 3≤d)
    (minimum : ∀ v, v≠z → d+1≤G.degree v) (bound : Fintype.card V≤2*d+3)
    (marks : 3≤(P.erase z).card) :
    ∃ x∈P, ∃ y, ∃ p : G.Walk x y,p.IsPath ∧ Fintype.card V≤p.support.length+3 := by
  classical
  let W := (univ : Finset V).erase z
  have size : W.card+1=Fintype.card V := by simpa [W] using card_erase_add_one (s:=univ) (mem_univ z)
  let H := G.induce (W:Set V)
  by_cases con : H.Connected
  swap
  · have same : {v : V | v∉({z}:Finset V)}=(W:Set V) := by ext v; simp [W]
    have cut : ¬(G.induce {v : V | v∉({z}:Finset V)}).Connected := by rwa [same]
    obtain ⟨x,xP,y,p,hp⟩ := Graph189MarkedLowCut.of_cut hc z P (by omega : 2≤d) minimum (by omega) marks cut
    exact ⟨x,xP,y,p,hp.isPath,by have h := hp.length_support; omega⟩
  let T := (P.erase z).subtype (fun v => v∈W)
  have countT : T.card=(P.erase z).card := by
    change ((P.erase z).subtype (fun v => v∈W)).card=_
    rw [card_subtype,filter_eq_self.mpr (fun x hx => mem_erase.mpr ⟨(mem_erase.mp hx).1,mem_univ _⟩)]
  have fit := card_le_univ T
  rw [Fintype.card_coe] at fit
  letI : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_coe]; omega)
  have minH (x : W) : d≤H.degree x := by
    have h := minimum x.val (mem_erase.mp x.property).1
    have keep := Graph189DenseSideRoute.retained (G:=G) W {z} (fun a _ y _ miss => by
      by_contra absent
      exact miss (mem_erase.mpr ⟨fun e => absent (mem_singleton.mpr e),mem_univ _⟩)) x
    rw [card_singleton] at keep
    change G.degree x.val≤H.degree x+1 at keep
    omega
  obtain ⟨a,b,p,hp,longest,len⟩ := Graph189SidePathDegree.longest_order con (by omega : 1≤d) minH
  have nW : Fintype.card W=W.card := Fintype.card_coe W
  change p.support.length=Fintype.card W ∨ 2*d+1≤p.support.length at len
  have enough : Fintype.card W≤p.support.length+1 := by rcases len with l|l <;> omega
  obtain ⟨x,xT,y,r,hr,near⟩ := Graph189MarkedRotation.from_longest p hp longest T enough (by omega) (by
    change Fintype.card W<H.degree a+H.degree b+T.card
    have A := minH a
    have B := minH b
    omega)
  change Fintype.card W≤r.support.length+(1+1) at near
  let f := (Embedding.induce (G:=G) (W:Set V)).toHom
  let q := r.map f
  have xP : x.val∈P := (mem_erase.mp (mem_subtype.mp xT)).2
  exact ⟨x.val,xP,y.val,q,hr.map Subtype.val_injective,by
    have length : q.support.length=r.support.length := by simp [q]
    omega⟩

#print axioms route
end Graph189MarkedException
