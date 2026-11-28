import Graph189SaturatedExterior
import Graph189ProtectedExteriorSize

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189SixProtected
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At degree six, a traceable deletion of the exceptional vertex of
degree at least three suffices through order twenty-two. -/
theorem traceable (z : V) (three : 3≤G.degree z) (six : G.secondSmallestDegree=6)
    (high : ∀ w, w≠z → G.secondSmallestDegree≤G.degree w)
    (cap : ∀ w, G.distEven w≤G.secondSmallestDegree+1) (order : Fintype.card V≤22)
    {a b : {w : V | w≠z}} (P : (G.induce {w : V | w≠z}).Walk a b) (hP : P.IsHamiltonian) :
    ∃ u v : V, ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  obtain ⟨u,v,p,hp,t,atZ,longest⟩ := exists_longest_through G z
  let E := (p.support.toFinsetᶜ : Finset V)
  by_cases present : E.Nonempty
  swap
  · refine ⟨u,v,p,hp.isHamiltonian_of_mem (fun w => ?_)⟩
    by_contra absent
    exact present ⟨w,by simpa [E] using absent⟩
  exfalso
  have mx : ∀ {i j}, ∀ r : G.Walk i j, r.IsPath → p.support[t.val]∈r.support → r.length≤p.length :=
    fun r hr h => longest r hr (atZ ▸ h)
  have exc (w : V) (diff : w≠p.support[t.val]) : G.secondSmallestDegree≤G.degree w :=
    high w (by simpa only [atZ] using diff)
  obtain ⟨x,hx⟩ := present
  let X : E := ⟨x,hx⟩
  let H := G.induce (E : Set V)
  have kernel := Graph189AllHighExterior.minimum p hp t mx (by omega)
    (fun {w} off => exc w (fun eq => off (by rw [eq]; exact List.getElem_mem _))) cap X
  change G.secondSmallestDegree/2≤H.degree X at kernel
  have vertices := H.degree_lt_card_verts X
  change H.degree X<Fintype.card E at vertices
  rw [Fintype.card_coe] at vertices
  have gaps := protected_size_of_traceable_deletion z (by omega) P hP p hp longest
  change 1+G.degree z+(G.degree z+1)*E.card≤Fintype.card V at gaps
  have scale := Nat.mul_le_mul_right E.card (show 4≤G.degree z+1 by omega)
  have size : E.card=4 := by omega
  have count := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at count
  change p.support.length+E.card=Fintype.card V at count
  exact Graph189SaturatedExterior.exclude p hp t mx exc cap 4 3 size (by omega) (by decide) (by decide) (by omega) (by omega)

#print axioms traceable
end Graph189SixProtected
