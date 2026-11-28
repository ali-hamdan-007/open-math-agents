import Graph189OptimalComponents
import Graph189TwoMarkShift

open SimpleGraph Finset Graph189ExteriorGap
namespace Graph189OptimalExterior
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The predecessors and successors of the marks consume separate two-distance
witnesses except for low vertices of the path. The exterior witnesses are disjoint. -/
theorem shell_count {a b x : V} (p : G.Walk a b) (hp : p.IsPath)
    (longest : ∀{u v},∀q : G.Walk u v,q.IsPath → q.length≤p.length)
    (out : x∉p.support) {k : ℕ} (C : Finset V) (off : ∀v∈C,v∉p.support)
    (quota : (univ.filter (fun z => G.dist x z=2)).card≤k)
    (middle : ∀t,t∈contactPositions p x → t+2∈contactPositions p x → G.degree (p.getVert (t+1))<k) :
    (C.filter (fun v => G.dist x v=2)).card+2*(contactPositions p x).card ≤
      k+(p.support.toFinset.filter (fun y => G.degree y<k)).card := by
  classical
  let A := contactPositions p x
  let B := A.image (fun i => i-1)
  let D := A.image (fun i => i+1)
  let W := B∪D
  let R := C.filter (fun v => G.dist x v=2)
  let low := p.support.toFinset.filter (fun y => G.degree y<k)
  have shifted {i : ℕ} (hi : i∈A) := shifted_contact p hp longest out hi
  have valid {i : ℕ} (mem : i∈W) : i<p.support.length ∧ G.dist x (p.getVert i)=2 := by
    rcases mem_union.mp mem with h|h
    · obtain ⟨j,hj,rfl⟩ := mem_image.mp h
      obtain ⟨_,below,dist,_⟩ := shifted hj
      exact ⟨by omega,dist⟩
    obtain ⟨j,hj,rfl⟩ := mem_image.mp h
    exact ⟨(shifted hj).2.1,(shifted hj).2.2.2⟩
  have lens := p.length_support
  have inject : Set.InjOn p.getVert (W:Set ℕ) := by
    intro i hi j hj eq
    exact hp.getVert_injOn (by change i≤p.length; have := (valid hi).1; omega)
      (by change j≤p.length; have := (valid hj).1; omega) eq
  have lowOverlap : (B∩D).image p.getVert⊆low := by
    intro v hv
    obtain ⟨s,hs,rfl⟩ := mem_image.mp hv
    obtain ⟨j,hj,ej⟩ := mem_image.mp (mem_inter.mp hs).1
    obtain ⟨i,hi,ei⟩ := mem_image.mp (mem_inter.mp hs).2
    change j-1=s at ej
    change i+1=s at ei
    have pos := (shifted hj).1
    have eq : i+2=j := by omega
    exact mem_filter.mpr ⟨List.mem_toFinset.mpr (p.getVert_mem_support _),ei ▸ middle i hi (eq ▸ hj)⟩
  have ov := card_le_card lowOverlap
  have sub : ((B∩D : Finset ℕ):Set ℕ)⊆(W:Set ℕ) := fun _ h => mem_union_left _ (mem_inter.mp h).1
  rw [card_image_of_injOn (inject.mono sub)] at ov
  have pred : Set.InjOn (fun i : ℕ => i-1) (A:Set ℕ) := by
    intro i hi j hj h
    have := (shifted hi).1
    have := (shifted hj).1
    change i-1=j-1 at h
    omega
  have counts := card_union_add_card_inter B D
  change W.card+(B∩D).card=B.card+D.card at counts
  rw [show B.card=A.card from card_image_of_injOn pred,
    show D.card=A.card from card_image_of_injective _ (fun i j h => Nat.add_right_cancel h)] at counts
  have dis : Disjoint R (W.image p.getVert) := by
    apply Finset.disjoint_left.mpr
    intro v hr hv
    obtain ⟨i,_,rfl⟩ := mem_image.mp hv
    exact off _ (mem_filter.mp hr).1 (p.getVert_mem_support _)
  have within : R∪W.image p.getVert⊆univ.filter (fun v => G.dist x v=2) := by
    intro v hv
    rcases mem_union.mp hv with hr|hw
    · exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hr).2⟩
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hw
    exact mem_filter.mpr ⟨mem_univ _,(valid hi).2⟩
  have total := (card_le_card within).trans quota
  rw [card_union_of_disjoint dis,card_image_of_injOn inject] at total
  change R.card+2*A.card≤k+low.card
  omega

end Graph189OptimalExterior
#print axioms Graph189OptimalExterior.shell_count
