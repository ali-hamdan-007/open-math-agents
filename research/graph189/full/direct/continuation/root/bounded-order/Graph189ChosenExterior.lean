import Graph189OptimalShell
import Graph189OrdinaryNearOriginal

open SimpleGraph Finset Graph189ExteriorGap
namespace Graph189OptimalExterior
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The exterior component used throughout the bounded-order paper. -/
structure Chosen {a b : V} (p : G.Walk a b) (C : Finset V) (k : ℕ) : Prop where
  path : p.IsPath
  longest : ∀{u v},∀q : G.Walk u v,q.IsPath → q.length≤p.length
  connected : (G.induce (C:Set V)).Preconnected
  outside : ∀v∈C,v∉p.support
  closed : ∀x∈C,∀y,G.Adj x y → y∉p.support → y∈C
  high : ∃x∈C,k≤G.degree x
  midpoint : ∀x∈C,(G.induce (C.erase x:Set V)).Preconnected →
    ∀t,t∈contactPositions p x → t+2∈contactPositions p x → G.degree (p.getVert (t+1))<k

theorem choose (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 6≤G.secondSmallestDegree) (minimum : 3≤G.minDegree)
    (bad : ¬∃a b,∃p : G.Walk a b,p.IsHamiltonian) :
    ∃a b,∃p : G.Walk a b,∃C,Chosen p C G.secondSmallestDegree := by
  classical
  let k := G.secondSmallestDegree
  have point (v : V) : G.distEven v≤1+k := (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have quota (v : V) := Graph189OrdinaryPathGap.second_layer_budget point v
  have unique (x y : V) (hx : G.degree x<k) (hy : G.degree y<k) : x=y := by
    by_contra diff
    exact (OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) x y diff).elim
      (Nat.not_le_of_gt hx) (Nat.not_le_of_gt hy)
  obtain ⟨a,b,p,F,path,long,Fdata,best⟩ := exists_optimal G
  let Cands := univ.filter (fun i => ∃v∈F i,k≤G.degree v)
  have candidates : Cands.Nonempty := by
    by_contra empty
    have small : p.support.toFinsetᶜ.card≤1 := by
      apply card_le_one.mpr
      intro x hx y hy
      have low (v : V) (hv : v∈p.support.toFinsetᶜ) : G.degree v<k := by
        by_contra! high
        obtain ⟨i,hi⟩ := (Fdata.cover v).mp hv
        exact empty ⟨i,mem_filter.mpr ⟨mem_univ _,v,hi,high⟩⟩
      exact unique _ _ (low _ hx) (low _ hy)
    have size := card_compl_add_card p.support.toFinset
    rw [List.toFinset_card_of_nodup path.support_nodup] at size
    exact bad (Graph189OrdinaryPathGap.traceable_of_near_unrestricted hc point large minimum p path
      (by unfold Graph189OrdinaryPathGap.Near; omega))
  obtain ⟨i,hi,minimal⟩ := Cands.exists_min_image (fun j => (F j).card) candidates
  have least (j : V) (hj : ∃v∈F j,k≤G.degree v) : (F i).card≤(F j).card :=
    minimal j (mem_filter.mpr ⟨mem_univ _,hj⟩)
  refine ⟨a,b,p,F i,path,long,Fdata.connected i,?_,?_,(mem_filter.mp hi).2,?_⟩
  · intro v vi on
    exact mem_compl.mp ((Fdata.cover v).mpr ⟨i,vi⟩) (List.mem_toFinset.mpr on)
  · intro x xi y edge off
    obtain ⟨j,yj⟩ := (Fdata.cover y).mp (mem_compl.mpr (fun on => off (List.mem_toFinset.mp on)))
    have eq := same_part Fdata (fun K data => best p path rfl K data) xi yj edge
    exact eq.symm ▸ yj
  intro x xi noncut t left right
  obtain ⟨valid,adj⟩ := (mem_contactPositions p x _).mp right
  exact midpoint_low p path long Fdata best xi noncut least valid
    ((mem_contactPositions p x t).mp left).2 adj quota
    (fun v => minimum.trans (G.minDegree_le_degree v)) unique

end Graph189OptimalExterior
#print axioms Graph189OptimalExterior.choose
