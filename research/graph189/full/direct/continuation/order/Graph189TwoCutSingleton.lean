import Graph189SingletonCutOrder
import Graph189PortPath
import Graph189ProtectedHamiltonConnected
import Graph189ProtectedExteriorSize

open SimpleGraph Finset Graph189ExteriorGap
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189TwoCutSingleton
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A path through the unique low vertex missing at most half the second
degree extends in the sense that the graph is traceable. -/
theorem protected_near (z : V) (low : G.degree z<G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1) {x y : V}
    (r : G.Walk x y) (hr : r.IsPath) (on : z∈r.support)
    (near : Fintype.card V≤r.support.length+G.secondSmallestDegree/2) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  obtain ⟨a,b,p,hp,t,eq,longest⟩ := exists_longest_through G z
  refine ⟨a,b,p,hp.isHamiltonian_of_mem fun w => ?_⟩
  by_contra absent
  let E := p.support.toFinsetᶜ
  let u : E := ⟨w,by simpa [E] using absent⟩
  have loc := protected_exterior_minimum p hp t (fun q hq h => longest q hq (eq ▸ h))
    (eq ▸ low) cap u
  have upper := (G.induce (E : Set V)).degree_lt_card_verts u
  change (G.induce (E : Set V)).degree u<Fintype.card E at upper
  rw [Fintype.card_coe] at upper
  have total := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at total
  change p.support.length+E.card=Fintype.card V at total
  have cmp := longest r hr on
  have pl := p.length_support
  have rl := r.length_support
  change _ ≤ (G.induce (E : Set V)).degree u at loc
  omega

theorem joined {a b c d : V} (p : G.Walk a b) (hp : p.IsPath)
    (q : G.Walk c d) (hq : q.IsPath) (edge : G.Adj b c)
    (apart : List.Disjoint p.support q.support) :
    ∃ r : G.Walk a d, r.IsPath ∧ r.support=p.support++q.support := by
  let r := p.append (.cons edge q)
  have eq : r.support=p.support++q.support := by simp [r,Walk.support_append]
  exact ⟨r,Walk.IsPath.mk' (eq ▸ hp.support_nodup.append hq.support_nodup apart),eq⟩

/-- Join a long path from a port of one side to a spanning path in the
opposite side through two anchors and the unique low vertex. -/
theorem traceable_of_side_paths (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    (z : V) (S : Finset V) (W : Bool → Finset V) (split : Graph189SingletonCutOrder.Split G z S W)
    (two : 2≤S.card) (low : G.degree z<G.secondSmallestDegree) (i : Bool)
    {x y : W i} (q : (G.induce ((W i):Set V)).Walk x y) (hq : q.IsPath)
    {u : V} (uS : u∈S) (xu : G.Adj x.val u)
    (sizeSmall : S.card≤(W (!i)).card)
    (small : ∀ a b : W (!i), a≠b → ∃ s : (G.induce ((W (!i)):Set V)).Walk a b, s.IsHamiltonian)
    (near : (W i).card+S.card≤q.support.length+2+G.secondSmallestDegree/2) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  letI : Nontrivial (W (!i)) := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [Fintype.card_coe]
    omega)
  obtain ⟨v,vS,diff⟩ : ∃ v∈S, v≠u := by
    obtain ⟨v,hv⟩ := card_pos.mp (show 0<(S.erase u).card by rw [card_erase_of_mem uS]; omega)
    exact ⟨v,(mem_erase.mp hv).2,(mem_erase.mp hv).1⟩
  obtain ⟨A,subA,sz,f,edges⟩ := Graph189ExteriorGap.matching_at_component_boundary S (W (!i))
    (split.wcut (!i)).symm (fun x hx y hy e => split.closed (!i) x hx y e hy)
    le_rfl sizeSmall
    (fun C short => Graph189CutSides.connected_after_smaller_deletion C (short.trans_le split.connectivity))
  have eqA : A=S := eq_of_subset_of_card_le subA sz
  subst A
  let t := f ⟨v,vS⟩
  obtain ⟨t',ne⟩ := exists_ne t
  obtain ⟨s,hs⟩ := small t t' ne.symm
  let eL := (Embedding.induce (G:=G) ((W i): Set V)).toHom
  let eR := (Embedding.induce (G:=G) ((W (!i)): Set V)).toHom
  let l := q.reverse.map eL
  let r := s.map eR
  have lefton {w : V} (h : w∈l.support) : w∈W i := by
    rw [show l.support=q.reverse.support.map eL from Walk.support_map _ _] at h
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp h
    exact t.property
  have righton {w : V} (h : w∈r.support) : w∈W (!i) := by
    rw [show r.support=s.support.map eR from Walk.support_map _ _] at h
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp h
    exact t.property
  have zu : G.Adj z u := (G.mem_neighborFinset _ _).mp (split.neighbors ▸ uS)
  have zv : G.Adj z v := (G.mem_neighborFinset _ _).mp (split.neighbors ▸ vS)
  let mid : G.Walk u v := .cons zu.symm (.cons zv .nil)
  have midlist : mid.support=[u,z,v] := rfl
  have midpath : mid.IsPath := Walk.IsPath.mk' (by
    rw [midlist]; simp [zu.ne.symm,diff.symm,zv.ne])
  obtain ⟨L,hL,ls⟩ := joined l (hq.reverse.map Subtype.val_injective) mid midpath xu (by
    apply List.disjoint_left.mpr
    intro w wl wm
    have h := lefton wl
    rw [midlist] at wm
    rcases List.mem_cons.mp wm with rfl|wm
    · exact disjoint_left.mp (split.wcut i) h uS
    rcases List.mem_cons.mp wm with rfl|wm
    · exact split.notz i h
    have same : w=v := by simpa using wm
    exact disjoint_left.mp (split.wcut i) (same ▸ h) vS)
  obtain ⟨Q,hQ,qs⟩ := joined L hL r (hs.isPath.map Subtype.val_injective) (edges ⟨v,vS⟩) (by
    apply List.disjoint_left.mpr
    intro w wl wr
    have h := righton wr
    rw [ls] at wl
    rcases List.mem_append.mp wl with left|midm
    · exact disjoint_left.mp (split.apart i) (lefton left) h
    rw [midlist] at midm
    rcases List.mem_cons.mp midm with rfl|midm
    · exact disjoint_left.mp (split.wcut (!i)) h uS
    rcases List.mem_cons.mp midm with rfl|midm
    · exact split.notz (!i) h
    have same : w=v := by simpa using midm
    exact disjoint_left.mp (split.wcut (!i)) (same ▸ h) vS)
  apply protected_near z low cap Q hQ
  · simp [qs,ls,midlist]
  have cover : univ ⊆ insert z ((S∪W i)∪W (!i)) := by
    intro w _
    rcases split.cover w with rfl|ws|ww|ww
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_union_left _ (mem_union_left _ ws))
    all_goals cases i <;> simp_all
  have cnt := (card_le_card cover).trans (card_insert_le _ _)
  rw [card_univ] at cnt
  have top := card_union_le (S∪W i) (W (!i))
  have bot := card_union_le S (W i)
  have llen : l.support.length=q.support.length := by simp [l]
  have rlen : r.support.length=(W (!i)).card := by
    change (s.map eR).support.length=_
    rw [Walk.support_map,List.length_map,hs.length_support]
    exact Fintype.card_coe _
  rw [qs,ls,List.length_append,List.length_append,midlist,llen,rlen]
  change Fintype.card V ≤ q.support.length+3+(W (!i)).card+G.secondSmallestDegree/2
  omega

/-- A separating pair with a singleton component and two other nonempty
regions forces a Hamiltonian path for every second degree at least eight. -/
theorem traceable (hc : G.Connected) (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    (z : V) (S : Finset V) (W : Bool → Finset V) (split : Graph189SingletonCutOrder.Split G z S W)
    (two : S.card=2) (large : 8≤G.secondSmallestDegree) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let k := G.secondSmallestDegree
  let P (i : Bool) := Graph189SingletonCutOrder.ports G S (W i)
  let H (i : Bool) := G.induce ((W i) : Set V)
  have pmem (i : Bool) (v : V) : v∈P i ↔ v∈W i ∧ ∃ u∈S, G.Adj v u := by
    simp [P,Graph189SingletonCutOrder.ports]
  have sub (i : Bool) : P i ⊆ W i := fun _ h => ((pmem i _).mp h).1
  obtain ⟨_,pWide,portCap,remote⟩ := Graph189SingletonCutOrder.population hc cap z S W split
    (by omega) (by omega)
  change ∀ i, S.card≤(P i).card at pWide
  change (P false).card+(P true).card≤k at portCap
  change ∀ i, (W i\P i).card<k at remote
  have big (i : Bool) : 1<(W i).card := by have h:=(pWide i).trans (card_le_card (sub i)); omega
  letI (i : Bool) : Nontrivial (W i) := Fintype.one_lt_card_iff_nontrivial.mp (by simpa using big i)
  have dz : G.degree z=2 := by rw [←G.card_neighborFinset_eq_degree,split.neighbors,two]
  have low : G.degree z<k := by change 8≤k at large; omega
  have minimum (i : Bool) (u : W i) : k-2≤(H i).degree u := by
    have high := (degree_pair (G:=G) u.val z (fun eq => split.notz i (eq ▸ u.property))).resolve_right (not_le.mpr low)
    let N := (G.neighborFinset u.val).filter (fun v => v∈((W i): Set V))
    have inc : G.neighborFinset u.val ⊆ S∪N := by
      intro v hv
      by_cases h : v∈W i
      · exact mem_union_right _ (mem_filter.mpr ⟨hv,h⟩)
      · exact mem_union_left _ (split.closed i u.val u.property v ((G.mem_neighborFinset _ _).mp hv) h)
    have cnt := (card_le_card inc).trans (card_union_le S N)
    rw [G.card_neighborFinset_eq_degree] at cnt
    change k≤G.degree u.val at high
    change k-2≤(G.induce ((W i):Set V)).degree u
    rw [Graph189ExteriorDegreeCycle.degree_induce_filter]
    change k-2≤N.card
    omega
  obtain ⟨i,cmp,sum⟩ : ∃ i : Bool, (P (!i)).card≤(P i).card ∧ (P i).card+(P (!i)).card≤k := by
    by_cases cmp : (P true).card≤(P false).card
    · exact ⟨false,cmp,portCap⟩
    · exact ⟨true,by simpa using le_of_not_ge cmp,by simpa [Nat.add_comm] using portCap⟩
  have ws (j : Bool) := card_sdiff_of_subset (sub j)
  have long : (W i).card≤2*(k-2)+1 := by
    have r := remote i
    have pw := pWide (!i)
    have sw := ws i
    omega
  have short : (W (!i)).card+1≤2*(k-2) := by
    have r := remote (!i)
    have sw := ws (!i)
    change 8≤k at large
    omega
  obtain ⟨a,b,p,hp⟩ := Graph189PortPath.of_degree (minimum i) (by simpa using long)
  let T := (P i).subtype (fun v => v∈W i)
  have cardT : T.card=(P i).card := by
    rw [show T=(P i).subtype (fun v => v∈W i) from rfl,Finset.card_subtype,
      Finset.filter_eq_self.mpr (fun v h => sub i h)]
  have present : T.Nonempty := card_pos.mp (by rw [cardT]; have h:=pWide i; omega)
  obtain ⟨x,xt,y,q,hq,qlen⟩ := Graph189PortPath.from_port p hp T present
  have px : x.val∈P i := Finset.mem_subtype.mp xt
  obtain ⟨_,u,uS,xu⟩ := (pmem i x.val).mp px
  apply traceable_of_side_paths cap z S W split (by omega) low i q hq uS xu
  · have h:=big (!i); omega
  · intro u v ne
    apply Graph189TerminalLeafClosure.prescribed_of_supergraph (G:=H (!i)) le_top _
      (Graph189TerminalLeafClosure.complete_prescribed u v ne)
    intro a b _ _
    change Fintype.card (W (!i))+1≤(H (!i)).degree a+(H (!i)).degree b
    rw [Fintype.card_coe]
    have ha := minimum (!i) a
    have hb := minimum (!i) b
    omega
  · rw [Fintype.card_coe,cardT] at qlen
    have losses := remote i
    rw [ws i] at losses
    change (W i).card+S.card≤q.support.length+2+k/2
    omega

/-- A disconnected graph outside N[z] yields actual separated sides of
the closed neighborhood. -/
theorem split_of_disconnected_complement (z : V) (connectivity : G.degree z≤G.vertexConnectivity)
    (low : G.degree z<G.secondSmallestDegree)
    (disc : ¬(G.induce {u : V | u∉insert z (G.neighborFinset z)}).Connected) :
    ∃ W, Graph189SingletonCutOrder.Split G z (G.neighborFinset z) W := by
  classical
  let S := G.neighborFinset z
  let T := insert z S
  have cardS : S.card=G.degree z := G.card_neighborFinset_eq_degree z
  have outside : ∃ u, u∉T := by
    by_contra! full
    have eq : T=univ := eq_univ_iff_forall.mpr full
    have bound := card_insert_le z S
    change T.card ≤ _ at bound
    rw [eq,card_univ] at bound
    obtain ⟨v,ne⟩ := exists_ne z
    have h := (degree_pair (G:=G) v z ne).resolve_right (by omega)
    have upper := G.degree_lt_card_verts v
    omega
  obtain ⟨A,B,l⟩ := Graph189CutSides.exists_cutSides_of_disconnected T outside disc
  let W : Bool → Finset V := fun i => if i then B else A
  have wT (i : Bool) : Disjoint (W i) T := by cases i <;> first | exact l.left_cut | exact l.right_cut
  have other (i : Bool) : Disjoint (W i) (W (!i)) := by cases i <;> first | exact l.apart | exact l.apart.symm
  refine ⟨W,rfl,cardS ▸ connectivity,?_,other,?_,?_,?_,?_⟩
  · intro i
    cases i <;> first | exact l.left_nonempty | exact l.right_nonempty
  · exact fun i => (wT i).mono_right (subset_insert _ _)
  · exact fun i hz => disjoint_left.mp (wT i) hz (mem_insert_self _ _)
  · intro i x hx y e out
    have yt : y∈T := by
      rcases l.cover y with ha|hb|ht
      · cases i
        · exact (out ha).elim
        · exact (l.no_cross y ha x hx e.symm).elim
      · cases i
        · exact (l.no_cross x hx y hb e).elim
        · exact (out hb).elim
      · exact ht
    rcases mem_insert.mp yt with rfl|ys
    · exact False.elim (disjoint_left.mp (wT i) hx
        (mem_insert_of_mem ((G.mem_neighborFinset _ _).mpr e.symm)))
    · exact ys
  · intro u
    rcases l.cover u with ha|hb|ht
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr hb))
    · rcases mem_insert.mp ht with hz|hs
      · exact Or.inl hz
      · exact Or.inr (Or.inl hs)

/-- The original graph is traceable whenever a degree-two vertex has a
disconnected graph outside its closed neighborhood, at second degree ≥8. -/
theorem of_disconnected_complement (hc : G.Connected)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    (twoConnected : 2≤G.vertexConnectivity) (z : V) (degree : G.degree z=2)
    (large : 8≤G.secondSmallestDegree)
    (disc : ¬(G.induce {u : V | u∉insert z (G.neighborFinset z)}).Connected) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨W,split⟩ := split_of_disconnected_complement z (by omega : G.degree z≤G.vertexConnectivity) (by omega) disc
  exact traceable hc cap z (G.neighborFinset z) W split ((G.card_neighborFinset_eq_degree z).trans degree) large

#print axioms traceable
#print axioms of_disconnected_complement
end Graph189TwoCutSingleton
