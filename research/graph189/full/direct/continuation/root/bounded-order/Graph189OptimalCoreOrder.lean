import Graph189OptimalPorts

open SimpleGraph Finset Graph189ExteriorGap
namespace Graph189OptimalExterior
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem internal_half {a b : V} {p : G.Walk a b} {C : Finset V} {k : ℕ} (h : Chosen p C k)
    {x : V} (xc : x∈C) (high : k≤G.degree x) (quota : (univ.filter (fun v => G.dist x v=2)).card≤k)
    (minimum : ∀v,3≤G.degree v) (uniqueLow : ∀u v,G.degree u<k → G.degree v<k → u=v) :
    G.degree x≤2*(G.neighborFinset x∩C).card := by
  have half := (high_exterior_half p h.path h.longest (h.outside _ xc) quota high minimum uniqueLow).2
  have parts := card_sdiff_add_card_inter (G.neighborFinset x) p.support.toFinset
  rw [←contact_card_neighbors p h.path x] at parts
  change _+(contactPositions p x).card=G.degree x at parts
  have split := degree_split h xc
  omega

/-- A high noncut vertex with a small internal degree gives the paper's
matched order bound in the actual graph, including one exceptional low vertex. -/
theorem noncut_order {a b : V} {p : G.Walk a b} {C : Finset V} {k : ℕ} (h : Chosen p C k)
    {x : V} (xc : x∈C) (high : k≤G.degree x)
    (noncut : (G.induce (C.erase x:Set V)).Preconnected)
    (minimum : ∀v,3≤G.degree v) (uniqueLow : ∀u v,G.degree u<k → G.degree v<k → u=v)
    (quota : (univ.filter (fun v => G.dist x v=2)).card≤k) (large : 6≤k)
    (dense : 3*(G.neighborFinset x∩C).card+3≤2*k) :
    let q := (G.neighborFinset x∩C).card
    let r := (C.filter (fun y => G.dist x y=2)).card
    let t := min q (k-q-r)
    C.card+t+(t+1)*q≤Fintype.card V ∧ 2*k≤t+3*q+1 := by
  classical
  let N := G.neighborFinset x∩C
  let X := insert x N
  let H := X.filter (fun y => k≤G.degree y)
  let r := (C.filter (fun y => G.dist x y=2)).card
  let q := N.card
  let t := min q (k-q-r)
  obtain ⟨size,sub,radius,rows,routes⟩ := high_core h xc high noncut minimum uniqueLow quota dense
  change q≤H.card at size
  change r+k+(X \ H).card≤2*q+1 at radius
  change 3*q+3≤2*k at dense
  have half := high.trans (internal_half h xc high quota minimum uniqueLow)
  change k≤2*q at half
  have pos : 0<t := by dsimp [t]; omega
  have enough : t≤H.card := (min_le_left _ _).trans size
  have width (v : V) (vh : v∈H) : t≤(contactPositions p v).card := by
    have rwv := rows v vh
    change k≤(contactPositions p v).card+q+r at rwv
    dsimp only [t]; omega
  have tails (v : V) (vh : v∈H) : ∃w,ExteriorRoute p w v (H.card+0) := by
    obtain ⟨u,uh,uv⟩ := exists_mem_ne (s:=H) (a:=v) (by omega : 1<H.card)
    obtain ⟨z,hz⟩ := routes ⟨u,uh⟩ ⟨v,vh⟩ (fun eq => uv (congrArg Subtype.val eq))
    exact ⟨u,route_of_induced_hamilton p H (fun y hy => h.outside _ (sub hy)) hz⟩
  have order := core_ports h H sub pos enough width routes tails
  have comp := Nat.mul_le_mul_left (t+1) size
  change C.card+t+(t+1)*q≤Fintype.card V ∧ 2*k≤t+3*q+1
  exact ⟨by omega,by dsimp [t]; omega⟩

end Graph189OptimalExterior
#print axioms Graph189OptimalExterior.noncut_order
