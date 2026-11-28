import Graph189BoundaryMatching

open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {x y : V}

/-- A Hamilton-spanning route between every two distinct nonexceptional terminals
is sufficient at a buffered component boundary. Deleting at most one matched
contact removes the exceptional port. -/
theorem buffered_order_avoiding_port (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length ≤ p.length)
    (K F : Finset V) (outside : ∀ z∈K, z∉p.support) (fP : Disjoint F p.support.toFinset)
    (fK : Disjoint F K) (boundary : ∀ u∈K, ∀ v∉K, G.Adj u v → v∈p.support ∨ v∈F)
    (exception : K)
    (regular : ∀ a b : K, a≠b → a≠exception → b≠exception →
      ∃ q : (G.induce (K : Set V)).Walk a b, q.IsHamiltonian)
    {s : ℕ} (three : 3 ≤ s) (smallP : s ≤ p.support.length) (smallK : s ≤ K.card)
    (connected : ∀ cut : Finset V, cut.card < s+F.card → (G.induce {u : V | u∉cut}).Connected) :
    (s+1)*K.card+(s-1) ≤ Fintype.card V := by
  classical
  have apart : Disjoint p.support.toFinset K := Finset.disjoint_left.mpr (by
    intro z hz hk
    exact outside z hk (List.mem_toFinset.mp hz))
  have sizeP : s ≤ p.support.toFinset.card := by rwa [List.toFinset_card_of_nodup hp.support_nodup]
  obtain ⟨M,on,wide,f,edges⟩ := matching_at_buffered_boundary p.support.toFinset K F apart fP fK
    (fun u hu v hv h => (boundary u hu v hv h).imp List.mem_toFinset.mpr id) sizeP smallK connected
  have single : ∃ w : M, ∀ z : M, f z=exception → z=w := by
    by_cases ex : ∃ z : M, f z=exception
    · obtain ⟨w,hw⟩ := ex
      exact ⟨w,fun z hz => f.injective (hz.trans hw.symm)⟩
    · obtain ⟨w,hw⟩ := Finset.card_pos.mp (show 0 < M.card by omega)
      exact ⟨⟨w,hw⟩,fun z he => (ex ⟨z,he⟩).elim⟩
  obtain ⟨w,forbidden⟩ := single
  let T := M.erase w.val
  let lift : T ↪ M := ⟨fun t => ⟨t.val,(Finset.mem_erase.mp t.property).2⟩,
    fun a b h => Subtype.ext (congrArg (fun z : M => z.val) h)⟩
  let attach := lift.trans f
  have size : T.card+1=M.card := Finset.card_erase_add_one w.property
  have avoid (z : T) : attach z ≠ exception := by
    intro he
    exact (Finset.mem_erase.mp z.property).1 (congrArg Subtype.val (forbidden (lift z) he))
  have bound := selected_vertex_matching_order p hp longest K outside T (by omega)
    (fun z hz => List.mem_toFinset.mp (on (Finset.mem_erase.mp hz).2)) attach (fun i => edges (lift i))
    (fun i j ne => regular _ _ (attach.injective.ne ne) (avoid i) (avoid j))
  have left := Nat.mul_le_mul_right K.card (show s+1 ≤ T.card+2 by omega)
  exact (Nat.add_le_add left (show s-1 ≤ T.card by omega)).trans bound

#print axioms buffered_order_avoiding_port
end Graph189ExteriorGap
