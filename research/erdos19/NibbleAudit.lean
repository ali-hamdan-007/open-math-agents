import OMAReductions.R_Erdos19_erdos_19_variants_kahn_R1_H1_R1

namespace Erdos19NibbleAudit

theorem not_H1 : ¬ OMA.R_Erdos19_erdos_19_variants_kahn_R1_H1_R1.H1 := by
  intro h
  obtain ⟨s, _, hs⟩ := h 2 (by decide)
  obtain ⟨D₀, hD₀⟩ := hs 1 (by decide)
  obtain ⟨_, _, c, _⟩ := hD₀ 0 D₀ 0 le_rfl ∅ (fun _ => ∅)
    (by simp) (by simp) (fun i => Fin.elim0 i) (by simp)
  exact Fin.elim0 (c ∅)

end Erdos19NibbleAudit

#print axioms Erdos19NibbleAudit.not_H1
