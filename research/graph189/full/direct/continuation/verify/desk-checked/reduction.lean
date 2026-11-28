import OMAReductions.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1

-- Moderate order for Graph 189, by @ali-hamdan-007.
open Finset SimpleGraph
namespace OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1_H1_R1

def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
    (∀ x, distEven G x ≤ 1 + secondSmallestDegree G) →
    2 * secondSmallestDegree G + 3 ≤ Fintype.card V →
    (∀ c : V, (G.induce {x | x ≠ c}).Connected) →
    Fintype.card V ≤ 3 * secondSmallestDegree G + 2 →
    Fintype.card V ≤ 2 * secondSmallestDegree G + 6 →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
    (∀ x, distEven G x ≤ 1 + secondSmallestDegree G) →
    2 * secondSmallestDegree G + 3 ≤ Fintype.card V →
    (∀ c : V, (G.induce {x | x ≠ c}).Connected) →
    Fintype.card V ≤ 3 * secondSmallestDegree G + 2 →
    2 * secondSmallestDegree G + 6 < Fintype.card V →
    secondSmallestDegree G = 5 →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

def H3 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
    (∀ x, distEven G x ≤ 1 + secondSmallestDegree G) →
    2 * secondSmallestDegree G + 3 ≤ Fintype.card V →
    (∀ c : V, (G.induce {x | x ≠ c}).Connected) →
    Fintype.card V ≤ 3 * secondSmallestDegree G + 2 →
    2 * secondSmallestDegree G + 6 < Fintype.card V →
    secondSmallestDegree G = 6 →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

def H4 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
    (∀ x, distEven G x ≤ 1 + secondSmallestDegree G) →
    2 * secondSmallestDegree G + 3 ≤ Fintype.card V →
    (∀ c : V, (G.induce {x | x ≠ c}).Connected) →
    Fintype.card V ≤ 3 * secondSmallestDegree G + 2 →
    2 * secondSmallestDegree G + 6 < Fintype.card V →
    7 ≤ secondSmallestDegree G →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

theorem main : H1 → H2 → H3 → H4 → OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1.H1 := by
  intro short five six seven V _ _ _ G _ hc point lower uncut upper
  by_cases h : Fintype.card V ≤ 2 * G.secondSmallestDegree + 6
  · exact short G hc point lower uncut upper h
  have wide : 2 * G.secondSmallestDegree + 6 < Fintype.card V := by omega
  by_cases f : G.secondSmallestDegree = 5
  · exact five G hc point lower uncut upper wide f
  by_cases s : G.secondSmallestDegree = 6
  · exact six G hc point lower uncut upper wide s
  exact seven G hc point lower uncut upper wide (by omega)
end OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1_H1_R1
