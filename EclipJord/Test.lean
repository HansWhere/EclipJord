import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring.RingNF

example (n : ℕ) : 6*(∑ ⟨i,_⟩ : Fin (n+1), i*(2*i+1)) = n*(n+1)*(4*n+5) := by
  induction n
  simp
  case succ n ih
  . rw [
      show (∑ ⟨i,_⟩ : Fin (n+2), i*(2*i + 1))
          = (∑ ⟨i,_⟩ : Fin (n+1), i*(2*i + 1)) + (n+1)*(2*(n+1) + 1) by
        rw [Fin.sum_univ_castSucc]
        congr,
      mul_add, ih
    ]
    ring_nf
