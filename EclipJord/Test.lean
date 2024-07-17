import Mathlib.Algebra.Polynomial.Eval
import Mathlib.RingTheory.Polynomial.Basic

open MvPolynomial
open Ideal

noncomputable section
variable {K : Type ℓ} [Field K]

abbrev 𝕍 (I : Ideal (MvPolynomial (Fin n) K)) : Set (Fin n → K)
:= { P : (Fin n → K) | ∀ f ∈ I, eval P f = 0}

structure AlgSet (K : Type ℓ) [Field K] (n : ℕ) : Type ℓ where
  V : Set (Fin n → K)
  is_algebraic : ∃ I : Ideal (MvPolynomial (Fin n) K), V = 𝕍 I

structure Variety (K : Type ℓ) [Field K] (n : ℕ) : Type ℓ where
  V : Set (Fin n → K)
  is_prime : ∃ I : Ideal (MvPolynomial (Fin n) K), IsPrime I ∧ V = 𝕍 I

def Variety.toAlgSet (A : Variety K n) : AlgSet K n := {
  V := A.V
  is_algebraic := Exists.elim A.is_prime $ by
    rintro I0 ⟨_, h⟩
    exists I0
}

inductive 𝕊1 : Type where
| base : 𝕊1
| loop : base = base
