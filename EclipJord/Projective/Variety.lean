import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.Eval
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Topology.Basic
import Mathlib.Order.BooleanAlgebra
import Mathlib.Data.Set.Finite
import EclipJord.Affine.Variety
open MvPolynomial
open Ideal
open scoped Pointwise

noncomputable section

namespace ℙ
variable {n d : ℕ}
variable {K : Type ℓ} [Field K]

-- scoped[MvPolynomial] notation:9000 R "[X,..]" n => MvPolynomial (Fin n) R

abbrev Homogeneous

#check (inferInstance : SetLike.GradedMonoid (homogeneousSubmodule (Fin n) K d))

abbrev 𝕍 (I : Ideal K[X,..]n) : Set (𝔸 K n)
:= { P : 𝔸 K n | ∀ f ∈ I, eval P f = 0}
