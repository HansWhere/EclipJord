import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.Eval
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.GradedAlgebra.HomogeneousIdeal
-- import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.Polynomial.Basic
-- import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Topology.Basic
import Mathlib.Order.BooleanAlgebra
import Mathlib.Data.Set.Finite
import EclipJord.Affine.Variety
import EclipJord.Projective.Defs
open MvPolynomial
open Ideal
-- open DirectSum
open scoped Pointwise

noncomputable section

namespace ℙ
variable {n d : ℕ}
variable {K : Type ℓ} [Field K] --[DecidableEq K]

scoped[MvPolynomial] notation:9000 R "[X,..]" n "homo" => (homogeneousSubmodule (Fin n) R)

def vanish (P : ℙ K n) (f : K[X,..](n+1) homo d) : Prop
:= ∀ P0 : no0 (𝔸 K (n+1)), Quotient.mk 𝔸.setoid P0 = P ∧ eval P0.1 f.1 = 0

  -- @Quotient.lift _ _
  -- (𝔸.setoid : Setoid (no0 (𝔸 K (n+1)))) (λ P ↦ MvPolynomial.eval P.1 f.1)
  -- (by
  --   rintro ⟨P, P_not0⟩ ⟨Q, Q_not0⟩
  --   simp [HasEquiv.Equiv, Setoid.r, 𝔸.collinear]
  --   rintro ⟨k, k_not0⟩
  --   simp
  --   intro P_colli_Q
  --   rw [P_colli_Q]
  -- )
  -- P

-- abbrev Homogeneous : Set (K[X,..]n) := sorry

#check (inferInstance : SetLike.GradedMonoid (K[X,..]n homo))
-- #check (inferInstance : GradedRing (homogeneousSubmodule (Fin n) K))

instance : DirectSum.Decomposition (K[X,..]n homo) where
  decompose' f := DirectSum.mk
    (λ d ↦ ↥(K[X,..]n homo d))
    (Finset.range f.totalDegree)
    (λ d ↦ ⟨homogeneousComponent d f, homogeneousComponent_isHomogeneous d f⟩)
  left_inv := sorry --by
    -- intro f
    -- rw [MvPolynomial.ext_iff]
    -- intro m
    -- simp [coeff, DirectSum.coeAddMonoidHom, MvPolynomial.sum_homogeneousComponent]
  right_inv := sorry

instance : GradedRing (K[X,..]n homo) where

#check (inferInstance : DirectSum.Decomposition K[X,..]n homo)
#check (inferInstance : GradedRing K[X,..]n homo)

abbrev 𝕍 (I : HomogeneousIdeal K[X,..](n+1) homo) : Set (ℙ K n)
:= { P : ℙ K n | ∀ f ∈ I, ∀ d : Fin (f.totalDegree),
  vanish P ⟨homogeneousComponent d f, homogeneousComponent_isHomogeneous d f⟩}

def 𝕞 (P : ℙ K n) : HomogeneousIdeal (K[X,..](n+1) homo) := sorry

structure AlgSet (K : Type ℓ) [Field K] (n : ℕ) : Type ℓ where
  V : Set (ℙ K n)
  is_algebraic : ∃ I : HomogeneousIdeal (K[X,..](n+1) homo), V = 𝕍 I

structure Variety (K : Type ℓ) [Field K] (n : ℕ) : Type ℓ where
  V : Set (ℙ K n)
  is_prime : ∃ I : HomogeneousIdeal (K[X,..](n+1) homo), IsPrime I.toIdeal ∧ V = 𝕍 I

def Variety.toAlgSet (A : Variety K n) : AlgSet K n := {
  V := A.V
  is_algebraic := Exists.elim A.is_prime $ by
    rintro I0 ⟨_, h⟩
    exists I0
}

end ℙ
