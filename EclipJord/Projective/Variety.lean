import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.Eval
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.GradedAlgebra.HomogeneousIdeal
-- import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.Polynomial.Basic
-- import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Field.Defs
-- import Mathlib.LinearAlgebra.Quotient
import Mathlib.Topology.Basic
-- import Mathlib.Order.BooleanAlgebra
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Set.Finite
import EclipJord.Affine.Variety
import EclipJord.Projective.Defs
open MvPolynomial
open Ideal
-- open DirectSum
-- open scoped Pointwise

variable {K : Type ℓ} [Field K]

noncomputable section
scoped[MvPolynomial] notation:9000 R "[X,..]" n "homo" => (homogeneousSubmodule (Fin n) R)

theorem MvPolynomial.eval_smul_homo [Field K] : ∀ P₀ : 𝔸 K n, ∀ f : K[X,..]n, ∀ k : K, ∀ d : ℕ,
    k^d * (eval P₀ (homogeneousComponent d f)) = eval (k • P₀) (homogeneousComponent d f) := by
  intro P₀ f k d
  have fh := homogeneousComponent_isHomogeneous d f
  simp only [MvPolynomial.IsHomogeneous, IsWeightedHomogeneous, weightedDegree_one, degree, coeff] at fh
  simp [eval_eq, coeff]
  have fh' : ∀ x ∈ ((homogeneousComponent d) f).support, ∑ i ∈ x.support, x i = d := by
    intro x
    intro xh
    simp [support] at xh
    exact @fh x xh
  conv =>
    rhs
    conv =>
      tactic =>
        apply Finset.sum_congr rfl
        intro x xh
      conv =>
        arg 2
        conv =>
          arg 2
          intro i
          rw [mul_pow]
        rw [Finset.prod_mul_distrib]
        arg 1
        rw [Finset.prod_pow_eq_pow_sum x.support]
        rw [fh' x xh]
      rw [←mul_assoc]
      conv =>
        arg 1
        rw [mul_comm]
      rw [mul_assoc]
    rw [←Finset.mul_sum]

-- theorem coeff_all0 (σ : Finset ℕ) : ∀ f : ℕ → K,
--   (∀ k : no0 K, (∑ d ∈ σ, (k.1^d) * f d) = 0) ↔ ∀ d ∈ σ, f d = 0 := by
--   intro f
--   apply Iff.intro
--   by_contra! h
--   . rcases h with ⟨sh, d₀, d₀h, fd₀_ne0⟩
--     have fh := sh
--     conv at fh =>
--       intro k
--       conv =>
--         lhs
--         rw [←Finset.sum_filter_add_sum_filter_not _ (Eq d₀), Finset.filter_eq]
--         simp [d₀h]
--       rw [add_eq_zero_iff_neg_eq]
--       simp
--     -- have some_ne0 : ∀ k : no0 K, k.1 ^ d₀ * f d₀ ≠ 0 := by
--     --   intro k
--     --   apply mul_ne_zero
--     --   . apply pow_ne_zero
--     --     exact k.2
--     --   . exact fd₀_ne0
--     have another_ne0 : ∀ k : no0 K, ∃ x ∈ Finset.filter (λ x ↦ d₀ ≠ x) σ, k.1 ^ x * f x ≠ 0 := by
--       intro k
--       apply Finset.exists_ne_zero_of_sum_ne_zero
--       rw [←fh k]
--       apply neg_ne_zero.mpr
--       -- exact some_ne0 k
--       apply mul_ne_zero
--       . apply pow_ne_zero
--         exact k.2
--       . exact fd₀_ne0
--     -- conv at some_ne0 =>
--     --   conv =>
--     --     intro k
--     --     rw [mul_ne_zero_iff]
--     --     simp [k.2]
--     --   simp
--     conv at another_ne0 =>
--       conv =>
--         intro k
--         simp [k.2]
--       simp
--     --  at some_ne0
--     rcases another_ne0 with ⟨d₁, ⟨d₁h, d₀_ne_d₁⟩, fd₁_ne0⟩
--     -- ∃ d, d ∈ σ ∧ d₀ ≠ d ∧ f d ≠ 0
--     have sh1 := sh ⟨1, by simp⟩
--     simp [one_pow] at sh1

--   . intro dh k
--     apply Finset.sum_eq_zero
--     intro d₀ d₀h
--     apply mul_eq_zero_of_right
--     exact dh d₀ d₀h


  -- intro kh
  -- intro sh
  -- by_contra h
  -- push_neg at h
  -- rcases h with ⟨h₀, hh⟩
  -- #check Finset.sum_filter_add_sum_filter_not σ (λ d ↦ d = h) (λ d ↦ k ^ d * c d)
  -- rw [←Finset.sum_filter_add_sum_filter_not _ (λ d ↦ d = h₀)] at sh
  -- have : Finset.filter (fun d ↦ d = h₀) σ = {h₀} := sorry
  -- simp [Finset.coe_filter] at sh

  -- intro dh
  -- simp [dh]
  -- done

namespace ℙ
variable {n d : ℕ}

def vanish (P : ℙ K n) (f : K[X,..] n+1) : Prop
:= ∀ P₀ : no0 (𝔸 K (n+1)), ℙ.mk P₀ = P → eval P₀.1 f = 0

#check (inferInstance : SetLike.GradedMonoid (K[X,..]n homo))
-- #check (inferInstance : GradedRing (homogeneousSubmodule (Fin n) K))

instance : DirectSum.Decomposition (K[X,..]n homo) where
  decompose' f := DirectSum.mk
    (λ d ↦ ↥(K[X,..]n homo d))
    (Finset.range f.totalDegree)
    (λ d ↦ ⟨homogeneousComponent d f, homogeneousComponent_isHomogeneous d f⟩)
  left_inv := by
    intro f
    rw [MvPolynomial.ext_iff]
    intro m
    sorry
    -- simp [coeff, DirectSum.coeAddMonoidHom, MvPolynomial.sum_homogeneousComponent]
  right_inv := sorry

instance : GradedRing (K[X,..]n homo) where

#check (inferInstance : DirectSum.Decomposition K[X,..]n homo)
#check (inferInstance : GradedRing K[X,..]n homo)

def 𝕍 (I : HomogeneousIdeal K[X,..] n+1 homo) : Set (ℙ K n)
:= { P : ℙ K n | ∀ f ∈ I, P.vanish f}

-- x^2-1 ∈ 𝕞? [1 : 0]
-- 1

-- def 𝕞? (P : ℙ K n) : HomogeneousIdeal (K[X,..] n+1 homo) := {
--   carrier := {f : K[X,..] n+1 | P.vanish f}
--   add_mem' := by
--     intros f g fh gh P₀ P₀h
--     simp [fh P₀ P₀h, gh P₀ P₀h]
--   zero_mem' := by
--     simp [vanish]
--   smul_mem' := by
--     intros r f fh P₀ P₀h
--     simp [fh P₀ P₀h]
--   is_homogeneous' := by
--     simp only [vanish, Ideal.IsHomogeneous]
--     intros d f fh P₀ P₀h
--     simp at fh
--     rw [←sum_homogeneousComponent f] at fh
--     have fh' : ∀ (k : no0 K), ∀ (P₀ : no0 (𝔸 K (n + 1))), ⟦P₀⟧ = P →
--         (∑ d ∈ Finset.range (f.totalDegree + 1),
--         (k.1 ^ d * (eval P₀.1 (homogeneousComponent d f)))) = 0 := by -- eval (k.1 • P₀.1)) ((homogeneousComponent i) f)
--       intro k P₀ kP₀h
--       -- have kP1_distr : k.1 • P₀.1 = (k • P₀).1 := by simp [(.•.), SMul.smul, 𝔸.no0.smul']
--       -- rw [kP1_distr]
--       conv =>
--         lhs; arg 2; intro d
--         rw [eval_smul_homo P₀.1 f k.1 d]
--       rw [←𝔸.no0.collinear.smul_closed P₀ k] at kP₀h
--       rw [←eval_sum (Finset.range (f.totalDegree + 1)) (λ d ↦ (homogeneousComponent d) f) (k.1 • P₀.1)]
--       apply fh
--       exact kP₀h
-- }

def 𝕞 (P : ℙ K n) : HomogeneousIdeal (K[X,..] n+1 homo) :=
  let fs := {f : K[X,..]n+1
    | ∃ i : ℕ, MvPolynomial.IsHomogeneous f i
    ∧ ∀ P₀ : no0 (𝔸 K (n + 1)), ⟦P₀⟧ = P → eval P₀ f = 0}
  HomogeneousIdeal.mk (Ideal.span fs) $ by
    apply Ideal.homogeneous_span
    simp [SetLike.Homogeneous, fs]
    intro _ i _ _
    exists i

-- p = max(S)
-- M(p, S)

#check HomogeneousIdeal.mk

structure AlgSet (K : Type ℓ) [Field K] (n : ℕ) : Type ℓ where
  V : Set (ℙ K n)
  is_algebraic : ∃ I : HomogeneousIdeal (K[X,..] n+1 homo), V = 𝕍 I

structure Variety (K : Type ℓ) [Field K] (n : ℕ) : Type ℓ where
  V : Set (ℙ K n)
  is_prime : ∃ I : HomogeneousIdeal (K[X,..] n+1 homo), IsPrime I.toIdeal ∧ V = 𝕍 I

def Variety.toAlgSet (A : Variety K n) : AlgSet K n := {
  V := A.V
  is_algebraic := Exists.elim A.is_prime $ by
    rintro I0 ⟨_, h⟩
    exists I0
}

def singleton (P : ℙ K n) : AlgSet K n := {
  V := {P}
  is_algebraic := by
    exists 𝕞 P
    ext P1
    simp [𝕍, 𝕞]
    simp [←HomogeneousIdeal.mem_iff, HomogeneousIdeal.toIdeal, vanish]
    simp only [Ideal.span, mem_span_set']
    constructor
    . intro Ph g ⟨d, ks, fs, sum_eq_g⟩
      rw [Ph]
      have fsh : ∀ i : Fin d, ∀ P₀ : no0 (𝔸 K (n + 1)), ⟦P₀⟧ = P → (eval P₀.1) (fs i) = 0 := by
        intro i P₀ P₀h
        exact (fs i).2.2 P₀.1 P₀.2 P₀h
      intro P₀ P₀_ne0 P₀_in_P
      simp [←sum_eq_g, eval_sum, smul_eval]
      apply Fintype.sum_eq_zero
      intro i
      apply mul_eq_zero_of_right
      apply (fs i).2.2 P₀ P₀_ne0 P₀_in_P
    . intro fh
      sorry
    -- conv =>
    --   congr
    --   tactic =>
    --     apply Fintype.sum_congr
    --     intro i
    --   simp only [smul_eval]
}

-- def 𝕞 (P : ℙ K n) : HomogeneousIdeal (K[X,..] n+1 homo) :=

def 𝕀 (V : AlgSet K n) : HomogeneousIdeal (K[X,..] n+1 homo) :=
  let fs := {f : K[X,..]n+1
    | ∃ i : ℕ, MvPolynomial.IsHomogeneous f i
    ∧ ∀ P ∈ V.1, ∀ P₀ : no0 (𝔸 K (n + 1)), ⟦P₀⟧ = P → eval P₀ f = 0}
  HomogeneousIdeal.mk (Ideal.span fs) $ by
    apply Ideal.homogeneous_span
    simp [SetLike.Homogeneous, fs]
    intro _ i _ _
    exists i

end ℙ
