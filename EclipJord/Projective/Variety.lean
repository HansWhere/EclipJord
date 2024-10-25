import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.Eval
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
-- import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.GradedAlgebra.HomogeneousIdeal
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Topology.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Set.Finite
import EclipJord.Affine.Variety
import EclipJord.Projective.AffineChart
open MvPolynomial
open Ideal

variable {n : ℕ} {K : Type ℓ} [Field K]

noncomputable section
scoped[MvPolynomial] notation:9000 R "[X,..]" n "homo"
  => (homogeneousSubmodule (Fin n) R)

instance : GradedRing (K[X,..]n homo) := MvPolynomial.gradedAlgebra

namespace MvPolynomial

theorem eval_smul_homo [Field K] : ∀ P₀ : 𝔸 K n, ∀ f : K[X,..]n, ∀ k : K, ∀ d : ℕ,
    k^d * (eval P₀ (homogeneousComponent d f))
    = eval (k • P₀) (homogeneousComponent d f) := by
  intro P₀ f k d
  have fh := homogeneousComponent_isHomogeneous d f
  simp only [MvPolynomial.IsHomogeneous, IsWeightedHomogeneous,
    weightedDegree_one, degree, coeff] at fh
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

def dehX (j : Fin n.succ) (i : Fin n.succ) : K[X,..]n :=
    if oh : i < j then X ⟨i.1, by
      have jh := j.2
      simp [LT.lt, Nat.lt] at oh jh
      exact Nat.le_trans oh jh
    ⟩
    else if ohh : i = j then 1
    else match i with
      | ⟨.zero, _⟩ => by
        simp at oh ohh
        exact (ohh oh.symm).elim
      | ⟨.succ i₀, i₀h⟩ => X ⟨i₀, Nat.le_of_succ_le_succ i₀h⟩

def dehomogenization (j : Fin n.succ) : (K[X,..]n.succ) →ₐ[K] K[X,..]n :=
  aeval (dehX j)

def embX (j : Fin n.succ) (i : Fin n) : K[X,..]n.succ :=
  if i < j then X i.1.cast
  else X i.1.succ.cast

def dehX_embX_cancel (j : Fin n.succ) (i : Fin n):
    (aeval (dehX j)) (@embX n K _ j i) = @X K _ _ i
:= by
  simp [embX]
  rcases i with ⟨i, i_n⟩
  rcases j with ⟨j, j_n⟩
  if oh : i < j then
    simp [oh, dehX]
  else
    simp [oh, dehX]
    simp at oh
    have : ¬ i.succ < j := by
      linarith
    simp [this]
    intro
    exact (show False by linarith).elim

def homogenization (j : Fin n.succ) (p : K[X,..]n) : (K[X,..]n.succ) :=
  ∑ m ∈ p.support,
    aeval (embX j) (monomial m (coeff m p)) * (X j)^(p.totalDegree + 1 - degree m)

theorem dehomo_homo
    : Function.LeftInverse (@dehomogenization n K _ j) (@homogenization n K _ j) := by
  simp [Function.LeftInverse, dehomogenization]
  intro p
  simp [homogenization, dehX]
  conv =>
    arg 2
    rw [as_sum p]
  congr
  ext m' m
  rw [monomial_eq]
  simp [or_iff_not_imp_right]
  intro
  conv =>
    arg 1; arg 2
    tactic =>
      apply Finset.prod_congr rfl
      intros
    rw [dehX_embX_cancel]


theorem ker_dehomo
    : RingHom.ker (dehomogenization j) = Ideal.span {@X K (Fin n.succ) _ j - 1} := by
  simp only [RingHom.ker]
  ext p
  rw [Ideal.mem_span_singleton', Ideal.mem_comap]
  simp [dehomogenization] --
  rw [as_sum p, aeval_sum]
  conv =>
    arg 1; arg 1
    tactic =>
      apply Finset.sum_congr rfl
      intro m mh
    rw [aeval_monomial]
    simp --[dehX, Finsupp.prod]
  simp
  constructor
  .
    sorry
  . simp
    intro q eq_p
    rw [←eq_p]
    simp [dehX]
    sorry

end MvPolynomial

def HomogeneousIdeal.dehomogenization (j : Fin n.succ)
(I : HomogeneousIdeal (K[X,..]n.succ homo)) : Ideal K[X,..]n :=
  I.toIdeal.map (MvPolynomial.dehomogenization j)

namespace ℙ
variable {n d : ℕ}

def vanish (P : ℙ K n) (f : K[X,..] n+1) : Prop
:= ∀ P₀ : no0 (𝔸 K (n+1)), ℙ.mk P₀ = P → eval P₀.1 f = 0

end ℙ

abbrev HomogeneousIdeal.zero_locus (I : HomogeneousIdeal K[X,..] n+1 homo)
    : Set (ℙ K n) :=
  { P : ℙ K n | ∀ f ∈ I, P.vanish f}

namespace ℙ

structure AlgSet (K : Type ℓ) [Field K] (n : ℕ) : Type ℓ where
  carrier : Set (ℙ K n)
  gen_by_ideal : ∃ I : HomogeneousIdeal (K[X,..] n+1 homo), I.zero_locus = carrier

namespace AlgSet

instance : SetLike (AlgSet K n) (ℙ K n) :=
  ⟨carrier, λ p q ↦ by cases p; cases q; congr!⟩

@[simp]
lemma mem_carrier {p : AlgSet K n} : x ∈ p.carrier ↔ x ∈ (p : Set (ℙ K n)) := Iff.rfl

@[ext]
theorem ext {p q : AlgSet K n} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := SetLike.ext h

protected def copy (p : AlgSet K n) (s : Set (ℙ K n)) (hs : s = ↑p) : AlgSet K n :=
  { carrier := s
    gen_by_ideal := hs.symm ▸ p.gen_by_ideal }

@[simp] lemma coe_copy (p : AlgSet K n) (s : Set (ℙ K n)) (hs : s = ↑p) :
  (p.copy s hs : Set (ℙ K n)) = s := rfl

lemma copy_eq (p : AlgSet K n) (s : Set (ℙ K n)) (hs : s = ↑p) : p.copy s hs = p :=
  SetLike.coe_injective hs

end AlgSet

def 𝕍 (I : HomogeneousIdeal (K[X,..] n+1 homo)) : AlgSet K n := ⟨I.zero_locus, by exists I⟩

structure Variety (K : Type ℓ) [Field K] (n : ℕ) : Type ℓ where
  carrier : Set (ℙ K n)
  gen_by_prime : ∃ I : HomogeneousIdeal (K[X,..] n+1 homo),
    I.toIdeal.IsPrime ∧ 𝕍 I = carrier

namespace Variety

def toAlgSet (V : Variety K n) : AlgSet K n := {
  carrier := V.carrier
  gen_by_ideal := Exists.elim V.gen_by_prime $ by
    rintro I₀ ⟨_, h⟩
    exists I₀
}

instance : SetLike (Variety K n) (ℙ K n) :=
  ⟨carrier, λ p q ↦ by cases p; cases q; congr!⟩

@[simp]
lemma mem_carrier {p : Variety K n} : x ∈ p.carrier ↔ x ∈ (p : Set (ℙ K n)) := Iff.rfl

@[ext]
theorem ext {p q : Variety K n} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := SetLike.ext h

protected def copy (p : Variety K n) (s : Set (ℙ K n)) (hs : s = ↑p) : Variety K n :=
  { carrier := s
    gen_by_prime := hs.symm ▸ p.gen_by_prime }

@[simp] lemma coe_copy (p : Variety K n) (s : Set (ℙ K n)) (hs : s = ↑p) :
  (p.copy s hs : Set (ℙ K n)) = s := rfl

lemma copy_eq (p : Variety K n) (s : Set (ℙ K n)) (hs : s = ↑p) : p.copy s hs = p :=
  SetLike.coe_injective hs

def 𝔸chart (j : Fin n.succ) (V : Variety K n) : 𝔸.Variety K n where
  carrier := (AffineChart K n j).invFun '' { P : Part K n j | P.1 ∈ V.1 }
  gen_by_prime := by
    rcases V with ⟨V, I, I_prime, 𝕍I_eq_V⟩
    -- intro V₀
    exists I.dehomogenization j
    simp [HomogeneousIdeal.dehomogenization]
    constructor
    . if kerh : RingHom.ker (dehomogenization j) ≤ I.toIdeal then
        apply Ideal.map_isPrime_of_surjective
        . exact dehomo_homo.surjective
        . exact kerh
      else
        sorry
    .
      simp [←𝕍I_eq_V, Set.image, AffineChart, 𝔸.𝕍, Ideal.map, dehomogenization]
      ext P
      simp
      constructor
      . intro
        sorry
      . intro
        sorry



-- def Singleton (P : ℙ K n) : Variety K n := {
--   carrier := {P}
--   gen_by_prime := by
--     let fs := {f : K[X,..]n+1
--       | ∃ i : ℕ, MvPolynomial.IsHomogeneous f i
--       ∧ ∀ P₀ : no0 (𝔸 K (n + 1)), ⟦P₀⟧ = P → eval P₀ f = 0}
--     exists HomogeneousIdeal.mk (Ideal.span fs) $ by
--       apply Ideal.homogeneous_span
--       simp [SetLike.Homogeneous, fs]
--       intro _ i _ _
--       exists i
--     simp only [fs, HomogeneousIdeal.toIdeal, 𝕍]
--     constructor
--     rw [isPrime_iff]
--     constructor
--     . rw [ne_top_iff_one, ←submodule_span_eq, mem_span_set']
--       push_neg
--       intro m ks fs' h
--       -- have contrad : @Eq K 0 1 := by
--       have ctr := congr_arg (eval P.out.1) h
--       simp at ctr
--       conv at ctr =>
--         congr
--         tactic =>
--           apply Fintype.sum_congr
--           intro i
--           have fsh := (fs' i).2
--           dsimp at fsh
--           rcases fsh with ⟨fsh1, fsh21, fsh22⟩
--         conv =>
--           arg 2
--           simp [fsh22 P.out (Quotient.out_eq P)]
--         rw [mul_zero]
--       rw [Fintype.sum_eq_zero] at ctr
--       apply @zero_ne_one K
--       exact ctr
--       intro
--       trivial
--     . intro f g fgh
--       rw [or_iff_not_imp_left]
--       intro fnh
--       sorry
--     . sorry
-- }

end Variety

def 𝔸.AlgSet.ℙclosure

def 𝕀 (V : AlgSet K n) : HomogeneousIdeal (K[X,..] n+1 homo) :=
  let fs := {f : K[X,..]n+1
    | ∃ i : ℕ, MvPolynomial.IsHomogeneous f i
    ∧ ∀ P ∈ V, ∀ P₀ : no0 (𝔸 K (n + 1)), ⟦P₀⟧ = P → eval P₀ f = 0}
  HomogeneousIdeal.mk (Ideal.span fs) $ by
    apply Ideal.homogeneous_span
    simp [SetLike.Homogeneous, fs]
    intro _ i _ _
    exists i

def 𝕞 (P : ℙ K n) : HomogeneousIdeal (K[X,..] n+1 homo) :=
  let fs := {f : K[X,..]n+1
    | ∃ i : ℕ, MvPolynomial.IsHomogeneous f i
    ∧ ∀ P₀ : no0 (𝔸 K (n + 1)), ⟦P₀⟧ = P → eval P₀ f = 0}
  HomogeneousIdeal.mk (Ideal.span fs) $ by
    apply Ideal.homogeneous_span
    simp [SetLike.Homogeneous, fs]
    intro _ i _ _
    exists i

-- def singleton (P : ℙ K n) : AlgSet K n := {
--   V := {P}
--   is_algebraic := by
--     exists 𝕞 P
--     ext P1
--     simp [𝕍, 𝕞]
--     simp [←HomogeneousIdeal.mem_iff, HomogeneousIdeal.toIdeal, vanish]
--     simp only [Ideal.span, mem_span_set']
--     constructor
--     . intro Ph g ⟨d, ks, fs, sum_eq_g⟩
--       rw [Ph]
--       have fsh : ∀ i : Fin d, ∀ P₀ : no0 (𝔸 K (n + 1)), ⟦P₀⟧ = P → (eval P₀.1) (fs i) = 0 := by
--         intro i P₀ P₀h
--         exact (fs i).2.2 P₀.1 P₀.2 P₀h
--       intro P₀ P₀_ne0 P₀_in_P
--       simp [←sum_eq_g, eval_sum, smul_eval]
--       apply Fintype.sum_eq_zero
--       intro i
--       apply mul_eq_zero_of_right
--       apply (fs i).2.2 P₀ P₀_ne0 P₀_in_P
--     . intro fh
--       sorry
    -- conv =>
    --   congr
    --   tactic =>
    --     apply Fintype.sum_congr
    --     intro i
    --   simp only [smul_eval]
-- }

theorem canc_𝕍𝕀 (V : AlgSet K n) : 𝕍 (𝕀 V) = V := by
  ext P₁
  dsimp [𝕍, 𝕀]
  rcases V with ⟨V, I, VIh⟩
  simp [HomogeneousIdeal.zero_locus, Set.ext_iff] at VIh
  constructor
  . intro P₁h
    show P₁ ∈ V
    rw [←(VIh P₁)]
    intro g gh
    apply P₁h
    show g ∈ span _
    sorry

  -- . rw [←not_imp_not]
  --   simp [HomogeneousIdeal.zero_locus, .∈., Set.Mem, SetLike.coe,
  --     setOf, HomogeneousIdeal.toIdeal]
  --   -- simp [HomogeneousIdeal.zero_locus, .∈., Set.Mem, SetLike.coe] --...
  --   -- push_neg
  --   intro Ph
  --   exists sorry

  sorry

theorem canc_𝕀𝕍 (I : HomogeneousIdeal (K[X,..] n+1 homo)) : 𝕀 (𝕍 I) = I.radical := by
  sorry

abbrev AlgSet.coordRing (V : AlgSet K n) : Type ℓ :=
  (K[X,..]n + 1) ⧸ (𝕀 V).toIdeal

-- def AlgSet.𝕞 (V : AlgSet K n) (P : ℙ K n) (Ph : P ∈ V.1)

abbrev Variety.coordRing (V : Variety K n) : Type ℓ :=
  V.toAlgSet.coordRing

end ℙ
