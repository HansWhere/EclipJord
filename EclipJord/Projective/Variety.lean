import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.Eval
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Monad
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
scoped[MvPolynomial] notation:9000 R "[X,..]" n "homo" => (homogeneousSubmodule (Fin n) R)

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
        have := ohh oh.symm
        contradiction
      | ⟨.succ i₀, i₀h⟩ => X ⟨i₀, Nat.le_of_succ_le_succ i₀h⟩

def dehomogenization (j : Fin n.succ) : (K[X,..]n.succ) →ₐ[K] K[X,..]n :=
  aeval (dehX j)

def embX (j : Fin n.succ) (i : Fin n) : K[X,..]n.succ :=
    if i < j then X i.1.cast
    else if i = j then 1
    else X i.1.succ.cast

def dehX_embX_cancel (p : K[X,..]n) (d : ℕ) (j : Fin n.succ) :
    (aeval (dehX j)) ((homogeneousComponent d) (aeval (@embX n K _ j) p))
    = homogeneousComponent d p := by
  simp [homogeneousComponent, weightedHomogeneousComponent,
    weightedDegree, Finsupp.restrictDom]


  sorry

def homogenization (j : Fin n.succ) (p : K[X,..]n) : (K[X,..]n.succ) :=
  let N := p.totalDegree + 1
  ∑ d ∈ Finset.range N, (homogeneousComponent d) (aeval (embX j) p) * (X j)^(N-d)
  -- support := (bind₁ (embX j) p).support

theorem dehomo_surj (j : Fin n.succ)
    : Function.Surjective (@MvPolynomial.dehomogenization n K _ j) := by
  simp [Function.Surjective, dehomogenization]
  intro p
  exists p.homogenization j
  simp [homogenization, dehX]
  conv =>
    arg 2
    rw [←sum_homogeneousComponent p]
  congr
  ext d m
  rw [MvPolynomial.coeff_homogeneousComponent, degree]


end MvPolynomial

def HomogeneousIdeal.dehomogenization (j : Fin n.succ)
(I : HomogeneousIdeal (K[X,..]n.succ homo)) : Ideal K[X,..]n :=
  I.toIdeal.map (MvPolynomial.dehomogenization j)


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

end ℙ

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

abbrev HomogeneousIdeal.zero_locus (I : HomogeneousIdeal K[X,..] n+1 homo) : Set (ℙ K n)
:= { P : ℙ K n | ∀ f ∈ I, P.vanish f}

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

def chart (j : Fin n.succ) (V : Variety K n) : 𝔸.Variety K n where
  carrier := (AffineChart K n j).invFun '' { P : Part K n j | P.1 ∈ V.1 }
  gen_by_prime := by
    rcases V with ⟨V, I, I_prime, 𝕍I_eq_V⟩
    intro V₀
    exists I.dehomogenization j
    simp [HomogeneousIdeal.dehomogenization]
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

abbrev AlgSet.coord_ring (V : AlgSet K n) : Type ℓ :=
  (K[X,..]n + 1) ⧸ (𝕀 V).toIdeal

-- def AlgSet.𝕞 (V : AlgSet K n) (P : ℙ K n) (Ph : P ∈ V.1)

abbrev Variety.coord_ring (V : Variety K n) : Type ℓ :=
  V.toAlgSet.coord_ring

end ℙ
