import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.Eval
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Noetherian
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Topology.Basic
import Mathlib.Order.BooleanAlgebra
import Mathlib.Data.Set.Finite
-- import EclipJord.Affine.Module
open MvPolynomial
open Ideal
open scoped Pointwise

abbrev 𝔸 (R : Type ℓ) [Ring R] (n : ℕ) : Type ℓ := Fin n → R

noncomputable section

namespace 𝔸
variable {n : ℕ}
variable {K : Type ℓ} [Field K]

scoped[MvPolynomial] notation:9000 R "[X,..]" n => MvPolynomial (Fin n) R

abbrev 𝕍 (I : Ideal K[X,..]n) : Set (𝔸 K n)
:= { P : 𝔸 K n | ∀ f ∈ I, eval P f = 0}

instance zariski_topology [DecidableEq K]  : TopologicalSpace (𝔸 K n) where
  IsOpen U := ∃ I : Ideal K[X,..]n, U = (𝕍 I)ᶜ
  isOpen_univ := by
    simp [𝕍]
    exists ⊤
    ext P
    simp
    exists 1
    simp
  isOpen_inter := by
    rintro U1 U2 ⟨I1, U1_open⟩ ⟨I2, U2_open⟩
    simp only [U1_open, U2_open, compl, 𝕍]
    exists I1 * I2
    ext P; simp; constructor
    rintro ⟨⟨f1, ⟨f1_in_I1, P_notin_V1⟩⟩, ⟨f2, ⟨f2_in_I2, P_notin_V2⟩⟩⟩
    exists f1 * f2
    simp [mul_mem_mul f1_in_I1 f2_in_I2, P_notin_V1, P_notin_V2]
    rintro ⟨f, ⟨f_in_I1I2, P_notin_V⟩⟩
    constructor
    exists f
    constructor
    apply mul_le_right
    exact f_in_I1I2
    exact P_notin_V
    exists f
    constructor
    apply mul_le_left
    exact f_in_I1I2
    exact P_notin_V
  isOpen_sUnion := by
    intros Us Us_open
    simp at Us_open
    choose I_of U_eq_VIUc using Us_open
    let uU := {f | ∃ U, ∃ in_Us : U ∈ Us, f ∈ I_of U in_Us}
    exists span uU
    rw [←compl_inj_iff, compl_compl, Set.compl_sUnion Us]
    ext P; simp; constructor
    intros P_not_in_any_U f f_in_SumU
    conv at P_not_in_any_U => {
      enter [U, in_Us]
      rw [U_eq_VIUc U in_Us]
      simp
      enter [g]
    }
    have fP_in : (eval P) f ∈ map (eval P) (span uU)
    := mem_map_of_mem (eval P) f_in_SumU
    conv at fP_in => {
      rw [map_span (eval P) uU]
      arg 2
      congr
      simp [Set.image]
    }
    have : span {x | ∃ g ∈ uU, (eval P) g = x} = ⊥
    := by
      simp [uU]
      rw [le_antisymm_iff, span_le]
      simp
      intros Q g U in_Us in_IU gP_isQ
      rw [←gP_isQ, P_not_in_any_U U in_Us g in_IU]
    simp [this] at fP_in
    exact fP_in
    -------------------------
    intros uUP_is0 U in_Us
    rw [U_eq_VIUc U in_Us]; simp
    intros f in_IU
    have in_uU : f ∈ uU := by simp [uU]; exists U, in_Us
    have : uU ⊆ span uU := subset_span
    rw [Set.subset_def] at this
    exact uUP_is0 f (this f in_uU)


    -- rintro ⟨U, ⟨in_Us, P_in_U⟩⟩
    -- #check I_of U in_Us

    -- exists P
    -- have Us_cc : Us = compl '' (compl '' Us) := by
    --   simp [←(Set.image_comp compl compl)]
    -- rw [←compl_inj_iff, compl_compl]
    -- conv in ⋃₀ Us => {}
    -- have I : Ideal K[X,..]n := sorry
    -- have Vs_cc : Vs = compl '' (compl '' Vs) := by
    --   simp [←(Set.image_comp compl compl)]
    -- rw [Vs_cc, ←Set.compl_sInter]
    -- have xxx : ⋃₀ (compl '' S) = (⋂₀ S)ᶜ
    -- := ⋂


    ---
    -- rcases IsNoetherian.noetherian I1 with ⟨fs1, fs1_span⟩
    -- rcases IsNoetherian.noetherian I2 with ⟨fs2, fs2_span⟩
    -- simp [←fs1_span, ←fs2_span] at f_in_I1I2
    -- simp [Ideal.span_mul_span fs1.toSet fs2.toSet] at f_in_I1I2
    -- -- have := mem_span_finset.mp f_in_I1I2
    -- have f_in_I1I2_correct : f ∈ Ideal.span (fs1*fs2) := by
    --   convert f_in_I1I2
    --   ext
    --   simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff, Finset.mem_coe,
    --     Finset.mem_mul]
    --   apply exists_congr (λ x ↦ and_congr (by rfl) ?_)
    --   apply exists_congr (λ x ↦ and_congr (by rfl) ?_)
    --   rw [mul_comm, eq_comm]
    -- have ⟨gs, sgs_eq_f⟩ := mem_span_finset.mp f_in_I1I2_correct
    -- have sgs_eq_ssgs :
    --   ∑ ff ∈ fs1 * fs2, gs ff • ff = ∑ f1 ∈ fs1, ∑ f2 ∈ fs2, gs (f1*f2) • (f1*f2) := by
    --   simp [Set.mul, Finset.sum_product]


    -- #check mem_span_finset.mp




-- def zero_locus (fs : Finset (K[X,..]n)) : Set (𝔸 K n)
-- := { P : 𝔸 K n | ∀ f ∈ fs, eval (𝔸toF P) f = 0}

-- instance zariski_topology [DecidableEq K] : TopologicalSpace (𝔸 K n) where
--   IsOpen U := ∃ fs : Finset (K[X,..]n), U = (zero_locus fs)ᶜ
--   isOpen_inter U1 U2 U1open U2open := by
--     simp
--     simp at U1open U2open
--     rcases U1open with ⟨fs1, U1_open⟩
--     rcases U2open with ⟨fs2, U2_open⟩
--     rw [U1_open, U2_open]
--     let fs := ((fs1.toList.product fs2.toList).map $ λ (f1,f2) ↦ f1*f2).toFinset
--     exists fs
--     ext P
--     simp [compl, zero_locus]
--     apply Iff.intro
--     rintro ⟨⟨f1, ⟨_, f1_ne0_atP⟩⟩, ⟨f2, ⟨_, f2_ne0_atP⟩⟩⟩
--     exists f1*f2
--     simp [f1_ne0_atP, f2_ne0_atP, fs]
--     exists f1, f2
--     simp [fs]
--     intro f f1 f2 f1_in_fs1 f2_in_fs2 f1f2_is_f f_ne0_atP
--     simp [←f1f2_is_f, eval_mul] at f_ne0_atP
--     constructor
--     exists f1
--     simp [f1_in_fs1, f_ne0_atP]
--     exists f2
--     simp [f2_in_fs2, f_ne0_atP]
--   isOpen_sUnion := by



#check Set.toFinset

#check (X 0 ^ 2 + X 1 + 1 : MvPolynomial (Fin 2) ℚ)
