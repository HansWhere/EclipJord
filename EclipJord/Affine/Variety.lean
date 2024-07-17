import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.Eval
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Topology.Basic
import Mathlib.Data.Set.Finite
import EclipJord.Affine.Defs
-- import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
open MvPolynomial
open Ideal
open scoped Pointwise

noncomputable section

namespace 𝔸
variable {n : ℕ}
variable {K : Type ℓ} [Field K]

-- abbrev K_cl := AlgebraicClosure K

scoped[MvPolynomial] notation:9000 R "[X,..]" n => MvPolynomial (Fin n) R

abbrev 𝕍 (I : Ideal K[X,..]n) : Set (𝔸 K n)
:= { P : 𝔸 K n | ∀ f ∈ I, eval P f = 0}

instance zariski_topology [DecidableEq K] : TopologicalSpace (𝔸 K n) where
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

#check Set.toFinset

#check (X 0 ^ 2 + X 1 + 1 : MvPolynomial (Fin 2) ℚ)

-- def AlgSet (K : Type ℓ) [Field K] (n : ℕ) : Set (Set (𝔸 K n))
-- := { V | ∃ I : Ideal K[X,..]n, V = 𝕍 I }

-- structure AlgSet (K : Type ℓ) [Field K] (n : ℕ) : Type ℓ where
--   V : Set (𝔸 K n)
--   I : Ideal K[X,..]n
--   algebraic : V = 𝕍 I

structure AlgSet (K : Type ℓ) [Field K] (n : ℕ) : Type ℓ where
  V : Set (𝔸 K n)
  is_algebraic : ∃ I : Ideal K[X,..]n, V = 𝕍 I

structure Variety (K : Type ℓ) [Field K] (n : ℕ) : Type ℓ where
  V : Set (𝔸 K n)
  is_prime : ∃ I : Ideal K[X,..]n, IsPrime I ∧ V = 𝕍 I

def Variety.toAlgSet (A : Variety K n) : AlgSet K n := {
  V := A.V
  is_algebraic := Exists.elim A.is_prime $ by
    rintro I0 ⟨_, h⟩
    exists I0
}

-- def 𝕀 (V : AlgSet) : Ideal K[X,..]n := {f : K[X,..]n | }
