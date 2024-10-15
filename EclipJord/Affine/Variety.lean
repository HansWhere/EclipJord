import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.Eval
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Nullstellensatz
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

theorem MvPolynomial.dvd_iff_eval_zero {f : K[X,..]n}
    : (X i - C a) ∣ f ↔ ∀ P : 𝔸 K n, P i = a → eval P f = 0 := by
  constructor
  . simp [.∣.]
    intro p dvd_f P Ph
    simp [dvd_f, Ph]
  .
    rw [←not_imp_not]
    simp [.∣.]
    intro P
    sorry

-- abbrev 𝕍 (I : Ideal K[X,..]n) : Set (𝔸 K n)
--   := { P : 𝔸 K n | ∀ f ∈ I, eval P f = 0}

abbrev 𝕍 (I : Ideal K[X,..]n) : Set (𝔸 K n) := zeroLocus I

instance zariski_topology [DecidableEq K] : TopologicalSpace (𝔸 K n) where
  IsOpen U := ∃ I : Ideal K[X,..]n, U = (𝕍 I)ᶜ
  isOpen_univ := by
    simp [𝕍]
    exists ⊤
    ext P
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
  carrier : Set (𝔸 K n)
  gen_by_ideal : ∃ I : Ideal K[X,..]n, 𝕍 I = carrier

def Set.isAlgebraic (V : Set (𝔸 K n)) : Prop := ∃ I : Ideal K[X,..]n, 𝕍 I = V

-- def 𝕀 (V : AlgSet K n) : Ideal K[X,..]n where
--   carrier := {f : K[X,..]n | ∀ P ∈ V.1, eval P f = 0}
--   add_mem' := by
--     intro f g fh gh
--     simp at fh gh ⊢
--     intro P Ph
--     rw [fh P Ph, gh P Ph]
--     simp
--   zero_mem' := by
--     simp
--   smul_mem' := by
--     intro c f fh
--     simp at fh ⊢
--     intro P Ph
--     right
--     exact fh P Ph

def 𝕀 (V : AlgSet K n) : Ideal K[X,..]n := MvPolynomial.vanishingIdeal V.1

def AlgSet.coordRing (V : AlgSet K n) : Type ℓ := (K[X,..]n) ⧸ (𝕀 V)

-- instance (V : AlgSet K n) : Ring (V.coordRing) :=

-- def 𝕞 (P : 𝔸 K n) : Ideal K[X,..]n := Ideal.span { f : K[X,..]n | ∃ i, X i - C (P i) = f}
def 𝕞 (P : 𝔸 K n) : Ideal K[X,..]n := 𝕀 {P}

namespace AlgSet

instance : SetLike (AlgSet K n) (𝔸 K n) :=
  ⟨carrier, λ p q ↦ by cases p; cases q; congr!⟩

@[simp]
lemma mem_carrier {p : AlgSet K n} : x ∈ p.carrier ↔ x ∈ (p : Set (𝔸 K n)) := Iff.rfl

@[ext]
theorem ext {p q : AlgSet K n} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := SetLike.ext h

protected def copy (p : AlgSet K n) (s : Set (𝔸 K n)) (hs : s = ↑p) : AlgSet K n :=
  { carrier := s
    gen_by_ideal := hs.symm ▸ p.gen_by_ideal }

@[simp] lemma coe_copy (p : AlgSet K n) (s : Set (𝔸 K n)) (hs : s = ↑p) :
  (p.copy s hs : Set (𝔸 K n)) = s := rfl

lemma copy_eq (p : AlgSet K n) (s : Set (𝔸 K n)) (hs : s = ↑p) : p.copy s hs = p :=
  SetLike.coe_injective hs

def singleton (P : 𝔸 K n) : AlgSet K n where
  carrier := {P}
  gen_by_ideal := by
    exists 𝕞 P
    ext P'
    simp [𝕍, 𝕞]
    constructor
    . intro fh
      ext ⟨i, i_lt_n⟩


      -- rw [←not_imp_not]
      -- intro P'_ne_P

      sorry
    . sorry

end AlgSet

def AlgSet.𝕞 (P : 𝔸 K n) (V : AlgSet K n) : Ideal V.coordRing := 𝕞 P

structure Variety (K : Type ℓ) [Field K] (n : ℕ) : Type ℓ where
  carrier : Set (𝔸 K n)
  gen_by_prime : ∃ I : Ideal K[X,..]n, IsPrime I ∧ 𝕍 I = carrier

namespace Variety

instance : SetLike (Variety K n) (𝔸 K n) :=
  ⟨carrier, λ p q ↦ by cases p; cases q; congr!⟩

@[simp]
lemma mem_carrier {p : Variety K n} : x ∈ p.carrier ↔ x ∈ (p : Set (𝔸 K n)) := Iff.rfl

@[ext]
theorem ext {p q : Variety K n} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := SetLike.ext h

protected def copy (p : Variety K n) (s : Set (𝔸 K n)) (hs : s = ↑p) : Variety K n :=
  { carrier := s
    gen_by_prime := hs.symm ▸ p.gen_by_prime }

@[simp] lemma coe_copy (p : Variety K n) (s : Set (𝔸 K n)) (hs : s = ↑p) :
  (p.copy s hs : Set (𝔸 K n)) = s := rfl

lemma copy_eq (p : Variety K n) (s : Set (𝔸 K n)) (hs : s = ↑p) : p.copy s hs = p :=
  SetLike.coe_injective hs

end Variety

def Variety.toAlgSet (A : Variety K n) : AlgSet K n := {
  carrier := A.carrier
  gen_by_ideal := Exists.elim A.gen_by_prime $ by
    rintro I0 ⟨_, h⟩
    exists I0
}


end 𝔸
