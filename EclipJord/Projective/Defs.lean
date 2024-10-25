import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Defs
import EclipJord.Affine.Defs
import Init.Core

-- def no0 (M : Type ℓ) [AddCommMonoid M] : Type ℓ := {x : M // x ≠ 0}

-- structure no0 (A : Type ℓ) [Zero A] : Type ℓ where
--   carrier : A
--   ne0 : carrier ≠ 0

abbrev no0 (A : Type ℓ) [Zero A] : Type ℓ := {x : A // x ≠ 0}

variable {K : Type ℓ} [Field K]
variable {n : ℕ}

namespace 𝔸

instance : NoZeroSMulDivisors K (𝔸 K n) where
  eq_zero_or_eq_zero_of_smul_eq_zero := by
    intros k P kPh
    simp [𝔸] at P
    have kPh' := congrFun kPh
    simp [forall_or_left] at kPh'
    cases kPh'
    case inl h => left; assumption
    case inr h => right; exact funext h

namespace no0

def mul' (a b : no0 K) : no0 K := ⟨a.1 * b.1, by simp [a.2, b.2]⟩

theorem mul_assoc' : ∀ (a b c : no0 K), mul' (mul' a b) c = mul' a (mul' b c) := by
  intros a b c
  simp only [mul', mul_assoc]

def one' : no0 K := ⟨1, by simp⟩

theorem one_mul' : ∀ (a : no0 K), mul' one' a = a := by
  intro ⟨a1, ah⟩
  simp [mul', one']

theorem mul_one' : ∀ (a : no0 K), mul' a one' = a := by
  intro ⟨a, ah⟩
  simp [mul', one']

def inv' (a : no0 K) : no0 K := ⟨a.1⁻¹, by simp [a.2]⟩

theorem mul_left_inv' : ∀ (a : no0 K), mul' (inv' a) a = one' := by
  intro ⟨a, ah⟩
  simp [mul', inv', one']
  rw [←mul_inv_cancel ah]
  apply mul_comm

theorem mul_comm' : ∀ (a b : no0 K), mul' a b = mul' b a := by
  intro a b
  simp only [mul', mul_comm]

instance : CommGroup (no0 K) where
  mul := mul'
  mul_assoc := mul_assoc'
  one := one'
  one_mul := one_mul'
  mul_one := mul_one'
  inv := inv'
  mul_left_inv := mul_left_inv'
  mul_comm := mul_comm'

@[simp]
def smul' (k : no0 K) (P: no0 (𝔸 K n)) : no0 (𝔸 K n) := ⟨ k.1 • P.1, by
  intro kPh
  rw [smul_eq_zero] at kPh
  cases kPh
  case inl h => exact absurd h k.2
  case inr h => exact absurd h P.2
⟩

theorem one_smul' : ∀ (b : no0 (𝔸 K n)), smul' one' b = b := by
  intro b
  simp [smul', one']

theorem mul_smul' : ∀ (x y : no0 K) (b : no0 (𝔸 K n))
, smul' (mul' x y) b = smul' x (smul' y b) := by
  intro ⟨x, xh⟩ ⟨y, yh⟩ ⟨b, bh⟩
  simp only [smul', mul', mul_smul]

instance : MulAction (no0 K) (no0 (𝔸 K n)) where
  smul := smul'
  one_smul := one_smul'
  mul_smul := mul_smul'

@[simp]
abbrev collinear : no0 (𝔸 K n) → no0 (𝔸 K n) → Prop
| xs, ys => ∃ k : no0 K, xs = k • ys

namespace collinear

theorem refl' (xs : no0 (𝔸 K n))
: collinear xs xs := by
  dsimp [collinear]
  exists 1
  simp

theorem symm' {xs ys : no0 (𝔸 K n)}
: collinear xs ys → collinear ys xs := by
  rintro ⟨k, h⟩
  exists k⁻¹
  symm
  simp [h]

theorem trans' {xs ys zs : no0 (𝔸 K n)}
: collinear xs ys → collinear ys zs → collinear xs zs := by
  rintro ⟨k1, h1⟩ ⟨k2, h2⟩
  exists k1 * k2
  rw [mul_smul, ←h2]
  exact h1

instance eqv {n : ℕ} : Setoid (no0 (𝔸 K n)) where
  r := collinear
  iseqv := {
    refl := refl',
    symm := symm',
    trans := trans'
  }

theorem smul_closed (P₀ : no0 (𝔸 K n))
: ∀ k : no0 K, Quotient.mk eqv (k • P₀) = Quotient.mk eqv (P₀) := by
  intro k
  simp [collinear]
  exists k

end collinear

end no0

end 𝔸

def ℙ (K : Type ℓ) [Field K] (n : ℕ) : Type ℓ :=
  Quotient (𝔸.no0.collinear.eqv : Setoid (no0 (𝔸 K n.succ)))

namespace ℙ

notation "𝔸≃" => 𝔸.no0.collinear.eqv

abbrev mk : no0 (𝔸 K n.succ) → ℙ K n
:= Quotient.mk (𝔸≃ : Setoid (no0 (𝔸 K n.succ)))

@[simp]
theorem eq_iff (P₁ P₂ : no0 (𝔸 K n.succ))
: @Quotient.mk _ 𝔸≃ P₁ = ⟦P₂⟧ ↔ 𝔸.no0.collinear P₁ P₂ := by
  simp only [@Quotient.eq (no0 (𝔸 K n.succ)), 𝔸.no0.collinear.eqv, .≈.]

example : [1, 2, 3] ≠ [3, 2, 1] := by decide

example : (⟪3, 2, 1⟫ : 𝔸 ℚ 3) ≠ 0 := by decide

example : ℙ ℚ 3 := ℙ.mk ⟨⟪3,2,3,2⟫, by decide⟩

example : ℙ ℚ 3 := ℙ.mk ⟨⟪3,2,3,2.1⟫, by decide⟩

example : ℙ ℚ 3 := ℙ.mk ⟨⟪3,2,3/2,2.1⟫, by decide⟩

example : ℙ ℚ 3 := ℙ.mk ⟨⟪3,2-2,3/2,2.1⟫, by decide⟩

-- example : ℙ ℚ 3 := ℙ.of ⟨⟪3+1,2-2,3/2,2.1⟫, by decide⟩
-- (why tactic 'decide' failed?)

example : ℙ ℚ 3 := ℙ.mk ⟨⟪0,2,3,2⟫, by decide⟩

end ℙ
