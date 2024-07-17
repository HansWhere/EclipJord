import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Module.Defs
import Lean
import EclipJord.Affine.Defs
import Init.Core

variable {K : Type ℓ} [Field K]
variable {n : ℕ}

def no0 (M : Type ℓ) [AddCommMonoid M] : Type ℓ := {x : M // x ≠ 0}

namespace 𝔸
def collinear : no0 (𝔸 K n) → no0 (𝔸 K n) → Prop
| xs, ys => ∃ k : no0 K, xs.1 = k.1 • ys.1

theorem collinear_refl (xs : no0 (𝔸 K n))
: collinear xs xs := by
  exists ⟨1, one_ne_zero⟩
  simp [one_smul]

theorem collinear_symm {xs ys : no0 (𝔸 K n)}
: collinear xs ys → collinear ys xs := by
  rintro ⟨k, h⟩
  exists ⟨(k.1)⁻¹, inv_ne_zero k.2⟩
  symm
  rw [h, ←mul_smul, mul_comm, mul_inv_cancel, one_smul]
  exact k.2

theorem collinear_trans {xs ys zs : no0 (𝔸 K n)}
: collinear xs ys → collinear ys zs → collinear xs zs := by
  rintro ⟨k1, h1⟩ ⟨k2, h2⟩
  refine ⟨⟨k1.1 * k2.1, ?_⟩, ?_⟩
  exact mul_ne_zero k1.2 k2.2
  rw [mul_smul, ←h2, ←h1]

instance setoid {n : ℕ} : Setoid (no0 (𝔸 K n)) where
  r := collinear
  iseqv := {
    refl := collinear_refl,
    symm := collinear_symm,
    trans := collinear_trans
  }
end 𝔸

def ℙ (K : Type ℓ) [Field K] (n : ℕ) : Type ℓ
:= Quotient (𝔸.setoid : Setoid (no0 (𝔸 K (n+1))))

namespace ℙ

def of [Field K] {n : ℕ} : no0 (𝔸 K (n+1)) → ℙ K n
:= Quotient.mk (𝔸.setoid : Setoid (no0 (𝔸 K (n+1))))

example : [1, 2, 3] ≠ [3, 2, 1] := by decide

example : (⟪3, 2, 1⟫ : 𝔸 ℚ 3) ≠ 0 := by decide

example : ℙ ℚ 3 := ℙ.of ⟨⟪3,2,3,2⟫, by decide⟩

example : ℙ ℚ 3 := ℙ.of ⟨⟪3,2,3,2.1⟫, by decide⟩

example : ℙ ℚ 3 := ℙ.of ⟨⟪3,2,3/2,2.1⟫, by decide⟩

example : ℙ ℚ 3 := ℙ.of ⟨⟪3,2-2,3/2,2.1⟫, by decide⟩

-- example : ℙ ℚ 3 := ℙ.of ⟨⟪3+1,2-2,3/2,2.1⟫, by decide⟩
-- (why tactic 'decide' failed?)

example : ℙ ℚ 3 := ℙ.of ⟨⟪0,2,3,2⟫, by decide⟩

end ℙ
