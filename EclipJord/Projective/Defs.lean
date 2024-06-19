import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Module.Defs
import Lean
import EclipJord.Affine.Defs
import Init.Core

variable {K : Type ℓ} [Field K]
variable {n : ℕ}

namespace 𝔸punc
def colli : nonzero (𝔸 K n) → nonzero (𝔸 K n) → Prop
| xs, ys => ∃ k : nonzero K, xs.1 = k.1 • ys.1

theorem colli_refl (xs : nonzero (𝔸 K n))
: colli xs xs := by
  exists ⟨1, one_ne_zero⟩
  simp [one_smul]

theorem colli_symm {xs ys : nonzero (𝔸 K n)}
: colli xs ys → colli ys xs := by
  rintro ⟨k, h⟩
  exists ⟨(k.1)⁻¹, inv_ne_zero k.2⟩
  symm
  rw [h, ←mul_smul, mul_comm, mul_inv_cancel, one_smul]
  exact k.2

theorem colli_trans {xs ys zs : nonzero (𝔸 K n)}
: colli xs ys → colli ys zs → colli xs zs := by
  rintro ⟨k1, h1⟩ ⟨k2, h2⟩
  refine ⟨⟨k1.1 * k2.1, ?_⟩, ?_⟩
  exact mul_ne_zero k1.2 k2.2
  rw [mul_smul, ←h2, ←h1]

instance setoid {n : ℕ} : Setoid (nonzero (𝔸 K n)) where
  r := colli
  iseqv := {
    refl := colli_refl,
    symm := colli_symm,
    trans := colli_trans
  }
end 𝔸punc

def ℙ (K : Type ℓ) [Field K] (n : ℕ) : Type ℓ
:= Quotient (𝔸punc.setoid : Setoid (nonzero (𝔸 K (n+1))))

def ℙ.of [Field K] {n : ℕ} : nonzero (𝔸 K (n+1)) → ℙ K n
:= Quotient.mk (𝔸punc.setoid : Setoid (nonzero (𝔸 K (n+1))))

-- syntax (priority := high) "⟦" term,+ "⟧" : term
-- macro_rules
--   | `(⟦$x⟧) => `(ℙ (cons $x 𝔸.nil))
--   | `(⟦$x, $xs:term,*⟧) => `(ℙ (cons $x ⟦$xs,*⟧))

example : [1, 2, 3] ≠ [3, 2, 1] := by decide

example : (⟪3, 2, 1⟫ : 𝔸 ℚ 3) ≠ 0 := by decide

example : ℙ ℚ 3 := ℙ.of ⟨⟪3,2,3,2⟫, by decide⟩

example : ℙ ℚ 3 := ℙ.of ⟨⟪3,2,3,2.1⟫, by decide⟩

example : ℙ ℚ 3 := ℙ.of ⟨⟪3,2,3/2,2.1⟫, by decide⟩

example : ℙ ℚ 3 := ℙ.of ⟨⟪3,2-2,3/2,2.1⟫, by decide⟩

-- example : ℙ ℚ 3 := ℙ.of ⟨⟪3+1,2-2,3/2,2.1⟫, by decide⟩
-- (why tactic 'decide' failed?)

example : ℙ ℚ 3 := ℙ.of ⟨⟪0,2,3,2⟫, by decide⟩
