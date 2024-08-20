-- import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Rat
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Field.Defs

variable {n : ℕ}
variable {R : Type ℓ} [Ring R]
variable {K : Type ℓ} [Field K]

abbrev 𝔸 (R : Type ℓ) [Ring R] (n : ℕ) : Type ℓ := Fin n → R

namespace 𝔸

def nil : 𝔸 R 0 := λ _ ↦ 0

theorem nil_uniq (x0 : 𝔸 R 0) (y0 : 𝔸 R 0) : x0 = y0 := by
  ext ⟨x, x_le0⟩
  contradiction

def cons (x : R) (xs : 𝔸 R n) : 𝔸 R (n + 1) :=
λ m ↦ match m with
  | ⟨0,_⟩ => x
  | ⟨m+1,_⟩ => xs ⟨m, by omega⟩

def cdr (xs : 𝔸 R (n+1)) : 𝔸 R n
:= λ ⟨m, _⟩ ↦ xs ⟨m+1, by omega⟩

infixr: 67 ":::" => cons

syntax (priority := high) "⟪" term,* "⟫" : term
macro_rules
| `(⟪⟫) => `(nil)
| `(⟪$x⟫) => `(cons $x nil)
| `(⟪$x, $xs:term,*⟫) => `(cons $x ⟪$xs,*⟫)

example : 𝔸 ℚ 3 := ⟪1.5,2,3⟫

-- def add' (xs : 𝔸 R n) (ys : 𝔸 R n) : 𝔸 R n :=
--   λ m ↦ xs m + ys m

-- def smul' (r : R) (xs : 𝔸 R n) : 𝔸 R n :=
--   λ m ↦ r * xs m

-- def zero' : 𝔸 R n :=
--   λ _ ↦ 0

-- def nsmul' (k : ℕ) (xs : 𝔸 R n) : 𝔸 R n :=
--   λ m ↦ k * xs m

instance [DecidableEq R] : DecidableEq (𝔸 R n) := by
  simp [𝔸]
  intros xs ys
  induction n
  case zero => right; simp [𝔸.nil_uniq xs ys]
  case succ n ih => if h : xs 0 = ys 0 then
    -- have := ih (cdr xs) (cdr ys)
    if hs : (cdr xs) = (cdr ys) then
      right
      ext ⟨m, m_le_sn⟩
      cases m with
      | zero => exact h
      | succ m => exact congr_fun hs ⟨m, by omega⟩
    else
      left
      intro xs_eq_ys
      apply congrArg cdr at xs_eq_ys
      contradiction
  else
    left
    intro xs_eq_ys
    have := congrFun xs_eq_ys 0
    contradiction

example : [1, 2, 3] ≠ [3, 2, 1] := by decide

example : (⟪3, 2, 1⟫ : 𝔸 ℚ 3) ≠ Zero.zero := by decide

-- instance : SMul R (𝔸 R n) where
--   smul r xs := λ m ↦ r * xs m

#eval (3 • (⟪3, 2, 1⟫ : 𝔸 ℚ 3)) 0

instance : Module R (𝔸 R n) where
  smul := SMul.smul
  one_smul := by
    intro
    funext
    simp
  mul_smul := by
    intros
    funext ⟨m,_⟩
    simp [mul_assoc]
  smul_zero := by
    intro
    funext
    simp
  smul_add := by
    intros
    funext
    simp [mul_add]
  add_smul := by
    intros
    funext
    simp [add_mul]
  zero_smul := by
    intro
    funext
    simp

variable [Group G]

end 𝔸
