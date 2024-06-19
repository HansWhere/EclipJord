import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Rat
import Lean

variable {n : ℕ}
variable {R : Type ℓ} [Ring R]

inductive 𝔸 (R : Type ℓ) [Ring R] : ℕ → Type ℓ
| nil : 𝔸 R 0
| cons : R → {n : ℕ} → 𝔸 R n → 𝔸 R (n + 1)

infixr: 67 ":::" => 𝔸.cons

syntax (priority := high) "⟪" term,+ "⟫" : term
macro_rules
| `(⟪$x⟫) => `(𝔸.cons $x 𝔸.nil)
| `(⟪$x, $xs:term,*⟫) => `(𝔸.cons $x ⟪$xs,*⟫)

example : 𝔸 ℚ 3 := ⟪1.5,2,3⟫

namespace 𝔸.op

def add : {n : ℕ} → 𝔸 R n → 𝔸 R n → 𝔸 R n
| 0, 𝔸.nil, 𝔸.nil => 𝔸.nil
| _+1, x ::: xs, y ::: ys => (x + y) ::: (add xs ys)

def smul : {n : ℕ} → R → 𝔸 R n → 𝔸 R n
| 0, _, 𝔸.nil => 𝔸.nil
| _+1, c, x ::: xs => (c * x) ::: (smul c xs)

def zero : {n : ℕ} → 𝔸 R n
| 0 => 𝔸.nil
| _+1 => 0 ::: zero

def nsmul {n : ℕ} : ℕ → 𝔸 R n → 𝔸 R n
| 0, _ => zero
| m+1, xs => add (nsmul m xs) xs

end 𝔸.op
open 𝔸.op

def nonzero (M : Type ℓ) [AddCommMonoid M] : Type ℓ := {x : M // x ≠ 0}

instance [DecidableEq R] : DecidableEq (𝔸 R n) := by
  intros xs ys
  induction n
  case zero => cases xs; cases ys; right; rfl
  case succ n ih =>
    cases xs with | cons x xs =>
    cases ys with | cons y ys =>
    if h : x = y then
      if hs : xs = ys then
        right; simp [h, hs]
      else
        left; simp; intro; exact hs
    else
      left; simp; intro; contradiction

example : [1, 2, 3] ≠ [3, 2, 1] :=
by decide

example : (⟪3, 2, 1⟫ : 𝔸 ℚ 3) ≠ 𝔸.op.zero :=
by decide

-- abbrev 𝔸f (R : Type ℓ) [Ring R] (n : ℕ) : Type ℓ := Fin n → R

def 𝔸toF : {n : ℕ} → 𝔸 R n → Fin n → R
| 0, 𝔸.nil, _ => 0
| _+1, 𝔸.cons x _, ⟨0, _⟩ => x
| _+1, 𝔸.cons _ xs, ⟨m+1, h⟩ => 𝔸toF xs ⟨m, by omega⟩

def Fto𝔸 {n : ℕ} (P : Fin n → R) : 𝔸 R n := match n with
| 0 => 𝔸.nil
| n+1 => P (⟨0, by omega⟩) ::: Fto𝔸 (λ j ↦ P ⟨j+1, by omega⟩)


instance (R : Type ℓ) [Ring R] (n : ℕ) : Equiv (𝔸 R n) (Fin n → R) where
  toFun := 𝔸toF
  invFun := Fto𝔸
  left_inv := by
    intro xs
    induction n with
    | zero => cases xs; simp [𝔸toF, Fto𝔸]
    | succ n ih =>
      cases xs with | cons x xs =>
        simp [𝔸toF, Fto𝔸]
        rw [ih]
  right_inv := by
    intro P
    funext j
    induction n with
    | zero => cases j; contradiction
    | succ n ih =>
      rcases j with ⟨m,h⟩
      cases m with
      | zero => simp [Fto𝔸, 𝔸toF]
      | succ m => simp [Fto𝔸, 𝔸toF, ih]
