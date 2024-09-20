-- import Mathlib.Tactic.HelpCmd
-- import Mathlib.Tactic.Choose
-- import Mathlib.Data.NNReal.Basic
-- import Mathlib.Data.Real.Sqrt
-- import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

lemma lem1_ineq (x : Real) : 0 < x → √(4*x + 1) < 1 + 2*x := by
  intro xh
  rw [←sqrt_sq (show 0 ≤ 1 + 2*x by linarith), sqrt_lt_sqrt_iff]
  nlinarith
  linarith

theorem prob1 (a b c d : Real) : 0 < a → 0 < b → 0 < c → 0 < d
    → a + b + c + d = 1
    → √(4*a+1) + √(4*b+1) + √(4*c+1) + √(4*d+1) < 6 := by
  intro ah bh ch dh abcd_eq1
  rw [calc
    6 = 4 + 2*(a+b+c+d) := by rw [abcd_eq1]; ring
    _ = (1+2*a)+(1+2*b)+(1+2*c)+(1+2*d) := by ring
  ]
  apply add_lt_add (add_lt_add (add_lt_add _ _) _) _
  repeat (apply lem1_ineq; assumption)

lemma agm_ineq (a b : Real) : 0 ≤ a → 0 ≤ b →
    2 * √(a * b) ≤ (a + b) := by
  intros
  rw [←sqrt_sq zero_le_two, ←sqrt_mul (by linarith),
    ←sqrt_sq (show 0 ≤ a+b by linarith),
    sqrt_le_sqrt_iff, ←sub_nonneg]
  ring_nf
  rw [show -(a*b*2) + a^2 + b^2 = (a - b)^2 by ring]
  nlinarith
  nlinarith

theorem prob2 : ∀ a b c : Real, 0 < a → 0 < b → 0 <c →
  8 * a * b * c ≤ (a + b) * (b + c) * (c + a) := by
  intro a b c ah bh ch
  rw [show 8*a*b*c = (2*√(a*b))*(2*√(b*c))*(2*√(c*a)) by
    ring_nf
    have abnn : 0 ≤ a * b := by apply le_of_lt; exact mul_pos ah bh
    have bcnn : 0 ≤ b * c := by apply le_of_lt; exact mul_pos bh ch
    rw [←sqrt_mul abnn,
        ←sqrt_mul (mul_nonneg abnn bcnn),
      show (a*b*(b*c)*(a*c)) = (a*b*c)^2 by ring,
      sqrt_sq]
    apply le_of_lt
    exact mul_pos (mul_pos ah bh) ch
  ]
  apply mul_le_mul (mul_le_mul (agm_ineq a b ah.le bh.le)
    (agm_ineq b c bh.le ch.le) _ _) (agm_ineq c a ch.le ah.le)
  apply mul_nonneg zero_le_two (sqrt_nonneg _)
  apply mul_nonneg (by linarith) (by linarith)
  apply mul_nonneg zero_le_two (sqrt_nonneg _)
  linarith


theorem prop3 : ∀ k : Real, 1 < k → (.^k) '' {x : Real | 1 ≤ x} = {x : Real | 1 ≤ x} := by
  intro k k_gt1
  ext x
  simp
  constructor
  . intro ⟨y, yr, yh⟩
    rw [←yh]
    apply one_le_rpow yr
    linarith
  . intro xr
    exists x ^ k⁻¹
    constructor
    apply one_le_rpow
    linarith
    apply inv_nonneg.mpr
    linarith
    rw [rpow_inv_rpow]
    linarith
    linarith


def aa (k : Nat) : Nat → Nat
  | 0 => 0
  | 1 => k
  | n+2 => (4*k+2) * aa k (n+1) - aa k n + 2*k

-- theorem P (k : Nat) :
--   ∃ a : Nat → Nat,
--     a 0 = 0 ∧
--     ∀ n : Nat, ∃ r : Nat,
--       r * r = k * k.succ * a n * (a n).succ ∧
--       a n.succ = k.succ * a n + k * (a n).succ + 2 * r
-- := by
--   exists aa k
--   constructor
--   dsimp [aa]
--   intro n
--   induction n with
--   | zero => simp [aa]
--   | succ n ih =>
--     rcases ih with ⟨ir, ir_sq, ir_a⟩
--     induction n with
--     | zero =>
--       exists k * (k+1)
--       simp [aa]
--       ring_nf
--       trivial
--     | succ n iih =>
--       exists sorry

-- theorem vieta_formula_cubic [Field K] [IsAlgClosed K] {b c d x : K}
--     (h : x*x*x + b*x*x + c*x + d = 0) :
--     ∃ y z : K,
--       y^3 + b*y^2 + c*y + d = 0 ∧
--       z^3 + b*z^2 + c*z + d = 0 ∧
--       x + y + z = b ∧
--       x*y + y*z + z*x = c ∧
--       x*y*z = d := by sorry

-- theorem
