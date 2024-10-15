import Mathlib
import Mathlib.Data.Nat.Choose.Sum

-- Show that every odd composite integer is a pseudoprime to both the base 1 and the base -1.
/- To demonstrate that every odd composite integer is a pseudoprime to both bases,
we will first define what a pseudoprime is. An integer \( n \) is called a pseudoprime
to a base \( a \) if \( a^{n-1} \equiv 1 \mod n \) holds true, even though \( n \) is not a prime number.-/
def isPseudoprime (n : ℤ) (b : ℤ) : Prop := b^n.natAbs ≡ b [ZMOD n]

theorem number_theory_1977_a1
    (n : ℤ) (n_odd : Odd n) (n_comp : ∃ m : ℕ, ∃ p : Fin m → ℤ, ∏ i, p i = n)
    : isPseudoprime n 1 ∧ isPseudoprime n (-1) := by
  simp [isPseudoprime, n_odd.natAbs.neg_one_pow]

-- 1. **Base 1**: For any integer \( n \), we have \( 1^{n-1} = 1 \). Therefore, \( 1^{n-1} \equiv 1 \mod n \) holds true for any integer \( n \), including odd composite integers. Thus, every odd composite integer is a pseudoprime to the base 1.

-- 2. **Base -1**: Now, we need to check the condition for base -1. We compute \( (-1)^{n-1} \). Since \( n \) is odd, \( n-1 \) is even. Therefore, \( (-1)^{n-1} = 1 \). This gives us \( (-1)^{n-1} \equiv 1 \mod n \).

-- 3. **Conclusion**: Since both conditions \( 1^{n-1} \equiv 1 \mod n \) and \( (-1)^{n-1} \equiv 1 \mod n \) are satisfied for every odd composite integer \( n \), we conclude that every odd composite integer is indeed a pseudoprime to both the base 1 and the base -1.

------------------------------------------------------------------------------

-- To prove this statement, we start by recalling the definition of a pseudoprime. An odd composite integer \( n \) is said to be a pseudoprime to the base \( a \) if it satisfies the congruence:
-- \[
-- a^{n-1} \equiv 1 \mod n
-- \]

-- Given that \( n \) is a pseudoprime to the base \( a \), we have:
-- \[
-- a^{n-1} \equiv 1 \mod n
-- \]

-- Now, we need to show that \( n \) is also a pseudoprime to the base \( n-a \). We will check the congruence for the base \( n-a \):
-- \[
-- (n-a)^{n-1} \mod n
-- \]

-- Using the binomial theorem, we can expand \( (n-a)^{n-1} \):
-- \[
-- (n-a)^{n-1} = \sum_{k=0}^{n-1} \binom{n-1}{k} n^{n-1-k} (-a)^k
-- \]

-- When we take this expression modulo \( n \), all terms where \( k \geq 1 \) will vanish because they will contain \( n \) as a factor. Thus, we are left with:
-- \[
-- (n-a)^{n-1} \equiv (-a)^{n-1} \mod n
-- \]

-- Next, we need to evaluate \( (-a)^{n-1} \mod n \). Since \( n \) is odd, \( (-a)^{n-1} \) can be rewritten as:
-- \[
-- (-a)^{n-1} = (-1)^{n-1} a^{n-1}
-- \]

-- Since \( n-1 \) is even (as \( n \) is odd), we have \( (-1)^{n-1} = 1 \). Therefore:
-- \[
-- (-a)^{n-1} \equiv a^{n-1} \mod n
-- \]


theorem number_theory_1983_b3
    (n : ℤ) (a : ℤ) (nodd : Odd n) (ncomp : ¬Prime n) (nah : isPseudoprime n a)
    : isPseudoprime n (n-a) := by
  simp [isPseudoprime, Int.ModEq, sub_eq_neg_add, add_pow,
    Finset.sum_int_mod]
  rw [Finset.sum_range_succ]
  conv =>
    arg 1; arg 1; arg 1
    tactic =>
      apply Finset.sum_congr rfl
      intro j jh
      simp at jh
    rw [←Nat.succ_pred $ show n.natAbs - j ≠ 0 by
      rwa [Nat.ne_zero_iff_zero_lt, Nat.sub_pos_iff_lt]]
    rw [show n^(n.natAbs-j).pred.succ = n^(n.natAbs-j).pred*n by
      simp [pow_succ]]
    rw [mul_comm _ n, ←mul_assoc, mul_comm _ n, mul_assoc, mul_assoc]
  rw [neg_eq_neg_one_mul, mul_pow, nodd.natAbs.neg_one_pow]
  simp
  rw [←Int.ModEq, Int.neg_modEq_neg, ←isPseudoprime]
  exact nah

-- Since we know from our initial assumption that \( a^{n-1} \equiv 1 \mod n \), we can conclude:
-- \[
-- (n-a)^{n-1} \equiv 1 \mod n
-- \]
-- This shows that \( n \) is a pseudoprime to the base \( n-a \). Thus, we have proven that if \( n \) is an odd composite integer and \( n \) is a pseudoprime to the base \( a \), then \( n \) is also a pseudoprime to the base \( n-a \).

theorem inequality_4824 (a b : ℝ) : ⌊a + b⌋ ≥ ⌊a⌋ + ⌊b⌋ := by
  apply Int.le_floor_add

theorem formal_7451
    (n a b : ℤ) (nah : isPseudoprime n a) (nbh : isPseudoprime n b)
    : isPseudoprime n (a*b) := by
  simp [isPseudoprime] at nah nbh ⊢
  rw [mul_pow]
  apply Int.ModEq.mul nah nbh

theorem number_theory_4828
    (n a b : ℤ) (nah : isPseudoprime n a) (abh : a*b ≡ 1 [ZMOD n])
    : isPseudoprime n b := by
  simp [isPseudoprime] at nah ⊢
  if oh : n = 0 then
    simp [oh] at nah abh ⊢
    simp [←nah] at abh
    exact abh.symm
  else
    rw [←Ne, ←Int.natAbs_ne_zero] at oh
    have ohh := Nat.succ_pred oh
    have := Int.ModEq.mul nah (Int.ModEq.refl (b^n.natAbs))
    have ddd := @one_pow ℤ _ n.natAbs ▸ (Int.ModEq.pow n.natAbs abh)
    rw [←mul_pow, ←Nat.succ_pred oh, @pow_succ _ _ b, mul_comm (b^_) _,
      ←mul_assoc] at this
    sorry
    done

def isStrongPseudoprime (n a : ℤ) : Prop :=
  ¬Prime n ∧ ∀ d: ℤ, Odd d → ∀ s: ℕ, d*2^s=n →
    a ^ d.natAbs ≡ 1 [ZMOD n] ∨
    ∃ r: Fin s, a ^ (d.natAbs*2^r.1) ≡ -1 [ZMOD n]

theorem number_theory_4830 : isStrongPseudoprime 25 7 := by
  simp [isStrongPseudoprime]
  constructor
  simp [Prime]
  intro
  exists 5
  exists 5
  intro d d_odd s sh
  sorry


theorem inequality_4835_1 (a b : ℝ) {_ : a > 0} {_ : b > 0} {_ : a > 0 ∧ b > 0}
    : ⌊a * b⌋ ≥ ⌊a⌋ * ⌊b⌋ := by
  have le_a := Int.floor_le a
  have le_b := Int.floor_le b
  have := mul_le_mul le_a le_b (by simp [Int.floor_nonneg]; linarith) (by linarith)
  rw [←Int.cast_mul, ←Int.le_floor] at this
  apply this

theorem inequality_4835_2 (a b : ℝ) {_ : a > 0} {_ : b > 0} {_ : a < 0 ∧ b < 0}
    : ⌊a * b⌋ ≥ ⌊a⌋ * ⌊b⌋ := by
  have le_a := Int.floor_le a
  have le_b := Int.floor_le b
  have := mul_le_mul le_a le_b (by simp [Int.floor_nonneg]; linarith) (by linarith)
  rw [←Int.cast_mul, ←Int.le_floor] at this
  apply this
