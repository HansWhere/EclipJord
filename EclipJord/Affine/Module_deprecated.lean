import EclipJord.Affine.Defs
import Mathlib.Algebra.Module.Defs

namespace 𝔸.op
variable {R : Type ℓ} [Ring R]
variable {n : ℕ}

instance addCommMonoid : AddCommMonoid (𝔸 R n) where
  add := add

  add_assoc := by
    intros xs ys zs
    show add (add xs ys) zs = add xs (add ys zs)
    induction n
    case zero =>
      cases xs; cases ys; cases zs
      simp [add]
    case succ n ih =>
      cases xs; cases ys; cases zs
      simp [add, add_assoc, ih]

  zero := zero

  zero_add := by
    intro xs
    show add zero xs = xs
    induction xs
    case nil => rfl
    case cons x n xs ih => simp [add, ih]

  add_zero := by
    intro xs
    show add xs zero = xs
    induction xs
    case nil => rfl
    case cons x n xs ih => simp [add, ih]

  nsmul := nsmul

  add_comm := by
    intros xs ys
    show add xs ys = add ys xs
    induction n
    case zero =>
      cases xs; cases ys
      rfl
    case succ n ih =>
      cases xs; cases ys
      simp [add, add_comm, ih]


instance module : Module R (𝔸 R n) where
  smul := smul

  one_smul := by
    intros xs
    show smul 1 xs = xs
    induction xs
    case nil => rfl
    case cons x xs ih => simp [smul, ih]

  mul_smul := by
    intros a b xs
    show smul (a * b) xs = smul a (smul b xs)
    induction xs
    case nil => rfl
    case cons x xs ih => simp [smul, ih, mul_assoc]

  smul_zero := by
    intro a
    show smul a zero = zero
    induction n
    case zero => rfl
    case succ n ih => simp [smul, ih]; rfl

  smul_add := by
    intros a xs ys
    show smul a (add xs ys) = add (smul a xs) (smul a ys)
    induction n
    case zero =>
      cases xs; cases ys
      simp [smul, add]
    case succ n ih =>
      cases xs; cases ys
      simp [smul, add, mul_add, ih]

  add_smul := by
    intros a b xs
    show smul (a + b) xs = add (smul a xs) (smul b xs)
    induction xs
    case nil => simp [smul, add]
    case cons x xs ih => simp [smul, add, add_mul, ih]

  zero_smul := by
    intro xs
    show smul 0 xs = zero
    induction xs
    case nil => rfl
    case cons x xs ih => simp [smul, ih]; rfl

end 𝔸.op
