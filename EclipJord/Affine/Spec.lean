import Mathlib.Algebra.Module.Defs
-- import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

namespace 𝔸Spec

example (x y z : Nat) (h : y = z) : x * y = x * z := by
  congr

end 𝔸Spec
