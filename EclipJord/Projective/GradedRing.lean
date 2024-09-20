import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.GradedAlgebra.HomogeneousIdeal
import Mathlib.Algebra.Quotient

instance [CommSemiring R] [GradedRing 𝒜] : HasQuotient (DirectSum.GAlgebra R (fun i ↦ ↥(𝒜 i))) (HomogeneousIdeal 𝒜)
