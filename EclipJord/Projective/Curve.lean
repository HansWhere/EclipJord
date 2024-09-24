import EclipJord.Projective.Variety

variable {n : ℕ} {K : Type ℓ} [Field K]

namespace ℙ

structure Curve (K : Type ℓ) [Field K] (n : ℕ) extends Variety K n : Type ℓ where
  krull_dim_1 : ∀ I J K : Ideal (toVariety.coord_ring),
    [I.IsPrime] → [J.IsPrime] → [K.IsPrime]
    → I ≠ ⊥ → J ≠ ⊥ → K ≠ ⊥ → I < J → J < K → I = J ∨ J = K

namespace Curve

instance : SetLike (Curve K n) (ℙ K n) where
  coe := λ C ↦ C.toVariety.carrier
  coe_injective' := λ p q ↦ by
    rcases p with ⟨⟨Vp, _⟩, _⟩
    rcases q with ⟨⟨Vq, _⟩, _⟩
    simp

@[simp]
lemma mem_carrier {p : Curve K n} : x ∈ p.carrier ↔ x ∈ (p : Set (ℙ K n)) := Iff.rfl

@[ext]
theorem ext {p q : Curve K n} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := SetLike.ext h

protected def copy (p : Curve K n) (s : Set (ℙ K n)) (hs : s = ↑p) : Curve K n :=
  { toVariety := ⟨s, by rw [hs]; exact p.gen_by_prime⟩
    krull_dim_1 := by
      simp only [SetLike.coe] at hs
      rw [show ∀ h, Variety.mk s h = p.toVariety by
        simp [SetLike.coe, hs]
      ]
      exact p.krull_dim_1
  }

@[simp] lemma coe_copy (p : Curve K n) (s : Set (ℙ K n)) (hs : s = ↑p) :
  (p.copy s hs : Set (ℙ K n)) = s := rfl

lemma copy_eq (p : Curve K n) (s : Set (ℙ K n)) (hs : s = ↑p) : p.copy s hs = p :=
  SetLike.coe_injective hs

-- def 𝕞 (C : Curve K n) (P : ℙ K n) (Ph : P ∈ C.1) : HomogeneousIdeal :=

def TangentSpace (C : Curve K n) (P : ℙ K n) (Ph : P ∈ C.1) : Type ℓ := C.coord_ring

end Curve

end ℙ
