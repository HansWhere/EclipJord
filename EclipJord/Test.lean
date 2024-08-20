def mp : (A ∨ B) → (A → B) → B
  | .inl a => λ f ↦ f a
  | .inr b => λ _ ↦ b

def mpr [Decidable A] [Decidable B] : ((A → B) → B) → (A ∨ B) := by
  intro f
  rw [
    Decidable.imp_iff_not_or,
    Decidable.imp_iff_not_or,
    not_or,
    and_or_right,
    Decidable.not_not
  ] at f
  exact f.1

def f
