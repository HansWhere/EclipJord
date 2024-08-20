import EclipJord.Projective.Defs

variable [Field K] {n : ℕ}

def ℙ.ne0_at (j : Fin n.succ) (P : ℙ K n)  : Prop
:= ∀ P₀ : no0 (𝔸 K n.succ), ℙ.mk P₀ = P → P₀.1 j ≠ 0

def partℙ (K : Type ℓ) [Field K] (n : ℕ) (j : Fin n.succ) : Type ℓ
:= {P : ℙ K n // P.ne0_at j}

def 𝔸.toℙ (j : Fin n.succ) (P : 𝔸 K n) : ℙ K n := ℙ.mk ⟨
  (λ i ↦
    if ijh : i < j then P ⟨i, by
      have jh := j.2
      simp [LT.lt, Nat.lt] at ijh jh
      exact Nat.le_trans ijh jh
    ⟩
    else if ijh' : i = j then 1
    else match i with
      | ⟨.zero, _⟩ => by
        simp at ijh ijh'
        have := ijh' ijh.symm
        contradiction
      | ⟨.succ i₀, i₀h⟩ => P ⟨i₀, Nat.le_of_succ_le_succ i₀h⟩
  ), by
    intro F
    have := congrFun F j
    simp at this
⟩

-- noncomputable def ℙ.to𝔸 (j : Fin n.succ) (P : ℙ K n) : 𝔸 K n := λ i ↦
--   let P₀ := P.out
--   if i.1 < j.1 then
--     P₀.1 ⟨i.1, by apply lt_trans i.2; simp⟩ / P₀.1 j
--   else
--     P₀.1 ⟨i.1.succ, by rw [Nat.succ_lt_succ_iff]; exact i.2⟩ / P₀.1 j

def ℙ.to𝔸 (j : Fin n.succ) (P : ℙ K n) (_ : P.ne0_at j) : Set (𝔸 K n) := {P₁ : 𝔸 K n |
  ∃ P₀ : no0 (𝔸 K n.succ),
    ℙ.mk P₀ = P
    ∧ (P₁ = λ i ↦
      if i.1 < j.1 then
        P₀.1 ⟨i.1, by apply lt_trans i.2; simp⟩ / P₀.1 j
      else
        P₀.1 ⟨i.1.succ, by rw [Nat.succ_lt_succ_iff]; exact i.2⟩ / P₀.1 j
    )
}

theorem ℙ.to𝔸_uniq (j : Fin n.succ) (P : ℙ K n) (h : P.ne0_at j)
: ∀ P₁ ∈ P.to𝔸 j h, ∀ P₂ ∈ P.to𝔸 j h, P₁ = P₂ := by
  simp [to𝔸]
  intro P₁ P₁' P₁'_ne0 P₁'_inP P₁h P₂ P₂' P₂'_ne0 P₂'_inP P₂h
  rw [←P₂'_inP] at P₁'_inP
  simp [eq, 𝔸.no0.collinear] at P₁'_inP
  rcases P₁'_inP with ⟨k, kh, P₁_eq_kP₂⟩
  simp [HSMul.hSMul, SMul.smul, 𝔸.no0.smul'] at P₁_eq_kP₂
  simp only [P₁h, P₂h]
  apply funext
  intro i
  if ijh : i.1 < j.1 then
  . simp only [ijh, P₁_eq_kP₂, mul_div_mul_left _ _ kh]
  else if ijh' : i.1 = j.1 then
  . simp only [ijh', P₁_eq_kP₂, mul_div_mul_left _ _ kh]
  else
  . simp only [ijh, ijh', P₁_eq_kP₂, mul_div_mul_left _ _ kh]

-- def ℙ.to𝔸 {n : ℕ} (j : Fin n.succ) (P : ℙ K n) (h : P.ne0_at j) (P₀ : no0 (𝔸 K n.succ)) (Ph : ℙ.mk P₀ = P) : Set (𝔸 K n)

  -- intro Ph i
  -- simp only [mk, ne0_at] at Ph h
  -- have := h P₀ Ph
  -- have := Nat.lt_trichotomy i.1 j.1
  -- if ijh : i.1 < j.1 then
  --   exact P₀.1 ⟨i.1, by apply lt_trans i.2; simp⟩
  -- else if ijh' : i.1 = j.1 then
  --   sorry
  -- else
  --   have := Nat.lt_trichotomy i.1 j.1
  --   sorry


def AffineChart (K : Type ℓ) [Field K] (n : ℕ) (j : Fin n.succ)
: 𝔸 K n ≃ partℙ K n j := {
  toFun := λ P ↦ ⟨P.toℙ j, by
    simp [ℙ.ne0_at, 𝔸.toℙ, ℙ.mk]
    intro P Ph PPh
    rw [Quotient.eq,] at PPh
    simp [HasEquiv.Equiv, Setoid.r, 𝔸.no0.collinear] at PPh
    rcases PPh with ⟨k, k_ne0, kh⟩
    simp [.•., SMul.smul, 𝔸.no0.smul'] at kh
    have := congrFun kh j
    simp at this
    rw [this]
    exact k_ne0
  ⟩


  invFun := sorry -- λ ⟨P, Ph⟩ ↦ P.to𝔸 j
  left_inv := sorry
    --by
    -- simp [Function.LeftInverse, 𝔸.toℙ]

  right_inv := sorry
}
