import EclipJord.Projective.Defs
import Mathlib.Tactic.Linarith.Frontend


variable [Field K] {n : ℕ}

def ℙ.ne0_at (j : Fin n.succ) (P : ℙ K n)  : Prop
:= ∀ P₀ : no0 (𝔸 K n.succ), ℙ.mk P₀ = P → P₀.1 j ≠ 0

abbrev ℙ.Part (K : Type ℓ) [Field K] (n : ℕ) (j : Fin n.succ) : Type ℓ
:= {P : ℙ K n // P.ne0_at j}

abbrev 𝔸.no0.Part (K : Type ℓ) [Field K] (n : ℕ) (j : Fin n.succ) : Type ℓ
:= {P : no0 (𝔸 K n.succ) // P.1 j ≠ 0}

instance 𝔸.no0.Part.collinear.eqv {j : Fin n.succ}
    : Setoid (𝔸.no0.Part K n j)
:= Subtype.instSetoid_mathlib (λ P : no0 (𝔸 K n.succ) ↦ P.1 j ≠ 0)

def 𝔸.no0.Part.toℙPart (P : 𝔸.no0.Part K n j)
    : ℙ.Part K n ⟨j.1, by linarith [j.2]⟩ := ⟨ℙ.mk P.1, (by
  simp [𝔸.no0.Part] at P
  simp [ℙ.ne0_at]
  intro _ _ P₀h
  rw [ℙ.eq_iff] at P₀h
  rcases P₀h with ⟨k, k_no0, kh⟩
  simp [k.2, P.2]
)⟩

def 𝔸.no0.Part.EquivℙPart (j : Fin n.succ)
    : Quotient (@𝔸.no0.Part.collinear.eqv K _ n j) ≃ ℙ.Part K n j  := by
  symm
  apply Equiv.subtypeQuotientEquivQuotientSubtype
  intro ⟨P, P_ne0⟩
  simp [ℙ.ne0_at, ℙ.mk]
  constructor
  . intro Pj_ne0 Q  Q_ne0 Q_eqv_P
    rw [Quotient.eq] at Q_eqv_P
    rcases Q_eqv_P with ⟨⟨k, k_ne0⟩, Q_eq_kP⟩
    simp [.•., SMul.smul] at Q_eq_kP
    simp [Q_eq_kP]
    exact ⟨k_ne0, Pj_ne0⟩
  . intro h
    exact h P P_ne0 rfl
  simp [Setoid.r, .•., SMul.smul, .≈.]

def 𝔸.toℙ (j : Fin n.succ) (P : 𝔸 K n) : ℙ K n := ℙ.mk ⟨
  (λ i ↦
    if oh : i < j then P ⟨i, by
      have jh := j.2
      simp [LT.lt, Nat.lt] at oh jh
      exact Nat.le_trans oh jh
    ⟩
    else if ohh : i = j then 1
    else match i with
      | ⟨.zero, _⟩ => by
        simp at oh ohh
        have := ohh oh.symm
        contradiction
      | ⟨.succ i₀, i₀h⟩ => P ⟨i₀, Nat.le_of_succ_le_succ i₀h⟩
  ), by
    intro F
    have := congrFun F j
    simp at this
⟩

def 𝔸.toℙPart (j : Fin n.succ) (P : 𝔸 K n) : ℙ.Part K n j
:= ⟨P.toℙ j, by
    simp [ℙ.ne0_at, 𝔸.toℙ]
    intro P₀ P₀_ne0 P₀h
    rw [Quotient.eq] at P₀h
    simp [HasEquiv.Equiv, Setoid.r] at P₀h
    rcases P₀h with ⟨k, k_ne0, kh⟩
    simp [.•., SMul.smul, 𝔸.no0.smul'] at kh
    have := congrFun kh j
    simp at this
    rw [this]
    exact k_ne0
  ⟩

-- noncomputable def ℙ.to𝔸 (j : Fin n.succ) (P : ℙ K n) : 𝔸 K n := λ i ↦
--   let P₀ := P.out
--   if i.1 < j.1 then
--     P₀.1 ⟨i.1, by apply lt_trans i.2; simp⟩ / P₀.1 j
--   else
--     P₀.1 ⟨i.1.succ, by rw [Nat.succ_lt_succ_iff]; exact i.2⟩ / P₀.1 j

def 𝔸.no0.Part.to𝔸 (j : Fin n.succ) (P : 𝔸.no0.Part K n j) : 𝔸 K n
:= λ i ↦
  if i.1 < j.1 then
    P.1.1 ⟨i.1, by apply lt_trans i.2; simp⟩ / P.1.1 j
  else
    P.1.1 ⟨i.1.succ, by rw [Nat.succ_lt_succ_iff]; exact i.2⟩ / P.1.1 j

instance 𝔸.instSetoidEq : Setoid (𝔸 K n) := ⟨Eq, Eq.refl, Eq.symm, Eq.trans⟩

-- def collinear_relator (K : Type ℓ) [Field K] (n : ℕ) (j : Fin n.succ) :
--     ((@𝔸.no0.Part.collinear.eqv K _ _ _).r ⇒ (@Eq (𝔸 K n)))
--     (𝔸.no0.Part.to𝔸 j) (𝔸.no0.Part.to𝔸 j) := by
--   simp [Relator.LiftFun, Setoid.r]
--   intro P P_ne0 Pj_ne0 Q Q_ne0 Qj_ne0 P_eqv_Q
--   rcases P_eqv_Q with ⟨⟨k, k_ne0⟩, P_eq_kQ⟩
--   simp [.•.,SMul.smul] at P_eq_kQ
--   ext i
--   simp [𝔸.no0.Part.to𝔸]
--   simp [P_eq_kQ, mul_div_mul_left _ _ k_ne0]

def ℙ.Part.to𝔸 {j : Fin n.succ} (P : Part K n j) : 𝔸 K n
:= ((𝔸.no0.Part.EquivℙPart j).invFun P).lift (𝔸.no0.Part.to𝔸 j) $ by
  simp
  intro P P_ne0 Pj_ne0 Q Q_ne0 Qj_ne0 P_eqv_Q
  rcases P_eqv_Q with ⟨⟨k, k_ne0⟩, P_eq_kQ⟩
  simp [.•.,SMul.smul] at P_eq_kQ
  ext i
  simp [𝔸.no0.Part.to𝔸]
  simp [P_eq_kQ, mul_div_mul_left _ _ k_ne0]

-- def ℙ.to𝔸s (j : Fin n.succ) (P : ℙ K n) (_ : P.ne0_at j) : Set (𝔸 K n)
-- := {P₁ : 𝔸 K n |
--   ∃ P₀ : no0 (𝔸 K n.succ),
--     ℙ.mk P₀ = P
--     ∧ (P₁ = λ i ↦
--       if i.1 < j.1 then
--         P₀.1 ⟨i.1, by apply lt_trans i.2; simp⟩ / P₀.1 j
--       else
--         P₀.1 ⟨i.1.succ, by rw [Nat.succ_lt_succ_iff]; exact i.2⟩ / P₀.1 j
--     )
-- }

-- theorem ℙ.to𝔸s_uniq (j : Fin n.succ) (P : ℙ K n) (h : P.ne0_at j)
-- : ∀ P₁ ∈ P.to𝔸s j h, ∀ P₂ ∈ P.to𝔸s j h, P₁ = P₂ := by
--   simp [to𝔸s]
--   intro P₁ P₁' P₁'_ne0 P₁'_inP P₁h P₂ P₂' P₂'_ne0 P₂'_inP P₂h
--   rw [←P₂'_inP] at P₁'_inP
--   simp [mk, eq_iff (⟨P₁', _⟩)] at P₁'_inP
--   rcases P₁'_inP with ⟨k, kh, P₁_eq_kP₂⟩
--   simp [.•., SMul.smul] at P₁_eq_kP₂
--   simp only [P₁h, P₂h]
--   apply funext
--   intro i
--   if oh : i.1 < j.1 then
--   . simp only [oh, P₁_eq_kP₂, mul_div_mul_left _ _ kh]
--   else if ohh : i.1 = j.1 then
--   . simp only [ohh, P₁_eq_kP₂, mul_div_mul_left _ _ kh]
--   else
--   . simp only [oh, ohh, P₁_eq_kP₂, mul_div_mul_left _ _ kh]

def AffineChart (K : Type ℓ) [Field K] (n : ℕ) (j : Fin n.succ)
    : 𝔸 K n ≃ ℙ.Part K n j := {
  toFun := 𝔸.toℙPart j
  invFun := ℙ.Part.to𝔸
  left_inv := by
    simp [Function.LeftInverse, 𝔸.toℙPart,
      ℙ.Part.to𝔸, 𝔸.toℙ, ℙ.mk, 𝔸.no0.Part.EquivℙPart,
      Equiv.subtypeQuotientEquivQuotientSubtype, Quotient.hrecOn,
      Quot.hrecOn, Quot.recOn, Quot.rec]
    intro P
    -- rw [Quotient.mk_out (𝔸.no0.Part.to𝔸 _ _)]
    funext i
    simp [𝔸.no0.Part.to𝔸]
    if oh : i.1 < j.1 then
    . simp [oh]
      intro j_le_i
      have : i.1 ≥ j.1 := by apply j_le_i
      have : False := by linarith
      contradiction
    else
    . simp [oh]
      simp at oh
      if ohh : i.1.succ < j.1 then
        have : False := by linarith
        contradiction
      else
        simp at ohh
        simp [show ¬(⟨i.1 + 1, by linarith [i.2]⟩ < j) by
          simp
          rcases j with ⟨j₁, j₁h⟩
          apply Fin.mk_le_mk.mpr
          apply ohh.ge
        ]
        intro ohhh
        rw [←ohhh, Fin.val_mk] at oh
        have : False := by linarith
        contradiction

  right_inv := by
    simp [Function.RightInverse, Function.LeftInverse, 𝔸.toℙPart,
      ℙ.Part.to𝔸, 𝔸.toℙ, 𝔸.no0.Part.EquivℙPart,
      Equiv.subtypeQuotientEquivQuotientSubtype, Quotient.hrecOn,
      Quot.hrecOn, Quot.recOn, Quot.rec]
    intro P Pj_ne0
    rcases P with ⟨Pₐ⟩
    show _ = ⟦Pₐ⟧
    rw [Quotient.eq]
    simp [.≈., Setoid.r]
    exists (Pₐ.1 j)⁻¹
    have Pₐj_inv_ne0 : (Pₐ.1 j)⁻¹ ≠ 0 := by
      simp [ℙ.ne0_at, ℙ.mk] at Pj_ne0
      apply inv_ne_zero (Pj_ne0 Pₐ Pₐ.2 $ by dsimp [Quotient.mk])
    exists Pₐj_inv_ne0
    apply Subtype.eq
    simp [𝔸.no0.Part.to𝔸, .•., SMul.smul]
    ext i
    if oh : i < j then
      simp [oh, 𝔸.no0.Part.to𝔸]
      rw [Fin.lt_def] at oh
      simp [oh]
      rw [div_eq_mul_inv, mul_comm]
    else if ohh : i = j then
      simp [oh, ohh]
      rw [←GroupWithZero.mul_inv_cancel _ Pₐj_inv_ne0, inv_inv]
    else
      simp [oh, ohh]
      rcases i with ⟨i₀, i₀h⟩
      cases i₀ with
      | zero =>
        simp at oh ohh
        exact (ohh oh.symm).elim
      | succ i' =>
        rcases j with ⟨j', j'h⟩
        simp [] at oh ohh ⊢
        if ohhh : i' < j' then
          simp [ohhh]
          rw [div_eq_mul_inv, mul_comm]
          have : i' + 1 = j' := by linarith
          contradiction
        else
          simp [ohhh]
          rw [div_eq_mul_inv, mul_comm]
}
