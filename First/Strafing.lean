/-
Copyright (c) 2025 Jiangwei Chong. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: Jiangwei Chong
-/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Extr

/-!
# Strafing

We present a proof of the `next_speed_max` theorem. The theorem gives a formula for the argmax as
`next_speed_cos_θ_argmax` which maximises the player speed after one frame of strafing. The
player speed is parametrised in cos θ, which is the angle between the current velocity vector and
the acceleration vector.
-/

noncomputable def γ₁ (kₑ τ M A : ℝ) : ℝ := kₑ * τ * M * A
noncomputable def γ₂ (L v cθ : ℝ) : ℝ := L - v * cθ
noncomputable def μ (kₑ τ M A L v cθ : ℝ) : ℝ :=
  if γ₂ L v cθ ≤ 0 then 0 else min (γ₁ kₑ τ M A) (γ₂ L v cθ)

lemma μ_eq_const_0 {kₑ τ M A L v cθ : ℝ} (h : L - v * cθ ≤ 0) : μ kₑ τ M A L v cθ = 0 := by
  grind [μ, γ₂]

lemma μ_eq_γ₁ {kₑ τ M A L v cθ : ℝ} (h₁ : 0 < L - v * cθ) (h₂ : v * cθ ≤ L - kₑ * τ * M * A) :
    μ kₑ τ M A L v cθ = γ₁ kₑ τ M A := by
  have : kₑ * τ * M * A ≤ L - v * cθ := by linarith
  grind [μ, γ₁, γ₂]

lemma μ_eq_γ₂ {kₑ τ M A L v cθ : ℝ} (h₁ : 0 < L - v * cθ) (h₂ : L - kₑ * τ * M * A ≤ v * cθ) :
    μ kₑ τ M A L v cθ = γ₂ L v cθ := by
  have : L - v * cθ ≤ kₑ * τ * M * A := by linarith
  grind [μ, γ₁, γ₂]

noncomputable def cos_ζ (kₑ τ M A L v : ℝ) : ℝ := (L - kₑ * τ * M * A) / v
noncomputable def cos_ζ' (L v : ℝ) : ℝ := L / v

noncomputable def next_speed_sq (kₑ τ M A L v cθ : ℝ) : ℝ :=
  v ^ 2 + (μ kₑ τ M A L v cθ) ^ 2 + 2 * v * (μ kₑ τ M A L v cθ) * cθ

/--
Formula for squared next speed in terms of cos θ computed from the length
of the next velocity vector as defined in Half-Life SDK.
-/
noncomputable def next_speed (kₑ τ M A L v cθ : ℝ) : ℝ := Real.sqrt (next_speed_sq kₑ τ M A L v cθ)

lemma next_speed_sq_μ₀ {kₑ τ M A L v cθ : ℝ} (h : L - v * cθ ≤ 0) :
    next_speed_sq kₑ τ M A L v cθ = v ^ 2 := by
  rw [next_speed_sq, μ_eq_const_0 h]
  ring_nf

lemma next_speed_sq_μ₁ {kₑ τ M A L v cθ : ℝ}
    (h₁ : 0 < L - v * cθ) (h₂ : v * cθ ≤ L - kₑ * τ * M * A) :
    next_speed_sq kₑ τ M A L v cθ = v ^ 2 + (kₑ * τ * M * A) ^ 2 + 2 * v * kₑ * τ * M * A * cθ := by
  rw [next_speed_sq, μ_eq_γ₁ (by linarith) (by linarith), γ₁]
  ring_nf

lemma next_speed_sq_μ₂ {kₑ τ M A L v cθ : ℝ}
    (h₁ : 0 < L - v * cθ) (h₂ : L - kₑ * τ * M * A ≤ v * cθ) :
    next_speed_sq kₑ τ M A L v cθ = v ^ 2 + L ^ 2 - v ^ 2 * cθ ^ 2 := by
  rw [next_speed_sq, μ_eq_γ₂ (by linarith) (by linarith), γ₂]
  ring_nf

/--
Arguments of the maximum of the squared next speed parametrised in cos θ.
-/
noncomputable def next_speed_cos_θ_argmax (kₑ τ M A L v : ℝ) : Set ℝ :=
  if 0 < kₑ * τ * M * A then
    if 0 < L then
      if 0 ≤ L - kₑ * τ * M * A then
        {min 1 cos_ζ kₑ τ M A L v}
      else
        {0}
    else
      Set.Icc (max (-1) cos_ζ' L v) 1
  else if L ≤ -v then
    Set.Icc (-1) 1
  else
    {-1}

lemma next_speed_argmax_bounds {kₑ τ M A L v : ℝ} (vpos : 0 < v) :
    ∀ a ∈ next_speed_cos_θ_argmax kₑ τ M A L v, a ∈ Set.Icc (-1) 1 := by
  intro a ha
  unfold next_speed_cos_θ_argmax cos_ζ cos_ζ' at ha
  by_cases h₁ : 0 < kₑ * τ * M * A
  · by_cases h₂ : 0 < L
    · by_cases h₃ : 0 ≤ L - kₑ * τ * M * A
      · have : a = min 1 ((L - kₑ * τ * M * A) / v) := by
          simp at ha
          grind
        by_cases h₄ : 1 < (L - kₑ * τ * M * A) / v
        · grind
        · have ha : a = (L - kₑ * τ * M * A) / v := by grind
          subst ha
          constructor
          · field_simp
            grind
          · grind
      · grind
    · simp [h₁, h₂] at ha
      grind
  · grind

/--
Proof of correctness of the argmax of next speed, parametrised in cos θ.
-/
theorem next_speed_max {kₑ τ M A L v : ℝ} (vpos : 0 < v) :
    ∀ a ∈ next_speed_cos_θ_argmax kₑ τ M A L v,
    a ∈ Set.Icc (-1) 1 ∧ IsMaxOn (next_speed kₑ τ M A L v) (Set.Icc (-1) 1) a := by
  intro a ha
  constructor
  · apply next_speed_argmax_bounds vpos
    exact ha
  apply IsMaxOn.comp_mono _ Real.sqrt_monotone
  intro cθ ⟨cθ_lb, cθ_ub⟩
  suffices next_speed_sq kₑ τ M A L v cθ ≤ next_speed_sq kₑ τ M A L v a by grind
  unfold next_speed_cos_θ_argmax cos_ζ at ha
  by_cases h₁ : 0 < kₑ * τ * M * A
  · by_cases h₂ : 0 < L
    · by_cases h₃ : 0 ≤ L - kₑ * τ * M * A
      · have : a = min 1 ((L - kₑ * τ * M * A) / v) := by
          simp at ha
          grind
        by_cases h₄ : 1 < (L - kₑ * τ * M * A) / v
        · have ha : a = 1 := by grind
          field_simp at h₄
          rw [ha, next_speed_sq_μ₁ (by nlinarith) (by nlinarith),
            next_speed_sq_μ₁ (by nlinarith) (by nlinarith)]
          gcongr
          nlinarith
        · have ha : a = (L - kₑ * τ * M * A) / v := by grind
          conv_rhs => rw [ha, next_speed_sq_μ₁ (by field_simp; linarith) (by field_simp; rfl)]
          by_cases v_cθ_le : 0 < L - v * cθ
          · rcases le_total (v * cθ) (L - kₑ * τ * M * A) with h_v_cθ_le | h_v_cθ_ge
            · rw [next_speed_sq_μ₁ v_cθ_le h_v_cθ_le]
              field_simp
              nlinarith
            · rw [next_speed_sq_μ₂ v_cθ_le h_v_cθ_ge]
              field_simp
              nlinarith
          · rw [next_speed_sq_μ₀ (by nlinarith)]
            field_simp
            nlinarith
      · have ha : a = 0 := by grind
        conv_rhs => rw [ha, next_speed_sq_μ₂ (by linarith) (by linarith)]
        by_cases v_cθ_le : 0 < L - v * cθ
        · rcases le_total (v * cθ) (L - kₑ * τ * M * A) with h_v_cθ_le | h_v_cθ_ge
          · rw [next_speed_sq_μ₁ v_cθ_le h_v_cθ_le]
            nlinarith
          · rw [next_speed_sq_μ₂ v_cθ_le h_v_cθ_ge]
            nlinarith
        · rw [next_speed_sq_μ₀ (by linarith)]
          nlinarith
    · simp [h₁, h₂, cos_ζ'] at ha
      field_simp at ha
      conv_rhs => rw [next_speed_sq_μ₀ (by linarith)]
      by_cases hLv : L < -v
      · rw [next_speed_sq_μ₀ (by nlinarith)]
      · by_cases v_cθ_le : 0 < L - v * cθ
        · rcases le_total (v * cθ) (L - kₑ * τ * M * A) with h_v_cθ_le | h_v_cθ_ge
          · rw [next_speed_sq_μ₁ v_cθ_le h_v_cθ_le]
            nlinarith
          · rw [next_speed_sq_μ₂ v_cθ_le h_v_cθ_ge]
            nlinarith
        · rw [next_speed_sq_μ₀ (by linarith)]
  · by_cases hvL : L ≤ -v
    · simp [h₁, hvL] at ha
      repeat rw [next_speed_sq_μ₀ (by nlinarith)]
    · have ha : a = -1 := by grind
      conv_rhs => rw [ha, next_speed_sq_μ₁ (by linarith) (by linarith)]
      by_cases v_cθ_le : 0 < L - v * cθ
      · rw [next_speed_sq_μ₁ v_cθ_le (by linarith)]
        suffices kₑ * τ * M * A ≤ -kₑ * τ * M * A * cθ by nlinarith
        nlinarith
      · rw [next_speed_sq_μ₀ (by linarith)]
        nlinarith
