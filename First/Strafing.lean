/-
Copyright (c) 2025 Jiangwei Chong. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: Jiangwei Chong
-/

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Util.Delaborators

/-!
# Strafing

Definitions and lemmas for analyzing the change in squared speed caused by strafing.

## Key results

We present the `next_speed_max` theorem which proves the correctness of the argmax given by
`next_speed_cos_θ_argmax` which maximises the player speed after one frame of strafing.
-/

noncomputable def γ₁ (kₑ τ M A : ℝ) : ℝ := kₑ * τ * M * A
noncomputable def γ₂_θ (L v cθ : ℝ) : ℝ := L - v * cθ
noncomputable def μ (kₑ τ M A L v cθ : ℝ) : ℝ :=
  if γ₂_θ L v cθ ≤ 0 then 0 else min (γ₁ kₑ τ M A) (γ₂_θ L v cθ)

lemma μ_eq_const_0 {kₑ τ M A L v cθ : ℝ} (h : L - v * cθ ≤ 0) : μ kₑ τ M A L v cθ = 0 := by
  grind [μ, γ₂_θ]

lemma μ_eq_γ₁ {kₑ τ M A L v cθ : ℝ} (h₁ : v * cθ < L) (h₂ : v * cθ ≤ L - kₑ * τ * M * A) :
    μ kₑ τ M A L v cθ = γ₁ kₑ τ M A := by
  have : kₑ * τ * M * A ≤ L - v * cθ := by linarith
  grind [μ, γ₁, γ₂_θ]

lemma μ_eq_γ₂ {kₑ τ M A L v cθ : ℝ} (h₁ : v * cθ < L) (h₂ : L - kₑ * τ * M * A ≤ v * cθ) :
    μ kₑ τ M A L v cθ = γ₂_θ L v cθ := by
  have : L - v * cθ ≤ kₑ * τ * M * A := by linarith
  grind [μ, γ₁, γ₂_θ]

noncomputable def cos_ζ (kₑ τ M A L v : ℝ) : ℝ := (L - kₑ * τ * M * A) / v
noncomputable def cos_ζ' (L v : ℝ) : ℝ := L / v

/--
Formula for squared next speed in terms of cos θ computed from the length
of the next velocity vector as defined in Half-Life SDK.
-/
noncomputable def next_speed_sq (kₑ τ M A L v cθ : ℝ) : ℝ :=
  v ^ 2 + (μ kₑ τ M A L v cθ) ^ 2 + 2 * v * (μ kₑ τ M A L v cθ) * cθ

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
  rw [next_speed_sq, μ_eq_γ₂ (by linarith) (by linarith), γ₂_θ]
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

/--
Proof of correctness of the argmax of squared next speed, parametrised in cos θ.
-/
theorem next_speed_max {kₑ τ M A L v : ℝ} (v_pos : 0 < v) :
    ∀ a ∈ next_speed_cos_θ_argmax kₑ τ M A L v, ∀ cθ ∈ Set.Icc (-1) 1,
    next_speed_sq kₑ τ M A L v cθ ≤ next_speed_sq kₑ τ M A L v a := by
  intro a h_a cθ hcθ@⟨cθ_lb, cθ_ub⟩
  unfold next_speed_cos_θ_argmax at h_a
  by_cases h₁ : 0 < kₑ * τ * M * A
  · by_cases h₂ : 0 < L
    · by_cases h₃ : 0 ≤ L - kₑ * τ * M * A
      · have : a = min 1 ((L - kₑ * τ * M * A) / v) := by
          simp [cos_ζ] at h_a
          grind
        by_cases h₄ : 1 < (L - kₑ * τ * M * A) / v
        · have ha : a = 1 := by grind
          field_simp at h₄
          rw [ha, next_speed_sq_μ₁ (by nlinarith) (by nlinarith),
            next_speed_sq_μ₁ (by nlinarith) (by nlinarith)]
          gcongr
          nlinarith
        · have ha : a = (L - kₑ * τ * M * A) / v := by grind
          conv_rhs => rw [ha,
            next_speed_sq_μ₁ (by field_simp; nlinarith) (by field_simp; nlinarith)]
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
    · simp [h₁, h₂, cos_ζ'] at h_a
      field_simp at h_a
      conv_rhs => rw [next_speed_sq_μ₀ (by linarith)]
      by_cases h_L_v : L < -v
      · rw [next_speed_sq_μ₀ (by nlinarith)]
      · by_cases v_cθ_le : 0 < L - v * cθ
        · rcases le_total (v * cθ) (L - kₑ * τ * M * A) with h_v_cθ_le | h_v_cθ_ge
          · rw [next_speed_sq_μ₁ v_cθ_le h_v_cθ_le]
            nlinarith
          · rw [next_speed_sq_μ₂ v_cθ_le h_v_cθ_ge]
            nlinarith
        · rw [next_speed_sq_μ₀ (by linarith)]
  · by_cases h_v_L : L ≤ -v
    · simp [h₁, h_v_L] at h_a
      repeat rw [next_speed_sq_μ₀ (by nlinarith)]
    · have ha : a = -1 := by grind
      conv_rhs => rw [ha, next_speed_sq_μ₁ (by linarith) (by linarith)]
      by_cases v_cθ_le : 0 < L - v * cθ
      · rw [next_speed_sq_μ₁ v_cθ_le (by linarith)]
        suffices kₑ * τ * M * A ≤ -kₑ * τ * M * A * cθ by nlinarith
        nlinarith
      · rw [next_speed_sq_μ₀ (by linarith)]
        nlinarith
