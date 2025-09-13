import Mathlib.Tactic
import Mathlib.Util.Delaborators

noncomputable def γ₁ (ke τ M A : ℝ) : ℝ := ke * τ * M * A
noncomputable def γ₂_θ (L v cθ : ℝ) : ℝ := L - v * cθ
noncomputable def μ (ke τ M A L v cθ : ℝ) : ℝ :=
  if γ₂_θ L v cθ ≤ 0 then 0 else min (γ₁ ke τ M A) (γ₂_θ L v cθ)

lemma μ_eq_const_0 {ke τ M A L v cθ : ℝ} (h : L - v * cθ ≤ 0) : μ ke τ M A L v cθ = 0 := by
  simp_all [μ, γ₂_θ]

lemma μ_eq_γ₁ {ke τ M A L v cθ : ℝ} (h₁ : v * cθ < L) (h₂ : v * cθ ≤ L - ke * τ * M * A) :
    μ ke τ M A L v cθ = γ₁ ke τ M A := by
  have : ke * τ * M * A ≤ L - v * cθ := by linarith
  simp_all [μ, γ₁, γ₂_θ]

lemma μ_eq_γ₂ {ke τ M A L v cθ : ℝ} (h₁ : v * cθ < L) (h₂ : L - ke * τ * M * A ≤ v * cθ) :
    μ ke τ M A L v cθ = γ₂_θ L v cθ := by
  have : L - v * cθ ≤ ke * τ * M * A := by linarith
  simp_all [μ, γ₁, γ₂_θ]

lemma μ_nonneg {ke τ M A L v cθ : ℝ} (h₁ : 0 ≤ ke * τ * M * A) : 0 ≤ μ ke τ M A L v cθ := by
  simp_all [μ, γ₁, γ₂_θ]
  by_cases h : L - v * cθ ≤ 0
  · simp_all
  · apply ite_nonneg (by linarith)
    apply le_min h₁ (by linarith [h])

noncomputable def next_speed_sq' (ke τ M A L v cθ : ℝ) : ℝ :=
  v ^ 2 + (μ ke τ M A L v cθ) ^ 2 + 2 * v * (μ ke τ M A L v cθ) * cθ
noncomputable def next_speed_sq (ke τ M A L v θ : ℝ) : ℝ := next_speed_sq' ke τ M A L v (Real.cos θ)

noncomputable def next_speed_sq_γ₁' (ke τ M A v cθ : ℝ) : ℝ :=
  v ^ 2 + ke * τ * M * A * (ke * τ * M * A + 2 * v * cθ)

noncomputable def next_speed_sq_γ₁ (ke τ M A v θ : ℝ) : ℝ :=
  next_speed_sq_γ₁' ke τ M A v (Real.cos θ)

noncomputable def next_speed_sq_γ₂' (L v cθ : ℝ) : ℝ := v ^ 2 * (1 - cθ ^ 2) + L ^ 2

lemma next_speed_sq_γ₁'_monotone_if_pos_γ₁ (ke τ M A v : ℝ) (h₁ : 0 < ke * τ * M * A) (h₂ : 0 ≤ v)
    : MonotoneOn (next_speed_sq_γ₁' ke τ M A v) (Set.Icc (-1) 1) := by
  intro cθ₁ between₁ cθ₂ between₂ cθ₁_le_cθ₂
  simp_all [next_speed_sq_γ₁']
  exact mul_le_mul_of_nonneg_left cθ₁_le_cθ₂ (by simp [h₂])

lemma next_speed_sq_γ₂'_max (L v : ℝ) : IsMaxOn (next_speed_sq_γ₂' L v) Set.univ 0 := by
  intro x
  simp_all [next_speed_sq_γ₂']
  by_cases h : v ^ 2 = 0
  · rw [h]
    norm_num
  · have : 0 ≤ v ^ 2 := pow_two_nonneg v
    rw [mul_le_iff_le_one_right (by grind)]
    apply sub_le_self
    exact pow_two_nonneg x

theorem max_at_cos_ζ_if_0_le_cos_ζ_le_cos_ζ' (ke τ M A L v : ℝ) :
    0 < v →
    0 ≤ L - ke * τ * M * A →
    0 < ke * τ * M * A →
    IsMaxOn (next_speed_sq' ke τ M A L v) unitInterval (min ((L - ke * τ * M * A) / v) 1) := by
  intro vpos h₁ h₂ cθ ⟨set₁, set₂⟩
  simp_all [next_speed_sq']
  have v_mul_cθ_le_v : v * cθ ≤ v := by exact (mul_le_iff_le_one_right vpos).mpr set₂
  have h' : L - ke * τ * M * A < L := by linarith
  obtain min_h | min_h := le_total 1 ((L - ke * τ * M * A) / v)
  · simp [min_h]
    have : v ≤ L - ke * τ * M * A := by exact (one_le_div₀ vpos).mp min_h
    rw [μ_eq_γ₁ (by linarith) (by linarith)]
    rw [μ_eq_γ₁ (by linarith) (by linarith)]
    simp_all [γ₁]
  simp [min_h]
  have v_cancel₁ : v * ((L - ke * τ * M * A) / v) = L - ke * τ * M * A := by
    rw [mul_div_cancel₀ _ (by linarith)]
  obtain h_disc | h_disc := le_total (v * cθ) (L - ke * τ * M * A)
  · rw [μ_eq_γ₁ (by linarith) (by linarith)]
    rw [μ_eq_γ₁ (by linarith) (by linarith)]
    simp_all [γ₁, le_div_iff₀]
    linarith [h_disc]
  by_cases h_zero : L - v * cθ ≤ 0
  · simp [μ_eq_const_0 h_zero]
    rw [add_assoc, le_add_iff_nonneg_right]
    apply le_add_of_nonneg_of_le (by apply pow_two_nonneg)
    field_simp
    apply mul_nonneg (by linarith)
    apply μ_nonneg (by linarith [h₂])
  simp at h_zero
  rw [μ_eq_γ₂ (by linarith [h_zero]) h_disc]
  rw [μ_eq_γ₁ (by linarith) (by linarith)]
  simp_all [γ₁, γ₂_θ]
  rw [add_assoc, add_assoc, add_le_add_iff_left, ← mul_div_assoc]
  have : 2 * v * (ke * τ * M * A) * (L - ke * τ * M * A) / v =
      2 * (ke * τ * M * A) * (L - ke * τ * M * A) := by field_simp
  rw [this]
  have : (L - v * cθ) ^ 2 + 2 * v * (L - v * cθ) * cθ ≤
      (ke * τ * M * A) ^ 2 + 2 * (ke * τ * M * A) * (L - ke * τ * M * A) ↔
      (L - ke * τ * M * A) ^ 2 ≤ (v * cθ) ^ 2 := by grind
  rw [this]
  rw [sq_le_sq₀ (by linarith) (by linarith)]
  linarith [h_disc]

lemma next_speed_sq_γ₁_cond (ke τ M A L v θ : ℝ)
    : ke * τ * M * A < L - v * Real.cos θ ∧ 0 < L - v * Real.cos θ
      → next_speed_sq ke τ M A L v θ = next_speed_sq_γ₁ ke τ M A v θ := by
  intro ⟨h₁, _⟩
  simp_all [next_speed_sq, next_speed_sq_γ₁, next_speed_sq_γ₁',
    next_speed_sq', μ, γ₁, γ₂_θ, min_eq_left_of_lt h₁]
  grind

lemma next_sq_γ₂_cond (ke τ M A L v θ : ℝ)
    : L - v * Real.cos θ ≤ ke * τ * M * A ∧ 0 < L - v * Real.cos θ
      → next_speed_sq ke τ M A L v θ
        = v ^ 2 * (Real.sin θ) ^ 2 + L ^ 2 := by
  simp_all [next_speed_sq, next_speed_sq', μ, γ₁, γ₂_θ, Real.sin_sq]
  grind
