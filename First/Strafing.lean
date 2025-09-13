import Mathlib.Tactic
import Mathlib.Util.Delaborators

def Vec2D : Type := Fin 2 → ℝ

noncomputable def γ₁ (ke τ M A : ℝ) : ℝ := ke * τ * M * A
noncomputable def γ₂_θ' (L v cθ : ℝ) : ℝ := L - v * cθ
noncomputable def μ' (ke τ M A L v cθ : ℝ) : ℝ :=
  if γ₂_θ' L v cθ ≤ 0 then 0 else min (γ₁ ke τ M A) (γ₂_θ' L v cθ)

lemma μ'_γ₂_le_0 (ke τ M A L v cθ : ℝ) : L - v * cθ ≤ 0 → μ' ke τ M A L v cθ = 0 := by
  intro h
  simp_all [μ', γ₂_θ']

lemma μ'_eq_γ₁ (ke τ M A L v cθ : ℝ) :
    v * cθ < L ∧ v * cθ ≤ L - ke * τ * M * A → μ' ke τ M A L v cθ = γ₁ ke τ M A := by
  intro h
  have : ke * τ * M * A ≤ L - v * cθ := by linarith
  simp_all [μ', γ₁, γ₂_θ']

lemma μ'_eq_γ₂ (ke τ M A L v cθ : ℝ) :
    v * cθ < L ∧ L - ke * τ * M * A ≤ v * cθ → μ' ke τ M A L v cθ = γ₂_θ' L v cθ := by
  intro ⟨h₁, h₂⟩
  simp_all [μ', γ₁, γ₂_θ']
  have h₁' : L - v * cθ ≤ ke * τ * M * A := by linarith
  simp_all

noncomputable def next_speed_sq' (ke τ M A L v cθ : ℝ) : ℝ :=
  v ^ 2 + (μ' ke τ M A L v cθ) ^ 2 + 2 * v * (μ' ke τ M A L v cθ) * cθ
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

/-
0 ≤ cos zeta ≤ cos zeta'

0 ≤ (L - ke τ M A) / v ≤ L / v

in mu, need
v cθ < L
ke τ M A ≤ L - v cθ => 0 ≤ v cθ ≤ L - ke τ M A < L => 0 ≤ cθ < (L - ke τ M A) / v < L / v
-/

theorem max_at_cos_ζ_if_0_le_cos_ζ_le_cos_ζ' (ke τ M A L v : ℝ) :
    0 < v → /- TODO: remove this condition! -/
    0 ≤ L - ke * τ * M * A →
    0 < ke * τ * M * A →
    IsMaxOn (next_speed_sq' ke τ M A L v) unitInterval (min ((L - ke * τ * M * A) / v) 1) := by
  intro vpos h₁ h₂ cθ ⟨set₁, set₂⟩
  simp_all [next_speed_sq']
  have h': L - ke * τ * M * A < L := by linarith
  obtain min_h | min_h := le_total 1 ((L - ke * τ * M * A) / v)
  · simp_all
    have p₁ : v ≤ L - ke * τ * M * A := by exact (one_le_div vpos).mp min_h
    have p₁' : v * 1 ≤ L - ke * τ * M * A := by linarith
    have p₂ : v * cθ ≤ v := by simp_all
    have p₃ : v * cθ < L := by linarith
    have p₄ : v * cθ ≤ L - ke * τ * M * A := by linarith
    simp_all [μ'_eq_γ₁]
    have : v < L := by
      calc
        v ≤ L - ke * τ * M * A := by linarith
        _ < L := by linarith
    simp_all [μ'_eq_γ₁, γ₁]
  · simp_all
    obtain cθ_h | cθ_h := le_total cθ ((L - ke * τ * M * A) / v)
    · have p₁ : v * ((L - ke * τ * M * A) / v) < L := by sorry
      have p₂ : v * ((L - ke * τ * M * A) / v) ≤ L - ke * τ * M * A := by sorry
      have p₃ : v * cθ ≤ L - ke * τ * M * A := by sorry
      have p₄ : v * cθ < L := by linarith
      simp_all [μ'_eq_γ₁, γ₁]
    · have p₁ : v * cθ < L := by sorry
      have p₂ : L - ke * τ * M * A < v * cθ := by sorry
      have p₃ : v * ((L - ke * τ *  M *A) / v) < L := by sorry
      have p₄ : L - ke * τ * M * A < v * ((L - ke * τ * M * A) / v) := by sorry
      simp_all [μ'_eq_γ₂, γ₂_θ']
      field_simp
      simp_all
      rw [add_assoc, add_assoc]
      simp_all [add_le_add_iff_left (v ^ 2)]
      have : (L - v * cθ) ^ 2 + v * cθ * (L - v * cθ) * 2 ≤
        (ke * τ * M * A) ^ 2 + 2 * (L - ke * τ * M * A) * (ke * τ * M * A) ↔
        (L - ke * τ * M * A) ^ 2 ≤ v ^ 2 * cθ ^ 2 := by grind
      rw [this]
      have v_sq_pos : 0 < v ^ 2 := by sorry
      have : (L - ke * τ * M * A) ^ 2 ≤ v ^ 2 * cθ ^ 2 ↔
          ((L - ke * τ * M * A) ^ 2) / (v ^ 2) ≤ cθ ^ 2 := by
        exact Iff.symm (div_le_iff₀' v_sq_pos)
      rw [this]
      have : ((L - ke * τ * M * A) ^ 2) / (v ^ 2) = ((L - ke * τ * M * A) / v) ^ 2 := by ring
      rw [this]
      have : 0 ≤ (L - ke * τ * M * A) / v := by sorry
      simp_all [sq_le_sq₀ this set₁]

lemma next_speed_sq_γ₁_cond (ke τ M A L v θ : ℝ)
    : ke * τ * M * A < L - v * Real.cos θ ∧ 0 < L - v * Real.cos θ
      → next_speed_sq ke τ M A L v θ = next_speed_sq_γ₁ ke τ M A v θ := by
  intro ⟨h₁, _⟩
  simp_all [next_speed_sq, next_speed_sq_γ₁, next_speed_sq_γ₁',
    next_speed_sq', μ', γ₁, γ₂_θ', min_eq_left_of_lt h₁]
  grind

lemma next_sq_γ₂_cond (ke τ M A L v θ : ℝ)
    : L - v * Real.cos θ ≤ ke * τ * M * A ∧ 0 < L - v * Real.cos θ
      → next_speed_sq ke τ M A L v θ
        = v ^ 2 * (Real.sin θ) ^ 2 + L ^ 2 := by
  simp_all [next_speed_sq, next_speed_sq', μ', γ₁, γ₂_θ', Real.sin_sq]
  grind
