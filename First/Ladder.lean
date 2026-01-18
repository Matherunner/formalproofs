/-
Copyright (c) 2025 Jiangwei Chong. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: Jiangwei Chong
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.CrossProduct

/-!
# Optimal ladder climbing angles

This file formalises the *vertical velocity* of a player on a Half-Life ladder and
proves the optimal direction for u (input yaw γ and pitch ω).

See https://jwchong.com/hl/ladder.html for background and context.

## Main results

We parametrise the ladder input velocity u in terms of two angles: γ and ω. This
is defined by `ladder_u_by_γ_ω`. Then we parametrise the vertical climbing velocity
by the γ and ω in `ladder_vert_v_scaled_angles`.

If the ladder norma tilt is φ = ±π/2, then the vertical velocity is always zero, as shown
by the theorem `vert_v_zero`.

`vert_v_max` is the main theorem proving the maximum points for any ladder normal tilt
φ ∈ (-π/2, π/2). You will note that this theorem requires no additional
assumptions besides the bounds for φ. This theorem is unconstrained in the sense that
it gives the maximum for ω ∈ [-π/2, π/2].

When both forward/back and moveright/moveleft keys are pressed, we can't realise angles
ω < -π/4 or π/4 < ω. So `vert_v_max_constrained` is similar to `vert_v_max`, except it
is subject to the additional constraint ω ∈ [-π/4, π/4].

`vert_v_max_value_constrained_eq` proves that holding both forward/back and moveright/moveleft
is always better than holding just one key when climbing, despite the constraint on the direction
of input velocity u when holding two keys and the unconstrained viewing direction when holding
just one key.
-/

open Matrix

abbrev Vec3 := Fin 3 → ℝ

noncomputable def IsUnitVec (x : Vec3) := x ⬝ᵥ x = 1

noncomputable def norm3 (x : Vec3) : ℝ := √(x ⬝ᵥ x)

noncomputable def normalise (x : Vec3) : Vec3 := (1 / norm3 x) • x

def uvec_k : Vec3 := ![0, 0, 1]

lemma norm3_nonneg {x : Vec3} : 0 ≤ norm3 x := by
  simp [norm3]

lemma unit_dot_self {x : Vec3} : norm3 x = 1 ↔ IsUnitVec x := by
  simp [norm3, IsUnitVec]

lemma dot_self_nonneg {x : Vec3} : 0 ≤ x ⬝ᵥ x := by
  apply Finset.sum_nonneg'
  intro i
  nlinarith

lemma uvec_k_dot_self : uvec_k ⬝ᵥ uvec_k = 1 := by
  simp [uvec_k]

lemma vec_horizontal_pos {n : Vec3} (h : uvec_k ⨯₃ n ≠ 0) : 0 < n 0 ^ 2 + n 1 ^ 2 := by
  simp [crossProduct, uvec_k] at h
  by_cases h₁ : n 1 = 0
  · simp [h₁]
    simp [h₁] at h
    exact sq_pos_of_ne_zero h
  have h₂ : 0 < n 1 ^ 2 := sq_pos_iff.mpr h₁
  nlinarith

lemma cos_add_sin {x : ℝ} : Real.cos x + Real.sin x = √2 * Real.cos (x - Real.pi / 4) := by
  simp [Real.cos_sub]
  ring_nf
  simp [Real.sq_sqrt]

lemma cos_three_pi_div_four : Real.cos (3 * Real.pi / 4) = -√2 / 2 := by
  rw [neg_div, neg_eq_iff_eq_neg.mpr]
  simp [← Real.cos_sub_pi, show 3 * Real.pi / 4 - Real.pi = -(Real.pi / 4) by linarith]

lemma sin_three_pi_div_four : Real.sin (3 * Real.pi / 4) = √2 / 2 := by
  simp [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by linarith]

/--
The **fundamental ladder equation**, returns the player velocity in 3D.
-/
noncomputable def ladder (u n : Vec3) : Vec3 :=
  if uvec_k ⨯₃ n = 0 then
    u - (u ⬝ᵥ n) • n
  else
    u - (u ⬝ᵥ n) • (n + n ⨯₃ normalise (uvec_k ⨯₃ n))

noncomputable def ladder_n_by_φ (φ : ℝ) : Vec3 := ![Real.cos φ, 0, -Real.sin φ]

noncomputable def ladder_u_by_γ_ω (γ ω : ℝ) : Vec3 :=
  ![Real.cos γ * Real.cos ω, Real.sin γ * Real.cos ω, -Real.sin ω]

-- TODO: prove bijection between parametrisation and n
-- TODO: prove symmetry of rotation around z axis

/--
The vertical component of velocity divided by the M and parametrised by angles.
-/
noncomputable def ladder_vert_v_scaled_angles (φ γ ω : ℝ) : ℝ :=
  (ladder (ladder_u_by_γ_ω γ ω) (ladder_n_by_φ φ)) 2

/--
The player velocity is always perpendicular to the ladder normal.
-/
theorem dot_ladder_n_eq_zero {u n : Vec3} (nunit : IsUnitVec n) : n ⬝ᵥ ladder u n = 0 := by
  unfold ladder
  unfold IsUnitVec at nunit
  by_cases is_vertical : uvec_k ⨯₃ n = 0
  repeat simp [is_vertical, nunit, dotProduct_comm]

def u_n_angle (u n : Vec3) (α : ℝ) := u ⬝ᵥ n = (norm3 u) * (norm3 n) * Real.cos α

/--
The vertical climbing velocity is always 0 if the normal vector is vertical.
-/
theorem vert_v_zero {u n : Vec3} (h : n = uvec_k ∨ n = -uvec_k) :
    uvec_k ⬝ᵥ ladder u n = 0 := by
  simp [ladder]
  rcases h with h₁ | h₂
  · simp [h₁, dotProduct_comm, uvec_k_dot_self]
  · simp [h₂, dotProduct_comm, uvec_k_dot_self]

/--
Parametrising vertical ladder vertical climbing speed in terms of α.
-/
lemma norm_ladder_uvec_k_eq {u : Vec3} {α : ℝ} (α_def : u_n_angle u uvec_k α) :
    norm3 (ladder u uvec_k) = (norm3 u) * |Real.sin α| := by
  dsimp [ladder, norm3]
  rw [← sq_eq_sq₀ (by simp) (by simp [mul_nonneg]), mul_pow, sq_abs, Real.sin_sq,
    Real.sq_sqrt dot_self_nonneg]
  simp
  grind [dotProduct_comm, u_n_angle, norm3, Real.sq_sqrt, dot_self_nonneg, uvec_k_dot_self]

/--
Vertical ladder vertical climbing speed maximisation in terms of the angle
between u and n.
-/
theorem vert_n_vert_v_max_at_π_over_2 {u : Vec3} :
    IsMaxOn (fun α ↦ (norm3 u) * |Real.sin α|)
      (Set.Icc 0 Real.pi) (Real.pi / 2) := by
  intro α ⟨lb, ub⟩
  simp [mul_le_of_le_one_right, norm3_nonneg, Real.abs_sin_le_one]

lemma n_not_vert {x : ℝ} (h : Real.cos x ≠ 0) : uvec_k ⨯₃ ladder_n_by_φ x ≠ 0 := by
  simp [uvec_k, ladder_n_by_φ, crossProduct, h]

/--
Parametrisation of vertical climbing velocity in terms of three angles.
-/
lemma vert_v_simp {φ γ ω : ℝ} (φ_bounds : -Real.pi / 2 < φ ∧ φ < Real.pi / 2) :
    ladder_vert_v_scaled_angles φ γ ω =
      -Real.sin ω - √2 * (Real.cos γ * Real.cos ω * Real.cos φ + Real.sin ω * Real.sin φ)
      * Real.cos (φ + Real.pi / 4) := by
  have zero_lt_cos_φ : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo (by constructor <;> linarith)
  simp only [ladder_vert_v_scaled_angles, ladder, n_not_vert (by linarith), ladder_u_by_γ_ω]
  simp [ladder_n_by_φ, crossProduct, normalise, norm3, uvec_k, Real.cos_add]
  field_simp
  simp [Real.sqrt_sq (by linarith)]
  linarith

/--
An expression for the postulated maximum.
-/
lemma vert_v_star_γ_eq_π {φ : ℝ} (φ_bounds : -Real.pi / 2 < φ ∧ φ < Real.pi / 2) :
    ladder_vert_v_scaled_angles φ Real.pi (-(φ + Real.pi / 4)) = √2 * Real.cos φ := by
  simp [vert_v_simp φ_bounds, Real.sin_neg, Real.cos_neg, Real.sin_add, Real.cos_add,
    Real.sin_pi_div_four, Real.cos_pi_div_four, Real.cos_pi]
  field_simp
  rw [Real.sq_sqrt (by linarith)]
  field_simp
  calc
    _ = Real.sin φ + Real.cos φ +
        (Real.sin φ ^ 2 + Real.cos φ ^ 2) * (Real.cos φ - Real.sin φ) := by
      ring_nf
    _ = 2 * Real.cos φ := by
      rw [Real.sin_sq_add_cos_sq]
      group

/--
An expression for the postulated maximum at γ = 0 and ω = φ - 3π/4.
-/
lemma vert_v_star_γ_eq_zero {φ : ℝ} (φ_bounds : -Real.pi / 2 < φ ∧ φ < Real.pi / 2) :
    ladder_vert_v_scaled_angles φ 0 (φ - 3 * Real.pi / 4) = √2 * Real.cos φ := by
  simp [vert_v_simp φ_bounds, ← Real.cos_sub, cos_three_pi_div_four, mul_div, ← Real.sin_add_pi]
  calc
    _ = Real.cos (φ + Real.pi / 4) + Real.sin (φ + Real.pi / 4) := by
      group
    _ = √2 * Real.cos φ := by
      simp [cos_add_sin]

/--
An expression for the postulated maximum at γ = π and ω = -π/4.
-/
lemma vert_v_star_γ_eq_π_constrained {φ : ℝ}
    (φ_bounds : -Real.pi / 2 < φ ∧ φ < Real.pi / 2) :
    ladder_vert_v_scaled_angles φ Real.pi (-(Real.pi / 4)) = √2 * Real.cos φ ^ 2 := by
  simp [vert_v_simp φ_bounds]
  calc
    _ = √2 / 2 + (Real.cos φ + Real.sin φ) * Real.cos (φ + Real.pi / 4) := by
      ring_nf
      simp [Real.sq_sqrt]
      group
    _ = √2 * Real.cos φ ^ 2 := by
      simp [Real.cos_add, Real.cos_pi_div_four, Real.sin_pi_div_four]
      ring_nf
      simp only [Real.sin_sq]
      group

/--
An expression for the postulated maximum at γ = 0 and ω = -π/4.
-/
lemma vert_v_star_γ_eq_zero_constrained {φ : ℝ}
    (φ_bounds : -Real.pi / 2 < φ ∧ φ < Real.pi / 2) :
    ladder_vert_v_scaled_angles φ 0 (-(Real.pi / 4)) = √2 / 2 * Real.sin (2 * φ) := by
  simp [vert_v_simp φ_bounds]
  calc
    _ = √2 / 2 - (Real.cos φ - Real.sin φ) * Real.cos (φ + Real.pi / 4) := by
      ring_nf
      simp [Real.sq_sqrt]
      group
    _ = √2 / 2 * Real.sin (2 * φ) := by
      simp [Real.cos_add, Real.cos_pi_div_four, Real.sin_pi_div_four, Real.sin_two_mul]
      ring_nf
      simp only [Real.sin_sq]
      group

/--
V parametrisation is monotonically increasing for γ ∈ [0, π] and φ ∈ (-π/2, π/4].
-/
lemma vert_v_simp_γ_monotone {φ ω : ℝ}
    (φ_bounds : -Real.pi / 2 < φ ∧ φ ≤ Real.pi / 4)
    (ω_bounds : -Real.pi / 2 ≤ ω ∧ ω ≤ Real.pi / 2) :
    MonotoneOn (fun γ ↦ ladder_vert_v_scaled_angles φ γ ω) (Set.Icc 0 Real.pi) := by
  intro a arange b brange a_le_b
  have h_φ : -Real.pi / 2 < φ ∧ φ < Real.pi / 2 := by constructor <;> linarith
  simp only [vert_v_simp h_φ]
  gcongr
  · exact Real.cos_nonneg_of_mem_Icc (by constructor <;> linarith)
  · exact Real.cos_nonneg_of_mem_Icc (by constructor <;> linarith)
  · exact Real.cos_nonneg_of_mem_Icc (by constructor <;> linarith)
  · exact Real.cos_le_cos_of_nonneg_of_le_pi arange.1 brange.2 a_le_b

/--
V parametrisation is antitone for γ ∈ [0, π] and φ ∈ (π/4, π/2).
-/
lemma vert_v_simp_γ_antitone {φ ω : ℝ}
    (φ_bounds : Real.pi / 4 < φ ∧ φ < Real.pi / 2)
    (ω_bounds : -Real.pi / 2 ≤ ω ∧ ω ≤ Real.pi / 2) :
    AntitoneOn (fun γ ↦ ladder_vert_v_scaled_angles φ γ ω) (Set.Icc 0 Real.pi) := by
  intro a arange b brange a_le_b
  have h_φ : -Real.pi / 2 < φ ∧ φ < Real.pi / 2 := by constructor <;> linarith
  simp only [vert_v_simp h_φ, sub_le_sub_iff_left]
  have h_cos_neg : Real.cos (φ + Real.pi / 4) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
  -- Need this to make gcongr work
  simp [mul_le_mul_right_of_neg h_cos_neg]
  gcongr
  · exact Real.cos_nonneg_of_mem_Icc (by constructor <;> linarith)
  · exact Real.cos_nonneg_of_mem_Icc (by constructor <;> linarith)
  · exact Real.antitoneOn_cos arange brange a_le_b

/--
V is maximised at γ = π for all φ and ω in their respective bounds.
-/
lemma vert_v_max_γ_eq_π {φ ω : ℝ}
    (φ_bounds : -Real.pi / 2 < φ ∧ φ ≤ Real.pi / 4)
    (ω_bounds : -Real.pi / 2 ≤ ω ∧ ω ≤ Real.pi / 2) :
    IsMaxOn (fun γ ↦ ladder_vert_v_scaled_angles φ γ ω) (Set.Icc 0 Real.pi) Real.pi := by
  intro γ γrange
  apply vert_v_simp_γ_monotone φ_bounds ω_bounds γrange
  · simp [Real.pi_nonneg]
  · exact γrange.2

/--
V is maximised at γ = 0 for all φ and ω in their respective bounds.
-/
lemma vert_v_max_γ_eq_zero {φ ω : ℝ}
    (φ_bounds : Real.pi / 4 < φ ∧ φ < Real.pi / 2)
    (ω_bounds : -Real.pi / 2 ≤ ω ∧ ω ≤ Real.pi / 2) :
    IsMaxOn (fun γ ↦ ladder_vert_v_scaled_angles φ γ ω) (Set.Icc 0 Real.pi) 0 := by
  intro γ γrange
  apply vert_v_simp_γ_antitone φ_bounds ω_bounds
  · simp [Set.mem_Icc]
    positivity
  · exact γrange
  · exact γrange.1

lemma vert_v_max_ω_when_γ_eq_zero {φ : ℝ} (φ_bounds : Real.pi / 4 < φ ∧ φ < Real.pi / 2) :
    IsMaxOn (ladder_vert_v_scaled_angles φ 0)
      (Set.Icc (-Real.pi / 2) (Real.pi / 2))
      (φ - 3 * Real.pi / 4) := by
  intro ω ωset
  have h_φ : -Real.pi / 2 < φ ∧ φ < Real.pi / 2 := by constructor <;> linarith
  set p := ω - φ + 3 * Real.pi / 4 with hp
  simp only [show ω = p + φ - 3 * Real.pi / 4 by linarith, vert_v_star_γ_eq_zero h_φ,
    vert_v_simp h_φ, Real.cos_zero, one_mul]
  calc
    _ = Real.sin (p + (φ + Real.pi / 4)) - √2 * Real.cos (p + φ - 3 * Real.pi / 4 - φ) *
        Real.cos (φ + Real.pi / 4) := by
      simp only [Real.cos_sub, ← Real.sin_add_pi]
      group
    _ = Real.sin (p + (φ + Real.pi / 4)) - √2 * Real.cos (p - 3 * Real.pi / 4) *
        Real.cos (φ + Real.pi / 4) := by
      group
    _ = Real.sin (p + (φ + Real.pi / 4)) - √2 ^ 2 / 2 * (-Real.cos p + Real.sin p) *
        Real.cos (φ + Real.pi / 4) := by
      simp only [Real.cos_sub, cos_three_pi_div_four, sin_three_pi_div_four]
      group
    _ = Real.cos p * (Real.cos (φ + Real.pi / 4) + Real.sin (φ + Real.pi / 4)) := by
      simp [Real.sq_sqrt, Real.sin_add]
      group
    _ ≤ √2 * Real.cos φ := by
      simp [cos_add_sin]
      group
      gcongr
      · exact Real.cos_nonneg_of_mem_Icc (by constructor <;> linarith)
      · rw [mul_le_iff_le_one_left (by positivity)]
        exact Real.cos_le_one p

/--
Fix γ = π, then V is maximised when ω = -(φ + Real.pi / 4).
-/
lemma vert_v_max_ω_when_γ_eq_π {φ : ℝ} (φ_bounds : -Real.pi / 2 < φ ∧ φ ≤ Real.pi / 4) :
    IsMaxOn (ladder_vert_v_scaled_angles φ Real.pi)
      (Set.Icc (-Real.pi / 2) (Real.pi / 2))
      (-(φ + Real.pi / 4)) := by
  intro ω ωset
  have h_φ : -Real.pi / 2 < φ ∧ φ < Real.pi / 2 := by constructor <;> linarith
  set p := ω + φ + Real.pi / 4 with hp
  simp only [show ω = p - φ - Real.pi / 4 by linarith, vert_v_star_γ_eq_π h_φ, vert_v_simp h_φ]
  calc
    _ = -Real.sin (p - φ - Real.pi / 4) +
        √2 * Real.cos (p - φ - Real.pi / 4 + φ) * Real.cos (φ + Real.pi / 4) := by
      simp only [Real.cos_pi, Real.cos_add]
      group
    _ = -Real.sin (p - (φ + Real.pi / 4)) +
        √2 * Real.cos (p - Real.pi / 4) * Real.cos (φ + Real.pi / 4)  := by
      group
    _ = -Real.sin (p - (φ + Real.pi / 4)) +
        (Real.cos p + Real.sin p) * Real.cos (φ + Real.pi / 4) := by
      simp [Real.cos_sub, Real.cos_pi_div_four, Real.sin_pi_div_four]
      field_simp
      simp [Real.sq_sqrt]
    _ = Real.cos p * (Real.sin (φ + Real.pi / 4) + Real.cos (φ + Real.pi / 4)) := by
      simp [Real.sin_sub]
      group
    _ = √2 * Real.cos p * Real.cos φ := by
      simp only [Real.sin_add, Real.cos_add, Real.cos_pi_div_four, Real.sin_pi_div_four]
      group
    √2 * Real.cos p * Real.cos φ ≤ √2 * Real.cos φ := by
      gcongr
      · grind [Real.cos_nonneg_of_mem_Icc]
      · have hsqrt : 0 ≤ √2 := by positivity
        have hcos : Real.cos p ≤ 1 := Real.cos_le_one p
        nlinarith

/--
Fix γ = 0, then V for φ ∈ (π/4, π/2) is maximised at ω = -π/4
subject to the constraint ω ∈ [-π/4, π/4].
-/
lemma vert_v_max_ω_γ_eq_zero_constrained {φ : ℝ} (φ_bounds : Real.pi / 4 < φ ∧ φ < Real.pi / 2) :
    IsMaxOn (ladder_vert_v_scaled_angles φ 0)
      (Set.Icc (-Real.pi / 4) (Real.pi / 4))
      (-(Real.pi / 4)) := by
  intro ω ωset
  have h_φ : -Real.pi / 2 < φ ∧ φ < Real.pi / 2 := by constructor <;> linarith
  simp only [vert_v_star_γ_eq_zero_constrained h_φ, vert_v_simp h_φ, Real.cos_add,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  calc
    _ = -Real.cos φ * (Real.sin ω * Real.cos φ + Real.cos ω * Real.cos φ +
        Real.sin ω * Real.sin φ - Real.cos ω * Real.sin φ) := by
      ring_nf
      simp [Real.sq_sqrt, Real.sin_sq]
      group
    _ = -Real.cos φ * (Real.sin (ω - φ) + Real.cos (ω - φ)) := by
      simp only [Real.cos_sub, Real.sin_sub]
      group
    _ = √2 * -Real.sin (ω - φ + Real.pi / 4) * Real.cos φ := by
      simp [Real.sin_add]
      ring_nf
      simp [Real.sq_sqrt]
      group
    _ ≤ √2 / 2 * Real.sin (2 * φ) := by
      simp only [Real.sin_two_mul]
      conv_rhs => ring_nf
      gcongr
      · exact Real.cos_nonneg_of_mem_Icc (by constructor <;> linarith)
      rw [← Real.sin_neg]
      apply Real.sin_le_sin_of_le_of_le_pi_div_two <;> grind

/--
Fix γ = π, then V for φ ∈ (0, π/4] is maximised at ω = -π/4
subject to the constraint ω ∈ [-π/4, π/4].
-/
lemma vert_v_max_ω_γ_eq_π_constrained {φ : ℝ} (φ_bounds : 0 < φ ∧ φ ≤ Real.pi / 4) :
    IsMaxOn (ladder_vert_v_scaled_angles φ Real.pi)
      (Set.Icc (-Real.pi / 4) (Real.pi / 4))
      (-(Real.pi / 4)) := by
  intro ω ωset
  have h_φ : -Real.pi / 2 < φ ∧ φ < Real.pi / 2 := by
    constructor <;> linarith [φ_bounds.1, Real.pi_pos]
  have h_cos : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo (by constructor <;> linarith)
  simp only [vert_v_star_γ_eq_π_constrained h_φ, vert_v_simp h_φ]
  simp only [Real.cos_add, Real.cos_pi_div_four, Real.sin_pi_div_four]
  calc
    _ = -(Real.sin ω + Real.cos ω) * Real.cos φ * Real.sin φ -
        (Real.sin ω - Real.cos ω) * Real.cos φ ^ 2 := by
      ring_nf
      simp [Real.sin_sq]
      group
    _ = Real.cos φ * (Real.cos (ω + φ) - Real.sin (ω + φ)) := by
      simp [Real.cos_add, Real.sin_add]
      group
    _ = √2 * Real.cos φ * Real.cos (ω + φ + Real.pi / 4) := by
      simp [Real.cos_add]
      ring_nf
      simp [Real.sq_sqrt]
      group
    _ ≤ √2 * Real.cos φ ^ 2 := by
      rw [mul_assoc, mul_le_mul_iff_right₀ (show 0 < √2 by positivity)]
      rw [pow_two, mul_le_mul_iff_right₀ h_cos]
      apply Real.cos_le_cos_of_nonneg_of_le_pi
      · linarith [φ_bounds.1]
      · conv_rhs => rw [show Real.pi = Real.pi / 4 + Real.pi / 4 + Real.pi / 2 by linarith]
        exact add_le_add_three ωset.2 φ_bounds.2 (by linarith)
      · grind

/--
Postulated argmax for vertical climbing velocity.
-/
noncomputable def vert_v_argmax (φ : ℝ) : ℝ × ℝ :=
  if φ ≤ Real.pi / 4 then
    (Real.pi, -(φ + Real.pi / 4))
  else
    (0, φ - 3 * Real.pi / 4)

/--
Maximisation of the vertical player velocity for φ ∈ (-π/2, π/2).
-/
theorem vert_v_max {φ : ℝ} (φ_bounds : -Real.pi / 2 < φ ∧ φ < Real.pi / 2) :
    IsMaxOn (fun ⟨γ, ω⟩ ↦ ladder_vert_v_scaled_angles φ γ ω)
      (Set.Icc (0, -Real.pi / 2) (Real.pi, Real.pi / 2))
      (vert_v_argmax φ) := by
  intro ⟨γ, ω⟩ ⟨⟨γ_lb, ω_lb⟩, ⟨γ_ub, ω_ub⟩⟩
  unfold vert_v_argmax
  dsimp
  split_ifs
  · trans
    · apply vert_v_max_γ_eq_π <;> constructor <;> linarith
    · apply vert_v_max_ω_when_γ_eq_π <;> constructor <;> linarith
  · trans
    · apply vert_v_max_γ_eq_zero <;> constructor <;> linarith
    · apply vert_v_max_ω_when_γ_eq_zero <;> constructor <;> linarith

/--
Postulated value of the maximum vertical climbing velocity.
-/
noncomputable def vert_v_max_value (φ : ℝ) : ℝ := √2 * Real.cos φ

/--
Correctness of `vert_v_max_value` as the maximum value.
-/
theorem vert_v_max_value_eq {φ γ ω : ℝ}
    (h_arg : (γ, ω) = vert_v_argmax φ)
    (φ_bounds : -Real.pi / 2 < φ ∧ φ < Real.pi / 2) :
    ladder_vert_v_scaled_angles φ γ ω = vert_v_max_value φ := by
  unfold vert_v_argmax at h_arg
  have h₁ : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo (by constructor <;> linarith)
  have h₂ : Real.cos φ ≠ 0 := by linarith
  simp only [ladder_vert_v_scaled_angles, ladder, ladder_n_by_φ, ladder_u_by_γ_ω,
    crossProduct, uvec_k, normalise, norm3, vert_v_max_value]
  split_ifs at h_arg
  · injection h_arg with h_γ h_ω
    simp [h_γ, h_ω, h₂, ← pow_two]
    rw [Real.sqrt_sq (by linarith [h₁]), inv_mul_cancel₀ h₂]
    simp only [Real.sin_add, Real.cos_add, Real.sin_neg, Real.cos_neg, Real.sin_pi_div_four,
      Real.cos_pi_div_four]
    calc
      _ = √2 / 2 * (Real.cos φ + Real.sin φ -
          (Real.sin φ ^ 2 + Real.cos φ ^ 2) * (Real.sin φ - Real.cos φ)) := by
        ring_nf
      _ = √2 * Real.cos φ := by
        simp [Real.sin_sq_add_cos_sq]
        group
  · injection h_arg with h_γ h_ω
    simp [h_γ, h_ω, h₂, ← pow_two]
    rw [Real.sqrt_sq (by linarith [h₁]), inv_mul_cancel₀ h₂]
    simp only [Real.sin_sub, Real.cos_sub, sin_three_pi_div_four, cos_three_pi_div_four]
    calc
      _ = √2 / 2 * (Real.sin φ + Real.cos φ -
          (Real.sin φ ^ 2 + Real.cos φ ^ 2) * (Real.sin φ - Real.cos φ)) := by
        ring_nf
      _ = √2 * Real.cos φ := by
        simp [Real.sin_sq_add_cos_sq]
        group

/--
Postulated constrained argmax for vertical climbing velocity.
-/
noncomputable def vert_v_argmax_constrained (φ : ℝ) : ℝ × ℝ :=
  if φ ≤ 0 then
    (Real.pi, -(φ + Real.pi / 4))
  else if φ ≤ Real.pi / 4 then
    (Real.pi, -(Real.pi / 4))
  else
    (0, -(Real.pi / 4))

/--
Maximisation of the vertical player velocity for φ ∈ (-π/2, π/2) subject to
the constraint ω ∈ [-π/4, π/4] corresponding to when both moveright/moveleft
and forward/back keys are pressed.
-/
theorem vert_v_max_constrained {φ : ℝ} (φ_bounds : -Real.pi / 2 < φ ∧ φ < Real.pi / 2) :
    IsMaxOn (fun ⟨γ, ω⟩ ↦ ladder_vert_v_scaled_angles φ γ ω)
      (Set.Icc (0, -Real.pi / 4) (Real.pi, Real.pi / 4))
      (vert_v_argmax_constrained φ) := by
  intro ⟨γ, ω⟩ ⟨⟨γ_lb, ω_lb⟩, ⟨γ_ub, ω_ub⟩⟩
  unfold vert_v_argmax_constrained
  dsimp
  split_ifs
  · trans
    · apply vert_v_max_γ_eq_π <;> constructor <;> linarith
    · apply vert_v_max_ω_when_γ_eq_π <;> constructor <;> linarith
  · trans
    · apply vert_v_max_γ_eq_π <;> constructor <;> linarith
    · apply vert_v_max_ω_γ_eq_π_constrained <;> constructor <;> linarith
  · trans
    · apply vert_v_max_γ_eq_zero <;> constructor <;> linarith
    · apply vert_v_max_ω_γ_eq_zero_constrained <;> constructor <;> linarith

/--
Postulated value of the constrained maximum vertical climbing velocity.
-/
noncomputable def vert_v_max_value_constrained (φ : ℝ) : ℝ :=
  if φ ≤ 0 then
    √2 * Real.cos φ
  else if φ ≤ Real.pi / 4 then
    √2 * Real.cos φ ^ 2
  else
    √2 / 2 * Real.sin (2 * φ)

/--
Correctness of `vert_v_argmax_constrained` as the maximum value.
-/
theorem vert_v_max_value_constrained_eq {φ γ ω : ℝ}
    (h_arg : ⟨γ, ω⟩ = vert_v_argmax_constrained φ)
    (φ_bounds : -Real.pi / 2 < φ ∧ φ < Real.pi / 2) :
    ladder_vert_v_scaled_angles φ γ ω = vert_v_max_value_constrained φ := by
  unfold vert_v_argmax_constrained at h_arg
  have h₁ : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo (by constructor <;> linarith)
  have h₂ : Real.cos φ ≠ 0 := by linarith
  simp only [ladder_vert_v_scaled_angles, ladder, ladder_n_by_φ, ladder_u_by_γ_ω,
    crossProduct, uvec_k, normalise, norm3, vert_v_max_value_constrained]
  split_ifs at h_arg with h_φ₁ h_φ₂
  · injection h_arg with h_γ h_ω
    simp [h_γ, h_ω, h₂, h_φ₁, ← pow_two]
    rw [Real.sqrt_sq (by linarith [h₁]), inv_mul_cancel₀ h₂]
    simp only [Real.sin_add, Real.cos_add, Real.sin_neg, Real.cos_neg, Real.sin_pi_div_four,
      Real.cos_pi_div_four]
    field_simp
    calc
      _ = Real.cos φ + Real.sin φ +
          (Real.sin φ ^ 2 + Real.cos φ ^ 2) * (-Real.sin φ + Real.cos φ) := by
        ring_nf
      _ = 2 * Real.cos φ := by
        simp [Real.sin_sq_add_cos_sq]
        group
  · injection h_arg with h_γ h_ω
    simp [h_γ, h_ω, h₂, h_φ₁, h_φ₂, ← pow_two]
    rw [Real.sqrt_sq (by linarith [h₁]), inv_mul_cancel₀ h₂]
    calc
      _ = √2 / 2 * (Real.cos φ ^ 2 + 1 - Real.sin φ ^ 2) := by
        group
      _ = √2 * Real.cos φ ^ 2 := by
        simp [Real.sin_sq]
        group
  · injection h_arg with h_γ h_ω
    simp [h_γ, h_ω, h₂, h_φ₁, h_φ₂, ← pow_two]
    rw [Real.sqrt_sq (by linarith [h₁]), inv_mul_cancel₀ h₂]
    calc
      _ = √2 / 2 * (1 - (Real.sin φ ^ 2 + Real.cos φ ^ 2) + 2 * Real.sin φ * Real.cos φ) := by
        group
      _ = √2 / 2 * Real.sin (2 * φ) := by
        simp [Real.sin_sq_add_cos_sq, Real.sin_two_mul]

/--
Multiplier to the formulae for vertical climbing velocity derived above when both
the forward/back and the moveright/moveleft keys are pressed.
-/
noncomputable def fs_mul : ℝ := √2

/--
Holding both forward/back and moveright/moveleft maximises vertical climbing velocity
compared to holding only one key, even after account for the constraint on ω when holding
the two keys.
-/
theorem vert_v_max_f_le_fs {φ γ_f ω_f γ_fs ω_fs : ℝ}
    {h_f : (γ_f, ω_f) = vert_v_argmax φ}
    {h_fs : (γ_fs, ω_fs) = vert_v_argmax_constrained φ}
    (φ_bounds : -Real.pi / 2 < φ ∧ φ < Real.pi / 2) :
    ladder_vert_v_scaled_angles φ γ_f ω_f ≤ fs_mul * ladder_vert_v_scaled_angles φ γ_fs ω_fs := by
  have h_sqrt_2 : 0 < √2 := by positivity
  have h_cos : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo (by constructor <;> linarith)
  rw [fs_mul, vert_v_max_value_eq h_f φ_bounds, vert_v_max_value,
    vert_v_max_value_constrained_eq h_fs φ_bounds, vert_v_max_value_constrained]
  split_ifs
  · rw [mul_le_mul_iff_right₀ h_sqrt_2, le_mul_iff_one_le_left h_cos]
    linarith [Real.one_lt_sqrt_two]
  · rw [mul_le_mul_iff_right₀ h_sqrt_2, pow_two, ← mul_assoc, le_mul_iff_one_le_left h_cos,
      ← div_le_iff₀' h_sqrt_2, ← Real.sqrt_div_self', ← Real.cos_pi_div_four]
    apply Real.cos_le_cos_of_nonneg_of_le_pi <;> linarith
  · simp only [Real.sin_two_mul]
    rw [mul_le_mul_iff_right₀ h_sqrt_2, ← mul_assoc, le_mul_iff_one_le_left h_cos]
    group
    rw [← div_le_iff₀' h_sqrt_2, ← Real.sqrt_div_self', ← Real.sin_pi_div_four]
    apply Real.sin_le_sin_of_le_of_le_pi_div_two <;> linarith

noncomputable def rotateAroundZ (θ : ℝ) (v : Vec3) : Vec3 :=
  ![v 0 * Real.cos θ - v 1 * Real.sin θ, v 0 * Real.sin θ + v 1 * Real.cos θ, v 2]

lemma cross_product_z_symmetry {θ : ℝ} {n : Vec3} :
    uvec_k ⨯₃ n = 0 ↔ uvec_k ⨯₃ rotateAroundZ θ n = 0 := by
  constructor
  · sorry
  · sorry

theorem ladder_z_symmetry {θ : ℝ} {u n : Vec3} :
    (ladder u n) 2 = (ladder (rotateAroundZ θ u) (rotateAroundZ θ n)) 2 := by
  unfold ladder
  by_cases h : uvec_k ⨯₃ n = 0
  · simp only [h, cross_product_z_symmetry.mp]
    simp [rotateAroundZ]
    left
    group
    apply Eq.symm
    calc
      _ = u 0 * n 0 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) +
          u 1 * n 1 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) + u 2 * n 2 := by
        group
      _ = u ⬝ᵥ n := by
        simp only [Real.sin_sq_add_cos_sq, vec3_dotProduct]
        group

  have n_not_vert : uvec_k ⨯₃ rotateAroundZ θ n ≠ 0 := by
    intro h'
    apply h
    exact (cross_product_z_symmetry (θ := θ) (n := n)).mpr h'

  simp [h, n_not_vert]
  conv in rotateAroundZ θ u 2 => simp [rotateAroundZ]
  rw [sub_right_inj]

  simp [
    show rotateAroundZ θ u ⬝ᵥ rotateAroundZ θ n * rotateAroundZ θ n 2 = u ⬝ᵥ n * n 2 by
      simp [rotateAroundZ]
      left
      -- TODO: copy pasted from h₃
      calc
        _ = (Real.sin θ ^ 2 + Real.cos θ ^ 2) * u 0 * n 0 +
            (Real.sin θ ^ 2 + Real.cos θ ^ 2) * u 1 * n 1 + u 2 * n 2 := by
          group
        _ = u ⬝ᵥ n := by
          simp only [Real.sin_sq_add_cos_sq, vec3_dotProduct]
          group
  ]

  have h₃ : rotateAroundZ θ u ⬝ᵥ rotateAroundZ θ n = u ⬝ᵥ n := by
    simp [rotateAroundZ]
    calc
      _ = (Real.sin θ ^ 2 + Real.cos θ ^ 2) * u 0 * n 0 +
          (Real.sin θ ^ 2 + Real.cos θ ^ 2) * u 1 * n 1 + u 2 * n 2 := by
        group
      _ = u ⬝ᵥ n := by
        simp only [Real.sin_sq_add_cos_sq, vec3_dotProduct]
        group
  simp [h₃]
  left

  simp [crossProduct, rotateAroundZ, uvec_k]
  conv_lhs =>
    simp [normalise, norm3, ← pow_two]
    field_simp
  simp [normalise]

  have h₅ : norm3 ![-(n 1 * Real.cos θ) + -(n 0 * Real.sin θ),
      n 0 * Real.cos θ - n 1 * Real.sin θ, 0] = √(n 0 ^ 2 + n 1 ^ 2) := by
    simp [norm3]
    calc
      _ = √((Real.sin θ ^ 2 + Real.cos θ ^ 2) * (n 0 ^ 2 + n 1 ^ 2)) := by
        group
      _ = √(n 0 ^ 2 + n 1 ^ 2) := by
        simp [Real.sin_sq_add_cos_sq]
  simp [h₅]
  field_simp
  conv in n 1 ^ 2 + n 0 ^ 2 => simp [add_comm]

  rw [div_left_inj']
  · apply Eq.symm
    calc
      _ = (n 0 ^ 2 + n 1 ^ 2) * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by
        ring_nf
      _ = n 0 ^ 2 + n 1 ^ 2 := by
        simp [Real.sin_sq_add_cos_sq]

  rw [Real.sqrt_ne_zero']
  apply vec_horizontal_pos h
