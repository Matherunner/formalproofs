import Mathlib.Tactic
import Mathlib.LinearAlgebra.CrossProduct

/-!
# Optimal ladder climbing angles

This file formalises the *vertical velocity* of a player on a Half-Life ladder and
proves the optimal direction for u (input yaw γ and pitch ω).

See https://jwchong.com/hl/ladder.html for background and context.

## Main results

* `vert_v_max`: The main theorem proving that for a given ladder tilt φ ∈ [0, -π),
  the vertical velocity is maximised at γ = π and ω = -(φ + π/4).
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
  have zero_lt_cos_φ : 0 < Real.cos φ := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith
  simp only [ladder_vert_v_scaled_angles, ladder, n_not_vert (by linarith), ladder_u_by_γ_ω]
  simp [ladder_n_by_φ, crossProduct, normalise, norm3, uvec_k, Real.cos_add]
  field_simp
  simp [Real.sqrt_sq (by linarith)]
  linarith

/--
An expression for the postulated maximum.
-/
lemma vert_v_star {φ : ℝ} (φ_bounds : -Real.pi / 2 < φ ∧ φ < Real.pi / 2) :
    ladder_vert_v_scaled_angles φ Real.pi (-(φ + Real.pi / 4)) = √2 * Real.cos φ := by
  simp [vert_v_simp φ_bounds, Real.sin_neg, Real.cos_neg, Real.sin_add, Real.cos_add,
    Real.sin_pi_div_four, Real.cos_pi_div_four, Real.cos_pi]
  field_simp
  rw [Real.sq_sqrt (by linarith)]
  field_simp
  calc
    _ = Real.sin φ + Real.cos φ +
        (Real.sin φ ^ 2 + Real.cos φ ^ 2) * (Real.cos φ - Real.sin φ) := by
      ring
    _ = 2 * Real.cos φ := by
      rw [Real.sin_sq_add_cos_sq]
      group

/--
V parametrisation is monotonically increasing for γ ∈ [0, π].
-/
lemma vert_v_simp_γ_monotone {φ ω : ℝ}
    (φ_bounds : -Real.pi / 2 < φ ∧ φ ≤ Real.pi / 4)
    (ω_bounds : -Real.pi / 2 ≤ ω ∧ ω ≤ Real.pi / 2) :
    MonotoneOn (fun γ ↦ ladder_vert_v_scaled_angles φ γ ω) (Set.Icc 0 Real.pi) := by
  intro a arange b brange a_le_b
  have h_φ : -Real.pi / 2 < φ ∧ φ < Real.pi / 2 := by constructor <;> linarith
  simp only [vert_v_simp h_φ]
  gcongr
  · apply Real.cos_nonneg_of_mem_Icc
    constructor <;> linarith
  · apply Real.cos_nonneg_of_mem_Icc
    constructor <;> linarith
  · apply Real.cos_nonneg_of_mem_Icc
    constructor <;> linarith
  · exact Real.cos_le_cos_of_nonneg_of_le_pi arange.1 brange.2 a_le_b

/--
V is maximised at γ = π for all φ and ω in their respective bounds.
-/
lemma vert_v_max_γ_eq_pi {φ ω : ℝ}
    (φ_bounds : -Real.pi / 2 < φ ∧ φ ≤ Real.pi / 4)
    (ω_bounds : -Real.pi / 2 ≤ ω ∧ ω ≤ Real.pi / 2) :
    IsMaxOn (fun γ ↦ ladder_vert_v_scaled_angles φ γ ω) (Set.Icc 0 Real.pi) Real.pi := by
  intro γ γrange
  simp at γrange
  apply vert_v_simp_γ_monotone φ_bounds ω_bounds γrange
  · simp [Real.pi_nonneg]
  · linarith

/--
Fix γ = π, then V is maximised when ω = -(φ + Real.pi / 4).
-/
lemma vert_v_max_ω_when_γ_eq_π {φ : ℝ} (φ_bounds : -Real.pi / 2 < φ ∧ φ ≤ Real.pi / 4) :
    IsMaxOn (ladder_vert_v_scaled_angles φ Real.pi)
      (Set.Icc (-Real.pi / 2) (Real.pi / 2))
      (-(φ + Real.pi / 4)):= by
  intro ω ωset
  have h_φ : -Real.pi / 2 < φ ∧ φ < Real.pi / 2 := by constructor <;> linarith
  set p := ω + φ + Real.pi / 4 with hp
  simp only [show ω = p - φ - Real.pi / 4 by linarith, vert_v_star h_φ, vert_v_simp h_φ]
  calc
    _ = -Real.sin (p - φ - Real.pi / 4) +
        √2 * Real.cos (p - φ - Real.pi / 4 + φ) * Real.cos (φ + Real.pi / 4) := by
      simp only [Real.cos_pi, Real.cos_add]
      ring_nf
    _ = -Real.sin (p - (φ + Real.pi / 4)) +
        √2 * Real.cos (p - Real.pi / 4) * Real.cos (φ + Real.pi / 4)  := by
      ring_nf
    _ = -Real.sin (p - (φ + Real.pi / 4)) +
        (Real.cos p + Real.sin p) * Real.cos (φ + Real.pi / 4):= by
      simp [Real.cos_sub, Real.cos_pi_div_four, Real.sin_pi_div_four]
      field_simp
      simp [Real.sq_sqrt]
    _ = Real.cos p * (Real.sin (φ + Real.pi / 4) + Real.cos (φ + Real.pi / 4)) := by
      simp [Real.sin_sub]
      ring_nf
    _ = √2 * Real.cos p * Real.cos φ := by
      simp only [Real.sin_add, Real.cos_add, Real.cos_pi_div_four, Real.sin_pi_div_four]
      ring_nf
    √2 * Real.cos p * Real.cos φ ≤ √2 * Real.cos φ := by
      gcongr
      · grind [Real.cos_nonneg_of_mem_Icc]
      · have hcos : Real.cos p ≤ 1 := Real.cos_le_one p
        have hsqrt : 0 ≤ √2 := by positivity
        nlinarith

/--
Maximisation of the vertical component of player velocity.
-/
theorem vert_v_max {φ : ℝ} (φ_bounds : -Real.pi / 2 < φ ∧ φ ≤ Real.pi / 4) :
    IsMaxOn (fun ⟨γ, ω⟩↦ ladder_vert_v_scaled_angles φ γ ω)
      ((Set.Icc 0 Real.pi) ×ˢ (Set.Icc (-Real.pi / 2) (Real.pi / 2)))
      (Real.pi, -(φ + Real.pi / 4)) := by
  intro ⟨γ, ω⟩ ⟨γ_bounds, ω_bounds⟩
  dsimp
  trans
  · exact vert_v_max_γ_eq_pi φ_bounds ω_bounds γ_bounds
  · exact vert_v_max_ω_when_γ_eq_π φ_bounds ω_bounds
