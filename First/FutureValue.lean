import Mathlib.Tactic

-- Future value with fixed contribution recurrence relation
def fv_fixed (n : ℕ) (p r c₀ : ℝ) : ℝ :=
  match n with
  | 0 => c₀
  | n + 1 => (1 + r) * fv_fixed n p r c₀ + p

-- Closed form for future value with fixed contribution
noncomputable def fv_fixed_sol (n : ℕ) (p r c₀ : ℝ) : ℝ :=
  c₀ * (1 + r) ^ n + p / r * ((1 + r) ^ n - 1)

-- Closed form satisfies the recurrence relation
theorem fv_fixed_sol_satisfied (p r c₀ : ℝ) (rpos : 0 < r) :
    ∀ n, fv_fixed n p r c₀ = fv_fixed_sol n p r c₀ := by
  unfold fv_fixed_sol fv_fixed
  intro n
  induction n with
  | zero => simp
  | succ => grind [fv_fixed]

-- Future value with growing contribution recurrence relation
def fv_inc (n : ℕ) (p₀ r rₚ c₀ : ℝ) : ℝ :=
  match n with
  | 0 => c₀
  | n + 1 => (1 + r) * fv_inc n p₀ r rₚ c₀ + p₀ * (1 + rₚ) ^ n

-- Closed form for future value with growing contribution
noncomputable def fv_inc_sol (n : ℕ) (p₀ r rₚ c₀ : ℝ) : ℝ :=
  c₀ * (1 + r) ^ n +
  if r = rₚ then
    p₀ * n * (1 + r) ^ (n - 1)
  else
    p₀ * ((1 + r) ^ n - (1 + rₚ) ^ n) / (r - rₚ)

-- Closed form satisfies the recurrence relation
theorem fv_inc_sol_satisfied (p₀ r rₚ c₀ : ℝ) :
    ∀ n, fv_inc n p₀ r rₚ c₀ = fv_inc_sol n p₀ r rₚ c₀ := by
  intro n
  induction n with
  | zero => simp [fv_inc, fv_inc_sol]
  | succ n ih =>
    simp [fv_inc, fv_inc_sol, ih]
    by_cases h_r_eq : r = rₚ
    · -- Split by n = 0 and n ≥ 1 due to difficulties with n - 1 + 1
      cases n <;> grind
    · grind
