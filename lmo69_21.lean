import tactic
import data.real.sqrt

/-

# Let m, n be natural numbers such that m/n < √2. Prove m/n < √2 * (1 - 1/(4n²))

Question 69.21 in Fomin's book "Leningrad Mathematical Olympiads".

Solutuon:
√2 - m/n = (2 - m²/n²) / (√2 + m/n) > (2n² - m²) / (2√2 * n²) ≥ 1 / (2√2 * n²)

-/

open real
lemma hb {m n: ℕ} (hn: n ≥ 1) (h: (m/n: ℝ) < sqrt 2):
(2:ℝ)*n^2-m^2 ≥ 1 :=
begin
  have mnge0: 0 ≤ (m/n: ℝ) := div_nonneg (show (m:ℝ) ≥ 0, by exact nat.cast_nonneg m) (show (n:ℝ) ≥ 0, by exact nat.cast_nonneg n),
  have hb': (m/n:ℝ)^2 < 2 := (lt_sqrt mnge0 (show 0 ≤ (2: ℝ), by linarith)).mp h,
  rw div_pow at hb',
  have nge0: (n:ℝ) > 0 := nat.cast_pos.mpr (show 0<n, by linarith),
  have n2ge0: (n:ℝ)^2 > 0 := by nlinarith,
  have hb'': (m:ℝ)^2 < 2*n^2 := (div_lt_iff n2ge0).mp hb',
  have hb''': (2:ℝ)*n^2-m^2 > 0 := by linarith,
  norm_cast at *,
  rw ← nat.cast_sub,
  rw ← nat.cast_sub at hb''',
  rw ← nat.cast_zero at hb''',
  rw nat.cast_lt at hb''',
  have hb'''': 1 ≤  2*n^2 - m^2 := by linarith,
  assumption_mod_cast,
  linarith,
  linarith,
end

lemma step1 {m n: ℕ} (hn: n ≥ 1) (h: (m/n: ℝ) < sqrt 2):
sqrt 2 - m/n = (2 - m^2/n^2)*n^2/((sqrt 2 + m/n)*n^2) :=
begin
  have denomne0: (sqrt 2 + m/n)*n^2 ≠ 0,
  {
    have mnge0: (m/n: ℝ) ≥ 0 := div_nonneg (show (m:ℝ) ≥ 0, by exact nat.cast_nonneg m) (show (n:ℝ) ≥ 0, by exact nat.cast_nonneg n),
    have sqrt2g0: sqrt 2 > 0 := by linarith,
    have sqrt2pmnge0: sqrt 2 + m/n > 0 := by linarith,
    have nge0: (n:ℝ) > 0 := nat.cast_pos.mpr (show 0<n, by linarith),
    have n2ge0: (n:ℝ)^2 > 0 := by nlinarith,
    have lhsge0: (sqrt 2 + m/n)*n^2 > 0 := mul_pos sqrt2pmnge0 n2ge0,
    linarith,
  },
  have step1': (sqrt 2 - m/n) = (sqrt 2 - m/n)*((sqrt 2 + m/n)*n^2)/((sqrt 2 + m/n)*n^2),
  {
    have reduce1: ((sqrt 2 + m/n)*n^2)/((sqrt 2 + m/n)*n^2) = 1 := by {rw div_eq_iff denomne0, norm_num},
    have assoc: (sqrt 2 - m/n)*((sqrt 2 + m/n)*n^2)/((sqrt 2 + m/n)*n^2) = (sqrt 2 - m/n)*(((sqrt 2 + m/n)*n^2)/((sqrt 2 + m/n)*n^2)) := by ring,
    rw assoc,
    rw reduce1,
    norm_num,
  },
  rw step1',
  have step1'': (sqrt 2 - m/n)*(sqrt 2 + m/n) = 2 - m^2/n^2,
  {
    rw [sub_mul, mul_add, mul_add, ← pow_two, sq_sqrt (show 0 ≤ (2: ℝ), by norm_num), ← sub_sub],
    ring_nf,
    simp,
  },
  rw [← mul_assoc, step1''],
end

lemma step2 {m n: ℕ} (hn: n ≥ 1) (h: (m/n: ℝ) < sqrt 2):
((2: ℝ) - m^2/n^2)*n^2/((sqrt 2 + m/n)*n^2) > (2*n^2-m^2)/(2*(sqrt 2)*n^2) :=
begin
  have hb: (2:ℝ)*n^2-m^2 ≥ 1 := hb hn h,
  have step2': ((2: ℝ) - m^2/n^2)*n^2/((sqrt 2 + m/n)*n^2) = (2*n^2-m^2)/((sqrt 2)*n^2 + m*n),
  {
    rw [sub_mul, add_mul],
    have comm': (m:ℝ)^2 / n^2 * n^2 = (m:ℝ)^2 * n^2 / n^2 := by ring,
    have assoc': (m:ℝ)^2 * n^2 / n^2 = (m:ℝ)^2 * (n^2 / n^2) := by ring,
    have nge0: (n:ℝ) > 0 := nat.cast_pos.mpr (show 0<n, by linarith),
    have n2ne0: (n:ℝ)^2 ≠ 0 := by nlinarith,
    have reduce': (n^2:ℝ)/n^2 = 1 := by {rw div_eq_iff n2ne0, norm_num},
    rw [comm', assoc', reduce', mul_one],

    have comm'': (m:ℝ) / n * n^2 = (m:ℝ) * n^2 / n := by ring,
    nth_rewrite 1 pow_two at comm'',
    have assoc'': (m:ℝ) * (n * n) / n = (m:ℝ) * n * (n / n) := by ring,
    have nne0: (n:ℝ) ≠ 0 := by nlinarith,
    have reduce'': (n:ℝ)/n = 1 := by {rw div_eq_iff nne0, norm_num},
    rw [comm'', assoc'', reduce'', mul_one],
  },
  have step2'': (sqrt 2)*n^2 + m*n < 2*(sqrt 2)*n^2,
  {
    have nge0: (n:ℝ) > 0 := nat.cast_pos.mpr (show 0<n, by linarith),
    have h': (m: ℝ) < (sqrt 2) * n := by rwa ← div_lt_iff nge0,
    replace h': (sqrt 2) * n + m < (sqrt 2) * n + (sqrt 2) * n := add_lt_add_left h' (sqrt 2 * ↑n),
    replace h': (sqrt 2) * n + m < 2 * (sqrt 2) * n := by {rw two_mul, convert h', ring},
    replace h': ((sqrt 2) * n + m)*n < 2 * (sqrt 2) * n * n := (mul_lt_mul_right nge0).mpr h',
    replace h': ((sqrt 2) * n + m)*n < 2 * (sqrt 2) * (n * n),
    {
      nth_rewrite 1 mul_assoc at h',
      nth_rewrite 0 mul_assoc at h',
      nth_rewrite 0 mul_assoc at h',
      nth_rewrite 0 ← mul_assoc at h',
      exact h',
    },
    replace h': ((sqrt 2) * n + m)*n < 2 * (sqrt 2) * n^2 := by rwa ← pow_two (n: ℝ) at h',
    replace h': (sqrt 2) * n^2 + m*n < 2 * (sqrt 2) * n^2 := by rwa (show (sqrt 2) * n^2 + m*n = ((sqrt 2) * n + m)*n , by ring),
    exact h'      
  },
  have step2''': (2*(n:ℝ)^2-m^2)/(2*(sqrt 2)*n^2) < (2*n^2-m^2)/((sqrt 2)*n^2 + m*n),
  {
    have numgt0: 0 < 2*(n:ℝ)^2-m^2 := by linarith,
    have denumgt0: 0 < (sqrt 2)*n^2 + m*n,
    {
      have mnge0: (m/n: ℝ) ≥ 0 := div_nonneg (show (m:ℝ) ≥ 0, by exact nat.cast_nonneg m) (show (n:ℝ) ≥ 0, by exact nat.cast_nonneg n),
      have sqrt2g0: sqrt 2 > 0 := by linarith,
      have nge0: (n:ℝ) > 0 := nat.cast_pos.mpr (show 0<n, by linarith),
      have n2ge0: (n:ℝ)^2 > 0 := by nlinarith,
      have mge0: (m:ℝ) ≥ 0 := nat.cast_nonneg m,
      nlinarith,
    },
    exact div_lt_div' (show (2*(n:ℝ)^2-m^2) ≤ (2*(n:ℝ)^2-m^2), by linarith) step2'' numgt0 denumgt0,
  },
  linarith,
end

theorem lmo69_21 {m n: ℕ} (hn: n ≥ 1) (h: (m/n: ℝ) < sqrt 2):
  (m/n: ℝ) < sqrt 2 * (1 - 1/(4*n^2)) :=
begin
  have hb: (2:ℝ)*n^2-m^2 ≥ 1 := hb hn h,

  have step1: sqrt 2 - m/n = (2 - m^2/n^2)*n^2/((sqrt 2 + m/n)*n^2) := step1 hn h,
  
  have step2: ((2: ℝ) - m^2/n^2)*n^2/((sqrt 2 + m/n)*n^2) > (2*n^2-m^2)/(2*(sqrt 2)*n^2) := step2 hn h,

  rw ← step1 at step2,
  have step3: sqrt 2 - m/n > 1 / (2*(sqrt 2)*n^2),
  {
    rw div_eq_inv_mul at *,
    rw div_eq_inv_mul at *,
    rw div_eq_inv_mul at *,
    have hhhh: ((2: ℝ) * sqrt 2 * n ^ 2)⁻¹ > 0,
    {
      have hhhhh: (2: ℝ) * sqrt 2 > 0 := by norm_num,
      have nge0: (n:ℝ) > 0 := nat.cast_pos.mpr (show 0<n, by linarith),
      have n2ge0: (n:ℝ)^2 > 0 := by nlinarith,
      have hhhhhh: (2: ℝ) * sqrt 2 * n ^ 2 > 0 := by nlinarith,
      exact inv_pos.mpr hhhhhh,
    },
    have hhh: ((2: ℝ) * sqrt 2 * n ^ 2)⁻¹ * 1 ≤ (2 * sqrt 2 * n ^ 2)⁻¹ * (2 * n ^ 2 - m ^ 2),
    {
      apply (mul_le_mul_left hhhh).mpr,
      linarith,
    },

    linarith,
  },
  norm_num at step3,
  rw lt_sub at step3,
  convert step3,
  rw [mul_sub, mul_one],
  rw (show (4:ℝ)=2*2, by norm_num),
  nth_rewrite 2 (show (2:ℝ)=(sqrt 2)*(sqrt 2), by {rw ← pow_two, rw sq_sqrt (show (0:ℝ) ≤ 2, by norm_num)}),
  rw (show (sqrt 2) * (1 / ((sqrt 2)*(sqrt 2)*2*n^2)) = (sqrt 2 * 1 / ((sqrt 2)*(sqrt 2)*2*n^2)), by ring),
  rw mul_one,
  nth_rewrite 1 mul_assoc,
  nth_rewrite 0 mul_assoc,
  rw div_mul_right,
  finish,
  norm_num,
end
