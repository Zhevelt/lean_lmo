import tactic
import data.zmod.basic

/-

# Solve in natural numbers: (z+1)^x - z^y = -1

Question 63.25 in Fomin's book "Leningrad Mathematical Olympiads".

Solutuon:
LHS has remainder 1 mod z, RHS has remainder -1 mod z, so z is either 1 or 2.
If z = 1, then 2^x = 0, impossible.
If z = 2, then we have 3^x + 1 = 2^y.
LHS is not divisible by 8, so y is either 1 or 2.
If y = 1, then 3^x = 1, impossible in naturals.
y = 2 gives solution (x, y, z) = (1, 2, 2)

-/

-- First step: z = 1 or z = 2
lemma z_eq_one_or_z_eq_two {x y z : ℕ} (hx: x ≥ 1) (hy: y ≥ 1) (hz: z ≥ 1):
(((z+1)^x : ℤ) - z^y = -1) → z=1 ∨ z=2 :=
begin
  intro h,
  have lhs_eq_1_mz: ((z + 1) ^ x : zmod z) - z ^ y = 1,
    have h': (z ^ y : zmod z) = 0,
      have hz0: (z : zmod z) = 0 := by norm_num,
      rw hz0,
      apply zero_pow',
      linarith,

    have h'': ((z + 1) ^ x : zmod z) = 1,
      have hz0: (z : zmod z) = 0 := by norm_num,
      rw hz0,
      simp,
    rw [h', h''],
    simp,

  have lhs_eq_m1_mz: (((z+1)^x : ℤ): zmod z) - z^y = -1,
    norm_cast,
    norm_cast at h,
    rw h,
    simp,
    
  have m1_eq_1_mz: (-1 : zmod z) = 1 := by finish,
  
  have zero_eq_2_mz: ((2: ℕ): zmod z) = 0,
    push_cast,
    nth_rewrite 0 ← m1_eq_1_mz,
    norm_num,

  rw zmod.nat_coe_zmod_eq_zero_iff_dvd at zero_eq_2_mz,
  have hhh: z ≤ 2,
    apply nat.le_of_dvd,
  norm_num,
  assumption,
  interval_cases z;
    norm_num,
end

open nat

-- 3^x + 1 is not divisible by 8.
lemma pow_of_three_add_one_not_dvd_eight (x: ℕ):
¬ 8 ∣ (3^x: ℤ) + 1 :=
begin
  intro h,
  have h' := (zmod.int_coe_zmod_eq_zero_iff_dvd (3^x+1) 8).mpr h,
  rw int.cast_add at h',
  simp at h',
  have h31: (3: zmod 8)^x+1 = 4 ∨ (3: zmod 8)^x+1 = 2 := 
    nat.rec_on x _ _,
    rw h' at h31, -- this should be much shorter, but whatever
    cases h31 with h31' h31'',
    {
      have h''':= (zmod.nat_coe_zmod_eq_zero_iff_dvd 4 8).mp,
      have h'''': ((4: ℕ): zmod 8) = 0,
        rw h31',
        refl,
      have h'':= h''' h'''',
      have h:= le_of_dvd (show 0<4, by norm_num) h'',
      linarith,
    },
    {
      have h''':= (zmod.nat_coe_zmod_eq_zero_iff_dvd 2 8).mp,
      have h'''': ((2: ℕ): zmod 8) = 0,
        rw h31'',
        refl,
      have h'':= h''' h'''',
      have h:= le_of_dvd (show 0<2, by norm_num) h'',
      linarith,
    },
    norm_num,
    intros n hind,
    cases hind with h2 h4,
    {
      right,
      have h33: (3: zmod 8)^n = 3,
        replace h2: (3: zmod 8)^n + 1 = 3 + 1 := by tauto,
        exact (add_left_inj 1).mp h2,
      change (3: zmod 8) ^ (n+1) + 1 = 2,
      rw pow_add,
      rw h33,
      tauto,
    },
    {
      left,
      have h33: (3: zmod 8)^n = 1,
        replace h4: (3: zmod 8)^n + 1 = 1 + 1 := by tauto,
        exact (add_left_inj 1).mp h4,
      change (3: zmod 8) ^ (n+1) + 1 = 4,
      rw pow_add,
      rw h33,
      tauto,
    },
end

theorem lmo63_25 (x y z : ℕ) (hx: x ≥ 1) (hy: y ≥ 1) (hz: z ≥ 1):
((z+1)^x : ℤ) - z^y = -1 ↔ x=1 ∧ y=2 ∧ z=2 :=
begin
  split,
  {
    intro h,
    replace hz := z_eq_one_or_z_eq_two hx hy hz h,
    cases hz,
    {
      exfalso,
      rw hz at h,
      simp at h,
      have h':= pow_ne_zero x (show ((1+1:ℤ) ≠ 0), by norm_num),
      rw h at h',
      finish,
    },
    rw hz at h,
    simp at h,
    ring_nf at h,
    replace h: (3^x:ℤ) + 1 = 2^y,
      rw eq_add_of_sub_eq h,
      ring,
    have h':= pow_of_three_add_one_not_dvd_eight x,
    rw h at h',
    by_cases h3: (y ≥ 3),
    {
      exfalso,
      have hh: y = (y-3) + 3,
        exact (nat.sub_eq_iff_eq_add h3).mp rfl,
      rw [hh, pow_add] at h',
      apply h',
      use 2 ^ (y - 3),
      ring,
    },
    replace h3: y<3 := by linarith,
    interval_cases y;
    norm_num,
    {
      replace h: (3^x: ℤ) = 1 := by {rw [pow_one, (show ((2:ℤ)=1+1), by norm_num)] at h, simpa using h},
      have hhh := (pow_le_one_iff_of_nonneg (show (3 ≥ 0), by linarith) (show (x ≠ 0), by linarith)).mp (show (3^x ≤ 1), by linarith),
      linarith,
    },
    replace h: (3^x: ℤ) = 3 := by {rw [pow_two, show ((2:ℤ)*2=3+1), by norm_num] at h, simpa using h},
    split,
    nth_rewrite 1 ← pow_one (3: ℤ) at h,
    have hh:= (pow_le_iff_le_right (show 2 ≤ 3, by linarith)).mp (show 3 ^ x ≤ 3 ^ 1, by linarith),
    linarith,
    exact hz,
  },
  finish,
end