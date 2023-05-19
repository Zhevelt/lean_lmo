import tactic

/-

# If integers a, b have form x^2 - 5y^2, then ab also has this form

Question 62.14 in Fomin's book "Leningrad Mathematical Olympiads".

-/

-- Cool number is the number which has this form
def is_cool (a: ℤ) : Prop :=
∃ x y : ℤ, a = x^2 - 5 * y ^ 2

-- If two numbers are cool, so is their product
theorem lmo62_14' {a b: ℤ} (ha: is_cool a) (hb: is_cool b):
  is_cool (a*b) :=
begin
  cases ha with xa hya,
  cases hya with ya ha,
  cases hb with xb hyb,
  cases hyb with yb hb,

  use [(xb*xa + 5*yb*ya), (xb*ya + yb*xa)],
  nlinarith,
end

theorem lmo62_14 {a b: ℤ} (ha: ∃ x y : ℤ, a = x^2 - 5 * y ^ 2) (hb: ∃ x y : ℤ, b = x^2 - 5 * y ^ 2):
  ∃ x y : ℤ, a*b = x^2 - 5 * y ^ 2 :=
begin
  have h:= lmo62_14' ha hb,
  exact h,
end