import analysis.seminorm

noncomputable theory

structure ring_seminorm (𝕜 : Type*) (E : Type*) [semi_normed_ring 𝕜] [semiring E] [has_scalar 𝕜 E]
  extends seminorm 𝕜 E :=
(mul : ∀ x y : E, to_fun (x * y) ≤ to_fun x * to_fun y)

variables {K : Type*} [semi_normed_ring K] 

lemma ring_seminorm.pow_le [norm_one_class K] {R : Type*} [ring R] [module K R]
  (f : ring_seminorm K R) (r : R) : ∀ {n : ℕ}, 0 < n → f.to_fun (r ^ n) ≤ (f.to_fun r) ^ n
| 1 h := by simp only [pow_one]
| (n + 2) h := 
begin
  simpa [pow_succ _ (n + 1)] using
  le_trans (f.mul r _) (mul_le_mul_of_nonneg_left (ring_seminorm.pow_le n.succ_pos) (f.to_seminorm.nonneg _)),
end
/- by simpa [pow_succ _ (n + 1)] using le_trans (f.mul r _)
    (mul_le_mul_left' (f.pow_le n.succ_pos) _) -/

variables {R : Type*} [ring R]

instance has_scalar' : has_scalar punit R := { smul := λ r x, 0 }

instance asdf : module punit R := {
  one_smul := λ b,
  begin
    simp only [punit.one_eq], 
    rw ← punit.zero_eq,
    sorry,
  end,
  mul_smul := sorry,
  smul_add := sorry,
  smul_zero := sorry,
  add_smul := sorry,
  zero_smul := sorry,
  ..has_scalar'  }

def foo : ring_seminorm unit ℝ :=
{ to_fun := λ r, ∥r∥,
  smul' := λ r x, by { rw [punit.norm_eq_zero, zero_mul, norm_eq_zero], refl },
  triangle' := sorry,
  mul := sorry }

#exit

/-- A function `f : R → ℝ≥0` satisfies `is_norm_le_one_class` if `f 1 ≤ 1`. -/
def is_norm_le_one_class {R : Type*} [semiring R] (f : R → ℝ≥0) : Prop := f 1 ≤ 1

/-- A function `f : R → ℝ≥0` satisfies `is_norm_one_class` if `f 1 = 1`. -/
def is_norm_one_class {R : Type*} [semiring R] (f : R → ℝ≥0) : Prop := f 1 = 1

lemma is_ring_norm_one_class_iff_nontrivial {R : Type*} [semiring R] {f : R → ℝ≥0}
  (hsn : is_ring_seminorm f) (hf1 : f 1 ≤ 1) : is_norm_one_class f ↔ ∃ r : R, f r ≠ 0 :=
begin
  rw is_norm_one_class,
  refine ⟨λ h, _, λ h, _⟩,
  { use 1,
    rw h, exact one_ne_zero, },
  { obtain ⟨x, hx⟩ := h,
    by_cases hf0 : f 1 = 0,
    { have hx' : f x ≤ 0,
      { rw ← mul_one x,
        apply le_trans (hsn.mul x 1) _,
        rw [hf0, mul_zero], },
      exact absurd (le_antisymm hx' (f x).2 ) hx, },
    { have h1 : f 1 * 1 ≤ f 1 * f 1,
      { conv_lhs{ rw ← one_mul (1 : R)},
        convert hsn.mul 1 1,
        rw mul_one, },
      rw mul_le_mul_left (lt_of_le_of_ne (zero_le (f 1)) (ne.symm hf0)) at h1,
      exact le_antisymm hf1 h1, }}
end

/-- A function `f : R → ℝ≥0` is a norm if it is a seminorm and `f x = 0` implies `x = 0`. -/
structure is_ring_norm {R : Type*} [semiring R] (f : R → ℝ≥0) extends (is_ring_seminorm f) : Prop :=
(ne_zero : ∀ r, r ≠ 0 → 0 < f r)

lemma field.is_ring_norm_of_is_ring_seminorm {R : Type*} [field R] {f : R → ℝ≥0}
  (hf : is_ring_seminorm f) (hnt : ∃ r : R, 0 ≠ f r) : is_ring_norm f :=
{ ne_zero := λ x hx, begin
    obtain ⟨c, hc⟩ := hnt,
    have hfx : 0 ≠ f x,
    { intro h0,
      have hc' : f c ≤ 0,
      { rw [← mul_one c, ← mul_inv_cancel hx, ← mul_assoc, mul_comm c, mul_assoc],
        refine le_trans (hf.mul x _) _,
        rw [← h0, zero_mul] },
      exact hc (ge_antisymm hc' (zero_le (f c))), },
    exact lt_of_le_of_ne (zero_le (f _)) hfx,
  end,
  ..hf }

/-- Given a ring `R` with a norm `f` and an `R`-algebra `A`, a function `g : A → ℝ≥0` is an algebra
  norm if it is a norm on `A` and `g ((algebra_map R A r) * a) = f r * g a`. -/
structure is_algebra_norm (R : Type*) [comm_ring R] {f : R → ℝ≥0} (hf : is_ring_norm f)
  {A : Type*} [ring A] [algebra R A] (g : A → ℝ≥0) extends (is_ring_norm g) : Prop :=
(smul : ∀ (r : R) (a : A) , g ((algebra_map R A r) * a) = f r * g a)

/-- A function `f : R → ℝ≥0` is nonarchimedean if it satisfies the inequality
  `f (r + s) ≤ max (f r) (f s)`. -/
def is_nonarchimedean {R : Type*} [ring R] (f : R → ℝ≥0) : Prop :=
∀ r s, f (r + s) ≤ max (f r) (f s)

/-- A function `f : R → ℝ≥0` is power-multiplicative if for all `r ∈ R` and all positive `n ∈ ℕ`,
  `f (r ^ n) = (f r) ^ n`. -/
def is_pow_mul {R : Type*} [ring R] (f : R → ℝ≥0) :=
∀ (r : R) {n : ℕ} (hn : 1 ≤ n), f (r ^ n) = (f r) ^ n

lemma seminormed_ring.to_is_ring_seminorm (R : Type*) [semi_normed_ring R] :
  is_ring_seminorm (λ r : R, ∥r∥₊) :=
{ zero := nnnorm_zero,
  add  := nnnorm_add_le,
  mul  := nnnorm_mul_le }

lemma normed_ring.to_is_ring_norm (R : Type*) [normed_ring R] :
  is_ring_norm (λ r : R, ∥r∥₊) :=
{ zero    := nnnorm_zero,
  add     := nnnorm_add_le,
  mul     := nnnorm_mul_le,
  ne_zero :=  λ x hx, nnnorm_pos_iff.mpr hx }