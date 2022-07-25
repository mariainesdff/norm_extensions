import analysis.seminorm

noncomputable theory
--open_locale nnreal

set_option old_structure_cmd true

variables {R : Type*} (x y : R) (r : ℝ)

/-- A seminorm on a ring `R` is a function `f : R → ℝ` that preserves zero, takes nonnegative 
  values, is subadditive and submultiplicative and such that `f (-x) = f x` for all `x ∈ R`. -/
structure ring_seminorm (R : Type*) [ring R]
  extends add_group_seminorm R :=
(mul_le' : ∀ x y : R, to_fun (x * y) ≤ to_fun x * to_fun y)

attribute [nolint doc_blame] ring_seminorm.to_add_group_seminorm

namespace ring_seminorm

variables [ring R]

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : has_coe_to_fun (ring_seminorm R) (λ _, R → ℝ) := ⟨λ p, p.to_fun⟩

@[ext] lemma ext {p q : ring_seminorm R} (h : ∀ x, p x = q x) : p = q :=
by { cases p, cases q, simp only, ext, exact h x }

instance : has_zero (ring_seminorm R) := 
⟨{ mul_le' :=  λ _ _, eq.ge (zero_mul _),
  ..add_group_seminorm.has_zero.zero }⟩

instance : inhabited (ring_seminorm R) := ⟨0⟩

variables (p : ring_seminorm R)

protected lemma nonneg : 0 ≤ p x := p.nonneg' _
@[simp] protected lemma map_zero : p 0 = 0 := p.map_zero'
protected lemma add_le : p (x + y) ≤ p x + p y := p.add_le' _ _
@[simp] protected lemma neg : p (- x) = p x := p.neg' _
protected lemma mul_le : p (x * y) ≤ p x * p y := p.mul_le' _ _

lemma pow_le : ∀ {n : ℕ}, 0 < n → p (x ^ n) ≤ (p x) ^ n
| 1 h := by simp only [pow_one]
| (n + 2) h := 
by simpa only [pow_succ _ (n + 1)] using le_trans (p.mul_le x _)
  (mul_le_mul_of_nonneg_left (pow_le n.succ_pos) (p.nonneg _))

/-- A function `f : R → ℝ` from a ring `R` satisfies `is_norm_le_one_class` if `f 1 ≤ 1`. -/
def is_norm_le_one_class {R : Type*} [semiring R] (f : R → ℝ) : Prop := f 1 ≤ 1

/-- A function `f : R → ℝ` from a ring `R` satisfies `is_norm_one_class` if `f 1 = 1`. -/
def is_norm_one_class {R : Type*} [semiring R] (f : R → ℝ) : Prop := f 1 = 1

lemma is_norm_one_class_iff_nonzero (hp : is_norm_le_one_class p) :
  is_norm_one_class p ↔ ∃ x : R, p x ≠ 0 :=
begin
  rw is_norm_one_class,
  refine ⟨λ h, ⟨1, by {rw h, exact one_ne_zero}⟩, λ h, _⟩,
  { obtain ⟨x, hx⟩ := h,
    by_cases hp0 : p 1 = 0,
    { have hx' : p x ≤ 0,
      { rw ← mul_one x,
        apply le_trans (p.mul_le x 1) _,
        rw [hp0, mul_zero], },
      exact absurd (le_antisymm hx' (p.nonneg x) ) hx },
    { have h1 : p 1 * 1 ≤ p 1 * p 1,
      { conv_lhs { rw ← one_mul (1 : R) },
        convert p.mul_le 1 1,
        rw mul_one, },
      rw mul_le_mul_left (lt_of_le_of_ne (p.nonneg _) (ne.symm hp0)) at h1,
      exact le_antisymm hp h1, }}
end

end ring_seminorm

/-- The norm of a semi_normed_ring as a ring_seminorm. -/
def seminormed_ring.to_ring_seminorm (R : Type*) [semi_normed_ring R] :
  ring_seminorm R := 
{ to_fun    := (λ r : R, ∥r∥),
  map_zero' := norm_zero,
  nonneg'   := norm_nonneg,
  add_le'   := norm_add_le,
  neg'      := norm_neg,
  mul_le'   := norm_mul_le }

/-- A function `f : R → ℝ` is a norm if it is a seminorm and `f x = 0` implies `x = 0`. -/
structure ring_norm (R : Type*) [ring R] extends (ring_seminorm R) :=
(ne_zero : ∀ x, x ≠ 0 → 0 < to_fun x)

attribute [nolint doc_blame] ring_norm.to_ring_seminorm

namespace ring_norm

variable [ring R]

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : has_coe_to_fun (ring_norm R) (λ _, R → ℝ) := ⟨λ p, p.to_fun⟩

@[ext] lemma ext {p q : ring_norm R} (h : ∀ x, p x = q x) : p = q :=
by { cases p, cases q, simp only, ext, exact h x }

variable (R)

/-- The trivial norm on a ring `R` is the `ring_norm` taking value `0` at `0` and `1` at every
  other element. -/
def trivial_norm [decidable_eq R] : ring_norm R :=
{ to_fun    := λ x, if x = 0 then 0 else 1,
  map_zero' := by simp only [eq_self_iff_true, if_true],
  nonneg'   := λ x, begin split_ifs, exacts [le_refl _, zero_le_one] end,
  add_le'   := λ x y, 
  begin
    by_cases hx : x = 0,
    { rw [if_pos hx, hx, zero_add, zero_add], },
    { rw if_neg hx, apply le_add_of_le_of_nonneg,
      { split_ifs, exacts [zero_le_one, le_refl _] },
      { split_ifs, exacts [le_refl _, zero_le_one] }}
  end,
  neg'      := λ x, by simp_rw neg_eq_zero,
  mul_le'   := λ x y, 
  begin by_cases h : x * y = 0,
    { rw if_pos h, apply mul_nonneg;
      {split_ifs, exacts [le_refl _, zero_le_one]}},
    { rw [if_neg h, if_neg (left_ne_zero_of_mul h), if_neg (right_ne_zero_of_mul h), mul_one] }
  end,
  ne_zero   := λ x hx, by { rw if_neg hx, exact zero_lt_one }}

instance [decidable_eq R] : inhabited (ring_norm R) := ⟨trivial_norm R⟩

/-- A nonzero ring seminorm on a field `K` is a ring norm. -/
def of_ring_seminorm {K : Type*} [field K] (f : ring_seminorm K)
  (hnt : ∃ r : K, 0 ≠ f r) : ring_norm K :=
{ ne_zero := λ x hx, begin
    obtain ⟨c, hc⟩ := hnt,
    have hfx : 0 ≠ f x,
    { intro h0,
      have hc' : f c ≤ 0,
      { rw [← mul_one c, ← mul_inv_cancel hx, ← mul_assoc, mul_comm c, mul_assoc],
        refine le_trans (f.mul_le x _) _,
        rw [← h0, zero_mul] },
      exact hc (ge_antisymm hc' (f.nonneg _)), },
    exact lt_of_le_of_ne (f.nonneg _) hfx,
  end,
  ..f }

end ring_norm

/-- The norm of a normed_ring as a ring_norm. -/
def normed_ring.to_ring_norm (R : Type*) [normed_ring R] : ring_norm R :=
{ ne_zero := λ x, norm_pos_iff.mpr,
  ..seminormed_ring.to_ring_seminorm R}


#lint

/-- Given a ring `R` with a norm `f` and an `R`-algebra `A`, a function `g : A → ℝ` is an algebra
  norm if it is a norm on `A` and `g ((algebra_map R A r) * a) = f r * g a`. -/
structure algebra_norm (R : Type*) [comm_ring R] (f : ring_norm R)
  (A : Type*) [ring A] [algebra R A] extends (ring_norm A) :=
(smul : ∀ (r : R) (a : A) , to_fun ((algebra_map R A r) * a) = f r * to_fun a)

namespace algebra_norm

variables [comm_ring R] (A : Type*) [ring A] [algebra R A] (f : ring_norm R)

instance : has_coe_to_fun (algebra_norm R f A) (λ _, A → ℝ) := ⟨λ p, p.to_fun⟩

instance [decidable_eq R] : 
  inhabited (algebra_norm R (ring_norm.trivial_norm R) R) := ⟨ {
  smul := λ r s, 
  begin 
    simp only [ring_norm.trivial_norm, algebra.id.map_eq_id, ring_hom.id_apply],
    by_cases hr : r = 0,
    { rw [hr, zero_mul, if_pos (eq.refl _), mul_ite, mul_zero, mul_one],
      split_ifs, refl, sorry },
    { sorry}
  end
  ..(ring_norm.trivial_norm R) }⟩

/- instance [decidable_eq R] [decidable_eq A] : 
  inhabited (algebra_norm R (ring_norm.trivial_norm R) A) := ⟨ {
  smul := λ r a, 
  begin
    simp only [ring_norm.trivial_norm],
    by_cases ha : a = 0,
    { rw [if_pos ha, ha, mul_zero, mul_zero, if_pos (eq.refl _)] },
    { simp only [if_neg ha, mul_one],  }
  end,
  ..ring_norm.trivial_norm A }⟩ -/

end algebra_norm

variables [ring R]

/-- A function `f : R → ℝ≥0` is nonarchimedean if it satisfies the inequality
  `f (r + s) ≤ max (f r) (f s)`. -/
def is_nonarchimedean (f : R → ℝ) : Prop := ∀ r s, f (r + s) ≤ max (f r) (f s)

/-- A function `f : R → ℝ` is power-multiplicative if for all `r ∈ R` and all positive `n ∈ ℕ`,
  `f (r ^ n) = (f r) ^ n`. -/
def is_pow_mul {R : Type*} [ring R] (f : R → ℝ) :=
∀ (r : R) {n : ℕ} (hn : 1 ≤ n), f (r ^ n) = (f r) ^ n


