/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import ring_seminorm
import analysis.special_functions.pow

noncomputable theory

open_locale topological_space nnreal

def normed_group_hom.normed_group_hom_inv_of_bijective_bounded {V : Type*} {W : Type*}
  [seminormed_add_comm_group V] [seminormed_add_comm_group W] (f : normed_add_group_hom V W)
  (h_bij : function.bijective f) (h_bdd : ∃ (C : ℝ), ∀ v, ‖v‖ ≤ C * ‖f v‖) :
  normed_add_group_hom W V := 
{ to_fun   := function.inv_fun f,
  map_add' := (add_monoid_hom.inverse f.to_add_monoid_hom (function.inv_fun f)
    (function.left_inverse_inv_fun h_bij.injective)
    (function.right_inverse_inv_fun h_bij.surjective)).map_add,
  bound'   := begin
    obtain ⟨C, hC⟩ := h_bdd,
    use C,
    intro w,
    set v := function.inv_fun f w with hv,
    rw ← function.right_inverse_inv_fun h_bij.surjective w,
    exact hC v,
  end}

-- TODO : find new name
lemma normed_group_hom.continuous_inv_of_bijective_bounded {V : Type*} {W : Type*}
  [seminormed_add_comm_group V] [seminormed_add_comm_group W] {f : normed_add_group_hom V W}
  (h_bij : function.bijective f) (h_bdd : ∃ (C : ℝ), ∀ v, ‖v‖ ≤ C * ‖f v‖) :
  continuous (function.inv_fun f) :=
begin
  set g : normed_add_group_hom W V :=
  { to_fun := function.inv_fun f,
    map_add' := λ x y,
    begin
      rw [← (classical.some_spec (((function.bijective_iff_exists_unique _).mp h_bij) x)).1,
        ← (classical.some_spec (((function.bijective_iff_exists_unique _).mp h_bij) y)).1],
      simp only [← function.comp_app (function.inv_fun f) f, function.inv_fun_comp h_bij.injective,
        id.def, ← map_add],
    end,
    bound'   := 
    begin
      use classical.some h_bdd,
      intro w,
      rw ← (classical.some_spec (((function.bijective_iff_exists_unique _).mp h_bij) w)).1,
      simp only [← function.comp_app (function.inv_fun f) f, function.inv_fun_comp h_bij.injective,
        id.def],
      exact classical.some_spec h_bdd _,
    end } with hg,
  change continuous g,
  apply normed_add_group_hom.continuous,
end

def normed_group_hom.homeo_of_bijective_bounded {V : Type*} {W : Type*} 
  [seminormed_add_comm_group V] [seminormed_add_comm_group W] {f : normed_add_group_hom V W} 
  (h_bij : function.bijective f) (h_bdd : ∃ (C : ℝ), ∀ v, ‖v‖ ≤ C * ‖f v‖) : homeomorph V W :=
{ to_fun             := f.to_fun,
  inv_fun            := function.inv_fun f.to_fun,
  left_inv           := function.left_inverse_inv_fun h_bij.injective,
  right_inv          := function.right_inverse_inv_fun h_bij.surjective,
  continuous_to_fun  := f.continuous,
  continuous_inv_fun := normed_group_hom.continuous_inv_of_bijective_bounded h_bij h_bdd }


variables {α : Type*} [comm_ring α] (f : α → ℝ)

-- 
section seminorm_from_bounded

variable (f)

def seminorm_from_bounded' : α → ℝ :=
λ x, supr (λ (y : α), f(x*y)/f(y))

variables {f}

lemma f_one_ne_zero (f_ne_zero : ∃ (x : α), f x ≠ 0) (f_nonneg : ∀ (x : α), 0 ≤ f x)
  (f_mul : ∃ (c : ℝ) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y) : f 1 ≠ 0 :=
begin
  intro h1,
  obtain ⟨c, hc, hxy⟩ := f_mul,
  specialize hxy 1,
  simp_rw [h1, one_mul, mul_zero, zero_mul] at hxy,
  obtain ⟨z, hz⟩ := f_ne_zero,
  exact hz (le_antisymm (hxy z) (f_nonneg z)),
end

lemma f_pow_ne_zero (f_nonneg : ∀ (x : α), 0 ≤ f x) {x : α} (hx : is_unit x) (hfx : f x ≠ 0) (n : ℕ)
  (f_mul : ∃ (c : ℝ) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y) : f (x ^ n) ≠ 0 :=
begin
  have h1 : f 1 ≠ 0 := f_one_ne_zero (exists.intro x hfx) f_nonneg f_mul,
  intro hxn,
  obtain ⟨c, hc, hxy⟩ := f_mul,
  obtain ⟨u, hu⟩ := hx,
  specialize hxy (x^n) (u.inv^n),
  rw [hxn, mul_zero, zero_mul, ← mul_pow, ← hu, units.inv_eq_coe_inv, units.mul_inv,
    one_pow] at hxy,
  exact h1 (le_antisymm  hxy (f_nonneg 1)),
end

lemma seminorm_from_bounded_zero (f_zero : f 0 = 0) :
  seminorm_from_bounded' f (0 : α) = 0 :=
begin
  simp_rw [seminorm_from_bounded', zero_mul, f_zero, zero_div],
  exact csupr_const,
end

lemma seminorm_from_bounded_bdd_range (f_nonneg : ∀ (x : α), 0 ≤ f x)
  (f_mul : ∃ (c : ℝ) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y) (x : α) :
  bdd_above (set.range (λ y, f (x * y) / f y)) :=
begin
  obtain ⟨c, hc_pos, hxy⟩ := f_mul,
  use c * f x,
  rw mem_upper_bounds,
  rintros r ⟨y, hy⟩,
  simp only [← hy],
  by_cases hy0 : f y = 0,
  { rw [← hy0.symm, div_zero],
    apply mul_nonneg (le_of_lt hc_pos) (f_nonneg x), },
  { simpa [div_le_iff (lt_of_le_of_ne (f_nonneg y) (ne.symm hy0))] using hxy x y, }, 
end

lemma seminorm_from_bounded_le (f_nonneg : ∀ (x : α), 0 ≤ f x)
  (f_mul : ∃ (c : ℝ) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y) (x : α) :
  seminorm_from_bounded' f x ≤ (classical.some f_mul) * f x :=
begin
  have h := classical.some_spec(classical.some_spec f_mul),
  apply csupr_le,
  intro y, by_cases hy : 0 = f y,
  { rw [← hy, div_zero],
    exact mul_nonneg (le_of_lt (classical.some (classical.some_spec f_mul))) (f_nonneg _), },
  { rw div_le_iff (lt_of_le_of_ne (f_nonneg _) hy),
    exact (classical.some_spec (classical.some_spec f_mul)) x y  }
end

lemma seminorm_from_bounded_ge (f_nonneg : ∀ (x : α), 0 ≤ f x)
  (f_mul : ∃ (c : ℝ) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y) (x : α):
  f x ≤ f 1 * seminorm_from_bounded' f x :=
begin
  by_cases h1 : f 1 = 0,
  { obtain ⟨c, hc_pos, hxy⟩ := f_mul,
    specialize hxy x 1,
    rw [mul_one, h1, mul_zero] at hxy,
    have hx0 : f x = 0 := le_antisymm hxy (f_nonneg _),
    rw [hx0, h1, zero_mul] },
  { rw [mul_comm,  ← div_le_iff (lt_of_le_of_ne' (f_nonneg _) h1)],
    have h_bdd : bdd_above (set.range (λ y, f (x * y) / f y)),
    { exact seminorm_from_bounded_bdd_range f_nonneg f_mul x},
    convert le_csupr h_bdd (1 : α),
    rw mul_one,  } ,
end

lemma seminorm_from_bounded_nonneg (f_nonneg : ∀ (x : α), 0 ≤ f x)
  (f_mul : ∃ (c : ℝ) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y) (x : α) :
  0 ≤ seminorm_from_bounded' f x :=
le_cSup_of_le (seminorm_from_bounded_bdd_range f_nonneg f_mul x) ⟨1, rfl⟩ 
  (div_nonneg (f_nonneg _) (f_nonneg _))

lemma f_mul_zero_of_f_zero (f_nonneg : ∀ (x : α), 0 ≤ f x)
  (f_mul : ∃ (c : ℝ) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y)
  {x : α} (hx : f x = 0) (y : α) : f (x * y) = 0 :=
begin
  obtain ⟨c, hc, hxy⟩ := f_mul,
  specialize hxy x y,
  rw [hx, mul_zero, zero_mul] at hxy,
  exact le_antisymm hxy (f_nonneg _),
end

lemma seminorm_from_bounded_eq_zero_iff (f_nonneg : ∀ (x : α), 0 ≤ f x)
(f_mul : ∃ (c : ℝ) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y) (x : α) :
  seminorm_from_bounded' f x = 0 ↔ f x = 0 := 
begin
  refine ⟨λ h, _, λ h, _⟩,
  { have hf := seminorm_from_bounded_ge f_nonneg f_mul x,
    rw [h, mul_zero] at hf,
    exact le_antisymm hf (f_nonneg _) },
  { have hf : seminorm_from_bounded' f x ≤ classical.some f_mul * f x := 
    seminorm_from_bounded_le f_nonneg f_mul x,
    rw [h, mul_zero] at hf,
    exact le_antisymm hf (seminorm_from_bounded_nonneg f_nonneg f_mul x), }
end

lemma seminorm_from_bounded_neg (f_neg : ∀ (x : α), f (-x) = f x) (x : α) :
  seminorm_from_bounded' f (-x) = seminorm_from_bounded' f x := 
begin
  simp only [seminorm_from_bounded'],
  congr, ext y,
  rw [neg_mul, f_neg],
end

lemma seminorm_from_bounded_mul (f_nonneg : ∀ (x : α), 0 ≤ f x) 
  (f_mul : ∃ (c : ℝ) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y) (x y : α) : 
  seminorm_from_bounded' f (x * y) ≤ seminorm_from_bounded' f x * seminorm_from_bounded' f y :=
begin
  apply csupr_le,
  by_cases hy : seminorm_from_bounded' f y = 0,
  { rw seminorm_from_bounded_eq_zero_iff f_nonneg f_mul at hy,
    intro z,
    have hz : f (y * (x * z)) = 0 := f_mul_zero_of_f_zero f_nonneg f_mul hy (x*z),
    rw [mul_comm x y, mul_assoc, hz, zero_div],
    exact mul_nonneg (seminorm_from_bounded_nonneg f_nonneg f_mul x)
      (seminorm_from_bounded_nonneg f_nonneg f_mul y),  },
  { intro z, 
    rw ← div_le_iff (lt_of_le_of_ne' (seminorm_from_bounded_nonneg f_nonneg f_mul _) hy),
    apply le_csupr_of_le (seminorm_from_bounded_bdd_range f_nonneg f_mul x) z,
    rw [div_le_iff (lt_of_le_of_ne' (seminorm_from_bounded_nonneg f_nonneg f_mul _) hy),
      div_mul_eq_mul_div],
    by_cases hz : f z = 0,
    { have hxyz : f (z * (x * y)) = 0 := f_mul_zero_of_f_zero f_nonneg f_mul hz _,
      simp_rw [mul_comm, hxyz, zero_div],
      exact div_nonneg (mul_nonneg (seminorm_from_bounded_nonneg f_nonneg f_mul y) (f_nonneg _))
        (f_nonneg _), },
    { rw [div_le_div_right (lt_of_le_of_ne' (f_nonneg _) hz), mul_comm (f (x * z))],
      by_cases hxz : f (x * z) = 0,
      { have hxyz : f (x * z * y) = 0 := f_mul_zero_of_f_zero f_nonneg f_mul hxz y,
        rw [mul_comm x y, mul_assoc, mul_comm y, hxyz],
        exact mul_nonneg (seminorm_from_bounded_nonneg f_nonneg f_mul y) (f_nonneg _) },
      { rw ← div_le_iff (lt_of_le_of_ne' (f_nonneg _) hxz),
        apply le_csupr_of_le (seminorm_from_bounded_bdd_range f_nonneg f_mul y) (x * z),
        rw [div_le_div_right (lt_of_le_of_ne' (f_nonneg _) hxz), mul_comm x y, mul_assoc], }}},
end

lemma seminorm_from_bounded_one_eq (f_ne_zero : ∃ (x : α), f x ≠ 0) (f_nonneg : ∀ (x : α), 0 ≤ f x)
  (f_mul : ∃ (c : ℝ) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y) :
  seminorm_from_bounded' f 1 = 1 :=
begin
  simp_rw [seminorm_from_bounded', one_mul],
  have h_le : (⨆ (y : α), f y / f y) ≤ 1,
  { apply csupr_le,
    intro x, by_cases hx : f x = 0,
    { rw hx, rw div_zero, exact zero_le_one },
    { rw div_self hx }},
  have h_ge : 1 ≤ (⨆ (y : α), f y / f y),
  { rw ← div_self (f_one_ne_zero f_ne_zero f_nonneg f_mul),
    have h_bdd : bdd_above (set.range (λ y, f y / f y)),
    { use (1 : ℝ),
      rw mem_upper_bounds,
      rintros r ⟨y, hy⟩,
      simp_rw [← hy],
      by_cases hy : f y = 0,
    { rw [hy, div_zero], exact zero_le_one },
    { rw div_self hy }},
    exact le_csupr h_bdd (1 : α), },
  exact le_antisymm h_le h_ge,
end

lemma seminorm_from_bounded_is_norm_le_one_class (f_nonneg : ∀ (x : α), 0 ≤ f x)
  (f_mul : ∃ (c : ℝ) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y) :
  seminorm_from_bounded' f 1 ≤ 1 :=
begin
  by_cases f_ne_zero : ∃ (x : α), f x ≠ 0,
  { exact le_of_eq (seminorm_from_bounded_one_eq f_ne_zero f_nonneg f_mul)},
  { simp_rw [seminorm_from_bounded', one_mul],
    apply csupr_le,
    intro x, 
    push_neg at f_ne_zero,
    { rw (f_ne_zero x), rw div_zero, exact zero_le_one }}
end

lemma seminorm_from_bounded_add (f_nonneg : ∀ (x : α), 0 ≤ f x)
  (f_mul : ∃ (c : ℝ) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y)
  (f_add : ∀ a b, f (a + b) ≤ f a + f b) (x y : α) : 
  seminorm_from_bounded' f (x + y) ≤ seminorm_from_bounded' f x + seminorm_from_bounded' f y :=
begin
  apply csupr_le,
  intro z,
  suffices hf : f ((x + y) * z) / f z ≤ f (x * z) / f z + f (y * z) / f z,
  { exact le_trans hf (add_le_add
      (le_csupr_of_le (seminorm_from_bounded_bdd_range f_nonneg f_mul x) z (le_refl _))
      (le_csupr_of_le (seminorm_from_bounded_bdd_range f_nonneg f_mul y) z (le_refl _))), },
  { by_cases hz : f z = 0,
    { simp only [hz, div_zero, zero_add, le_refl, or_self], },
    { rw [div_add_div_same, div_le_div_right (lt_of_le_of_ne' (f_nonneg _) hz), add_mul],
      exact f_add _ _ }} 
end

def seminorm_from_bounded (f_zero : f 0 = 0) (f_nonneg : ∀ (x : α), 0 ≤ f x)
  (f_mul : ∃ (c : ℝ) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y)
  (f_add : ∀ a b, f (a + b) ≤ f a + f b) (f_neg : ∀ (x : α), f (-x) = f x) : ring_seminorm α :=
{ to_fun    := seminorm_from_bounded' f,
  map_zero' := seminorm_from_bounded_zero f_zero,
  add_le'   := seminorm_from_bounded_add f_nonneg f_mul f_add,
  mul_le'   := seminorm_from_bounded_mul f_nonneg f_mul,
  neg'      := seminorm_from_bounded_neg f_neg }

lemma seminorm_from_bounded_is_nonarchimedean (f_nonneg : ∀ (x : α), 0 ≤ f x)
  (f_mul : ∃ (c : ℝ) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y)
  (hna : is_nonarchimedean f) : is_nonarchimedean (seminorm_from_bounded' f) :=
begin
  intros x y,
  apply csupr_le,
  intro z,
  rw le_max_iff,
  suffices hf : f ((x + y) * z) / f z ≤ f (x * z) / f z ∨
    f ((x + y) * z) / f z ≤ f (y * z) / f z,
  cases hf with hfx hfy; [left, right],
  { exact le_csupr_of_le (seminorm_from_bounded_bdd_range f_nonneg f_mul x) z hfx },
  { exact le_csupr_of_le (seminorm_from_bounded_bdd_range f_nonneg f_mul y) z hfy },
  { by_cases hz : f z = 0,
    { simp only [hz, div_zero, le_refl, or_self], },
    { rw [div_le_div_right (lt_of_le_of_ne' (f_nonneg _) hz), div_le_div_right
        (lt_of_le_of_ne' (f_nonneg _) hz), add_mul, ← le_max_iff],
      exact hna _ _, }}, 
end

lemma seminorm_from_bounded_of_mul_apply (f_nonneg : ∀ (x : α), 0 ≤ f x)
  (f_mul : ∃ (c : ℝ) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y)  {x : α}
  (hx : ∀ (y : α), f (x * y) = f x * f y) :
  seminorm_from_bounded' f x = f x :=
begin
  simp_rw [seminorm_from_bounded', hx, ← mul_div_assoc'],
  have h_le : (⨆ (y : α), f x * (f y / f y)) ≤ f x,
  { apply csupr_le,
    intro x, by_cases hx : f x = 0,
    { rw [hx, div_zero, mul_zero], exact f_nonneg _, },
    { rw [div_self hx, mul_one] }},
  have h_ge : f x ≤ (⨆ (y : α), f x * (f y / f y)),
  { by_cases f_ne_zero : ∃ (x : α), f x ≠ 0,
    { conv_lhs { rw ← mul_one (f x) },
      rw ← div_self (f_one_ne_zero f_ne_zero f_nonneg f_mul),
      have h_bdd : bdd_above (set.range (λ y, f x * (f y / f y))),
      { use f x,
        rw mem_upper_bounds,
        rintros r ⟨y, hy⟩,
        simp_rw [← hy],
        by_cases hy0 : f y = 0,
      { rw [hy0, div_zero, mul_zero], exact f_nonneg _ },
      { rw [div_self hy0, mul_one] }},
      exact le_csupr h_bdd (1 : α), },
      { push_neg at f_ne_zero,
        simp_rw [f_ne_zero, zero_div, zero_mul, csupr_const], } },
  exact le_antisymm h_le h_ge,
end

lemma seminorm_from_bounded_of_mul_le (f_nonneg : ∀ (x : α), 0 ≤ f x) {x : α} 
  (hx : ∀ (y : α), f (x * y) ≤ f x * f y) (h_one : f 1 ≤ 1)  : seminorm_from_bounded' f x = f x :=
begin
  simp_rw [seminorm_from_bounded'],
  have h_le : (⨆ (y : α), f (x * y) / f y) ≤ f x,
  { apply csupr_le,
    intro y, by_cases hy : f y = 0,
    { rw [hy, div_zero], exact f_nonneg _, },
    {rw div_le_iff (lt_of_le_of_ne' (f_nonneg _) hy), exact hx _,  }},
  have h_ge : f x ≤ (⨆ (y : α), f (x * y) / f y),
  { have h_bdd : bdd_above (set.range (λ y, f (x * y) / f y)),
    { use (f x),
      rw mem_upper_bounds,
      rintros r ⟨y, hy⟩,
      simp only [← hy],
      by_cases hy0 : f y = 0,
      { rw [hy0, div_zero],
       exact f_nonneg _ },
      { rw [← mul_one (f x), ← div_self hy0, ← mul_div_assoc, div_le_iff 
          (lt_of_le_of_ne' (f_nonneg _) hy0), mul_div_assoc, div_self hy0, mul_one],
          exact hx y,  }},
    convert le_csupr h_bdd (1 : α),
    by_cases h0 : f x = 0,
    { rw [mul_one, h0, zero_div],},
    { have heq : f 1 = 1,
      { apply le_antisymm h_one,
        specialize hx 1, 
        rw [mul_one, le_mul_iff_one_le_right (lt_of_le_of_ne (f_nonneg _) (ne.symm h0))] at hx,
        exact hx, },
      rw [heq, mul_one, div_one], } },
  exact le_antisymm h_le h_ge,
end

lemma seminorm_from_bounded_ne_zero (f_nonneg : ∀ (x : α), 0 ≤ f x)
  (f_mul : ∃ (c : ℝ) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y) 
  (f_ne_zero : ∃ x : α, f x ≠ 0) :
  ∃ x : α, seminorm_from_bounded' f x ≠ 0 :=
begin
  obtain ⟨x, hx⟩ := f_ne_zero,
  use x,
  rw [ne.def, seminorm_from_bounded_eq_zero_iff f_nonneg f_mul x],
  exact hx,
end

lemma seminorm_from_bounded_ker (f_nonneg : ∀ (x : α), 0 ≤ f x)
(f_mul : ∃ (c : ℝ) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y) :
  (seminorm_from_bounded' f)⁻¹' {0} = f⁻¹' {0} := 
begin
  ext x,
  simp only [set.mem_preimage, set.mem_singleton_iff],
  exact seminorm_from_bounded_eq_zero_iff f_nonneg f_mul x,
end

lemma seminorm_from_bounded_is_norm_iff (f_zero : f 0 = 0) (f_nonneg : ∀ (x : α), 0 ≤ f x)
  (f_mul : ∃ (c : ℝ) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y)
  (f_add : ∀ a b, f (a + b) ≤ f a + f b) (f_neg : ∀ (x : α), f (-x) = f x) :
  (∀ (x : α), (seminorm_from_bounded f_zero f_nonneg f_mul f_add f_neg).to_fun x = 0 → x = 0) ↔ 
    f⁻¹' {0} = {0} :=
begin
  refine ⟨λ h0, _, λ h_ker, _⟩,
  { rw ← seminorm_from_bounded_ker f_nonneg f_mul,
    ext x,
    simp only [set.mem_preimage, set.mem_singleton_iff],
    exact ⟨λ h, h0 x h, λ h, by {rw h, exact seminorm_from_bounded_zero f_zero}⟩ },
  { intros x hx,
    rw [← set.mem_singleton_iff, ← h_ker, set.mem_preimage, set.mem_singleton_iff,
      ← seminorm_from_bounded_eq_zero_iff f_nonneg f_mul x],
    exact hx }
end 

def norm_from_bounded (f_zero : f 0 = 0) (f_nonneg : ∀ (x : α), 0 ≤ f x)
  (f_mul : ∃ (c : ℝ) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y)
  (f_add : ∀ a b, f (a + b) ≤ f a + f b) (f_neg : ∀ (x : α), f (-x) = f x)
  (f_ker : f⁻¹' {0} = {0}) : ring_norm α := 
{ eq_zero_of_map_eq_zero' := 
  (seminorm_from_bounded_is_norm_iff f_zero f_nonneg f_mul f_add f_neg).mpr f_ker,
  ..(seminorm_from_bounded f_zero f_nonneg f_mul f_add f_neg) }

lemma seminorm_from_bounded_of_mul_is_mul {x : α} (f_nonneg : ∀ (x : α), 0 ≤ f x)
  (f_mul : ∃ (c : ℝ) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y)
  (hx : ∀ (y : α), f (x * y) = f x * f y) (y : α) : 
  seminorm_from_bounded' f (x * y) = (seminorm_from_bounded' f x) * (seminorm_from_bounded' f y) :=
begin
  rw [seminorm_from_bounded_of_mul_apply f_nonneg f_mul hx],
  simp only [seminorm_from_bounded', mul_assoc, hx, mul_div_assoc, 
    real.mul_supr_of_nonneg (f_nonneg _)],
end

end seminorm_from_bounded