import filter
import seminormed_rings
import analysis.special_functions.pow
import csupr

noncomputable theory

open_locale topological_space

def normed_group_hom.normed_group_hom_inv_of_bijective_bounded {V : Type*} {W : Type*}
  [semi_normed_group V] [semi_normed_group W] (f : normed_group_hom V W)
  (h_bij : function.bijective f) (h_bdd : ∃ (C : ℝ), ∀ v, ∥v∥ ≤ C * ∥f v∥) :
  normed_group_hom W V := 
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

lemma normed_group_hom.continuous_inv_of_bijective_bounded {V : Type*} {W : Type*}
  [semi_normed_group V] [semi_normed_group W] {f : normed_group_hom V W}
  (h_bij : function.bijective f) (h_bdd : ∃ (C : ℝ), ∀ v, ∥v∥ ≤ C * ∥f v∥) :
  continuous (function.inv_fun f) :=
normed_group_hom.continuous (f.normed_group_hom_inv_of_bijective_bounded h_bij h_bdd)

def normed_group_hom.homeo_of_bijective_bounded {V : Type*} {W : Type*} [semi_normed_group V]
  [semi_normed_group W] {f : normed_group_hom V W} (h_bij : function.bijective f) 
  (h_bdd : ∃ (C : ℝ), ∀ v, ∥v∥ ≤ C * ∥f v∥) : homeomorph V W :=
{ to_fun             := f.to_fun,
  inv_fun            := function.inv_fun f.to_fun,
  left_inv           := function.left_inverse_inv_fun h_bij.injective,
  right_inv          := function.right_inverse_inv_fun h_bij.surjective,
  continuous_to_fun  := f.continuous,
  continuous_inv_fun := normed_group_hom.continuous_inv_of_bijective_bounded h_bij h_bdd }

variables {α : Type*} [comm_ring α] (f : α → nnreal)

section seminorm_from_bounded

variable (f)

def seminorm_from_bounded : α → nnreal :=
λ x, supr (λ (y : α), f(x*y)/f(y))

variables {f}

lemma nat.one_div_cast_pos {n : ℕ} (hn : 0 < n) : 0 < 1/(n : ℝ) := 
begin
  rw [one_div, inv_pos, nat.cast_pos],
  exact lt_of_lt_of_le zero_lt_one hn,  
end

lemma nat.one_div_cast_nonneg (n : ℕ): 0 ≤ 1/(n : ℝ) := 
begin
  by_cases hn : n = 0,
  { rw [hn, nat.cast_zero, div_zero] },
  { refine le_of_lt (nat.one_div_cast_pos (zero_lt_iff.mpr hn)), }
end

lemma nat.one_div_cast_ne_zero {n : ℕ} (hn : 0 < n) : 1/(n : ℝ) ≠ 0 := 
ne_of_gt (nat.one_div_cast_pos hn)


lemma f_one_ne_zero (f_ne_zero : ∃ (x : α), f x ≠ 0)
  (f_mul : ∃ (c : nnreal) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y) : f 1 ≠ 0 :=
begin
  intro h1,
  obtain ⟨c, hc, hxy⟩ := f_mul,
  specialize hxy 1,
  simp_rw [h1, one_mul, mul_zero, zero_mul] at hxy,
  obtain ⟨z, hz⟩ := f_ne_zero,
  exact hz (le_antisymm (hxy z) (zero_le (f z))),
end

lemma f_pow_ne_zero {x : α} (hx : is_unit x) (hfx : f x ≠ 0) (n : ℕ)
  (f_mul : ∃ (c : nnreal) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y) : f (x ^ n) ≠ 0 :=
begin
  have h1 : f 1 ≠ 0 := f_one_ne_zero (exists.intro x hfx) f_mul,
  intro hxn,
  obtain ⟨c, hc, hxy⟩ := f_mul,
  obtain ⟨u, hu⟩ := hx,
  specialize hxy (x^n) (u.inv^n),
  rw [hxn, mul_zero, zero_mul, ← mul_pow, ← hu, units.inv_eq_coe_inv, units.mul_inv, one_pow,
    le_zero_iff] at hxy,
  exact h1 hxy,
end

lemma seminorm_from_bounded_zero (f_zero : f 0 = 0) :
  seminorm_from_bounded f (0 : α) = 0 :=
begin
  simp_rw [seminorm_from_bounded, zero_mul, f_zero, zero_div],
  exact csupr_const,
end

lemma seminorm_from_bounded_bdd_range (x : α)
  (f_mul : ∃ (c : nnreal) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y) :
  bdd_above (set.range (λ y, f (x * y) / f y)) :=
begin
  obtain ⟨c, hc_pos, hxy⟩ := f_mul,
  use c * f x,
  rw mem_upper_bounds,
  rintros r ⟨y, hy⟩,
  simp only [← hy],
  by_cases hy0 : 0 = f y,
  { rw [← hy0, div_zero],
    exact mul_nonneg (le_of_lt hc_pos) (zero_le _), },
  { simpa [div_le_iff₀ (ne.symm hy0)] using hxy x y, }, 
end

lemma seminorm_from_bounded_le (x : α) 
  (f_mul : ∃ (c : nnreal) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y) :
  seminorm_from_bounded f x ≤ (classical.some f_mul) * f x :=
begin
  have h := classical.some_spec(classical.some_spec f_mul),
  apply csupr_le,
  intro y, by_cases hy : 0 = f y,
  { rw [← hy, div_zero],
    exact mul_nonneg (le_of_lt (classical.some (classical.some_spec f_mul))) (zero_le _), },
  { rw div_le_iff₀ (ne.symm hy),
    exact (classical.some_spec (classical.some_spec f_mul)) x y }
end

lemma seminorm_from_bounded_ge (x : α)
  (f_mul : ∃ (c : nnreal) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y) :
  f x ≤ f 1 * seminorm_from_bounded f x :=
begin
  by_cases h1 : 0 = f 1,
  { obtain ⟨c, hc_pos, hxy⟩ := f_mul,
    specialize hxy x 1,
    rw [mul_one, ← h1, mul_zero] at hxy,
    have hx0 : f x = 0 := le_antisymm hxy (zero_le _),
    rw [hx0, ← h1, zero_mul] },
  { rw [mul_comm,  ← div_le_iff₀ (ne.symm h1)],
    have h_bdd : bdd_above (set.range (λ y, f (x * y) / f y)),
    { exact seminorm_from_bounded_bdd_range x f_mul},
    convert le_csupr h_bdd (1 : α),
    rw mul_one, } ,
end

lemma f_mul_zero_of_f_zero (f_mul : ∃ (c : nnreal) (hc : 0 < c), ∀ (x y : α),
  f (x * y) ≤ c * f x * f y) {x : α} (hx : f x = 0) (y : α) : f (x * y) = 0 :=
begin
  obtain ⟨c, hc, hxy⟩ := f_mul,
  specialize hxy x y,
  rw [hx, mul_zero, zero_mul] at hxy,
  exact le_antisymm hxy (zero_le _),
end

lemma seminorm_from_bounded_eq_zero_iff (x : α)  
(f_mul : ∃ (c : nnreal) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y) :
  seminorm_from_bounded f x = 0 ↔ f x = 0 := 
begin
  refine ⟨λ h, _, λ h, _⟩,
  { have hf := seminorm_from_bounded_ge x f_mul,
    rw [h, mul_zero] at hf,
    exact le_antisymm hf (zero_le _)},
  { have hf : seminorm_from_bounded f x ≤ classical.some f_mul * f x := 
    seminorm_from_bounded_le x f_mul,
    rw [h, mul_zero] at hf,
    exact le_zero_iff.mp hf, }
end

lemma seminorm_from_bounded_mul (f_mul : ∃ (c : nnreal) (hc : 0 < c), ∀ (x y : α),
  f (x * y) ≤ c * f x * f y) (x y : α) : seminorm_from_bounded f (x * y) ≤
  seminorm_from_bounded f x * seminorm_from_bounded f y :=
begin
  apply csupr_le,
  by_cases hy : seminorm_from_bounded f y = 0,
  { rw seminorm_from_bounded_eq_zero_iff _ f_mul at hy,
    intro z,
    simp_rw [mul_comm x y, mul_assoc, f_mul_zero_of_f_zero f_mul hy _, zero_div],
    exact zero_le _, },
  { intro z,
    rw ← div_le_iff₀ hy,
    apply le_csupr_of_le (seminorm_from_bounded_bdd_range x f_mul) z,
    rw [div_le_iff₀ hy, div_mul_eq_mul_div],
    by_cases hz : f z = 0,
    { simp_rw [mul_comm, f_mul_zero_of_f_zero f_mul hz _, zero_div],
      exact zero_le _, },
    { rw [div_le_div_right₀ hz, mul_comm (f (x * z))],
      by_cases hxz : f (x * z) = 0,
      { simp_rw [mul_comm x y, mul_assoc, mul_comm y, f_mul_zero_of_f_zero f_mul hxz _],
        exact zero_le _, },
      { rw ← div_le_iff₀ hxz,
        apply le_csupr_of_le (seminorm_from_bounded_bdd_range y f_mul) (x * z),
        rw [div_le_div_right₀ hxz, mul_comm x y, mul_assoc], }}},
end

lemma seminorm_from_bounded_one_eq (f_ne_zero : ∃ (x : α),
  f x ≠ 0) (f_mul : ∃ (c : nnreal) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y) :
  seminorm_from_bounded f 1 = 1 :=
begin
  simp_rw [seminorm_from_bounded, one_mul],
  have h_le : (⨆ (y : α), f y / f y) ≤ 1,
  { apply csupr_le,
    intro x, by_cases hx : f x = 0,
    { rw hx, rw div_zero, exact zero_le_one },
    { rw div_self hx }},
  have h_ge : 1 ≤ (⨆ (y : α), f y / f y),
  { rw ← div_self (f_one_ne_zero f_ne_zero f_mul),
    have h_bdd : bdd_above (set.range (λ y, f y / f y)),
    { use (1 : nnreal),
      rw mem_upper_bounds,
      rintros r ⟨y, hy⟩,
      simp_rw [← hy],
      by_cases hy : f y = 0,
    { rw [hy, div_zero], exact zero_le_one },
    { rw div_self hy }},
    exact le_csupr h_bdd (1 : α), },
  exact le_antisymm h_le h_ge,
end

lemma seminorm_from_bounded_one 
  (f_mul : ∃ (c : nnreal) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y) :
  seminorm_from_bounded f 1 ≤ 1 :=
begin
  by_cases f_ne_zero : ∃ (x : α), f x ≠ 0,
  { exact le_of_eq (seminorm_from_bounded_one_eq f_ne_zero f_mul)},
  { simp_rw [seminorm_from_bounded, one_mul],
    apply csupr_le,
    intro x, 
    push_neg at f_ne_zero,
    { rw (f_ne_zero x), rw div_zero, exact zero_le_one }}
end

lemma seminorm_from_bounded_is_seminorm (f_zero : f 0 = 0)
  (f_mul : ∃ (c : nnreal) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y) :
  is_seminorm (seminorm_from_bounded f) :=
{ zero := seminorm_from_bounded_zero f_zero,
  mul  := seminorm_from_bounded_mul f_mul,
  one  := seminorm_from_bounded_one f_mul }

lemma seminorm_from_bounded_is_nonarchimedean 
  (f_mul : ∃ (c : nnreal) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y)
  (hna : is_nonarchimedean f) : is_nonarchimedean (seminorm_from_bounded f) :=
begin
  intros x y,
  apply csupr_le,
  intro z,
  rw le_max_iff,
  suffices hf : f ((x + y) * z) / f z ≤ f (x * z) / f z ∨
    f ((x + y) * z) / f z ≤ f (y * z) / f z,
  cases hf with hfx hfy; [left, right],
  { exact le_csupr_of_le (seminorm_from_bounded_bdd_range x f_mul) z hfx },
  { exact le_csupr_of_le (seminorm_from_bounded_bdd_range y f_mul) z hfy },
  { by_cases hz : f z = 0,
    { simp only [hz, div_zero, le_refl, or_self], },
    { rw [div_le_div_right₀ hz, div_le_div_right₀ hz, add_mul, ← le_max_iff],
      exact hna _ _, }}
end

lemma seminorm_from_bounded_of_mul_apply 
  (f_mul : ∃ (c : nnreal) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y)  {x : α}
  (hx : ∀ (y : α), f (x * y) = f x * f y) :
  seminorm_from_bounded f x = f x :=
begin
  simp_rw [seminorm_from_bounded, hx, ← mul_div_assoc'],
  have h_le : (⨆ (y : α), f x * (f y / f y)) ≤ f x,
  { apply csupr_le,
    intro x, by_cases hx : f x = 0,
    { rw hx, rw div_zero, rw mul_zero, exact zero_le _, },
    { rw [div_self hx, mul_one] }},
  have h_ge : f x ≤ (⨆ (y : α), f x * (f y / f y)),
  { by_cases f_ne_zero : ∃ (x : α), f x ≠ 0,
    { conv_lhs { rw ← mul_one (f x) },
      rw ← div_self (f_one_ne_zero f_ne_zero f_mul),
      have h_bdd : bdd_above (set.range (λ y, f x * (f y / f y))),
      { use (f x : nnreal),
        rw mem_upper_bounds,
        rintros r ⟨y, hy⟩,
        simp_rw [← hy],
        by_cases hy0 : f y = 0,
      { rw [hy0, div_zero, mul_zero], exact zero_le _ },
      { rw [div_self hy0, mul_one] }},
      exact le_csupr h_bdd (1 : α), },
      { push_neg at f_ne_zero,
        simp_rw [f_ne_zero, zero_div, zero_mul, csupr_const], }},
  exact le_antisymm h_le h_ge,
end

lemma seminorm_from_bounded_of_mul_le {x : α}
  (hx : ∀ (y : α), f (x * y) ≤ f x * f y) (h_one : f 1 ≤ 1) : seminorm_from_bounded f x = f x :=
begin
  simp_rw [seminorm_from_bounded],
  have h_le : (⨆ (y : α), f (x * y) / f y) ≤ f x,
  { apply csupr_le,
    intro y, by_cases hy : f y = 0,
    { rw [hy, div_zero], exact zero_le _, },
    { rw div_le_iff₀ hy, exact hx _, }},
  have h_ge : f x ≤ (⨆ (y : α), f (x * y) / f y),
  { have h_bdd : bdd_above (set.range (λ y, f (x * y) / f y)),
    { use (f x),
      rw mem_upper_bounds,
      rintros r ⟨y, hy⟩,
      simp only [← hy],
      by_cases hy0 : f y = 0,
      { rw [hy0, div_zero],
        exact zero_le _  },
      { rw [← mul_one (f x), ← div_self hy0, ← mul_div_assoc, div_le_iff₀ hy0, mul_div_assoc,
          div_self hy0, mul_one],
          exact hx y, }},
    convert le_csupr h_bdd (1 : α),
    by_cases h0 : f x = 0,
    { rw [mul_one, h0, zero_div],},
    { have heq : f 1 = 1,
      { apply le_antisymm h_one,
        specialize hx 1,
        rw [mul_one, le_mul_iff_one_le_right (lt_of_le_of_ne (zero_le (f x)) (ne.symm h0))] at hx,
        exact hx, },
      rw [heq, mul_one, div_one], } },
  exact le_antisymm h_le h_ge,
end

lemma seminorm_from_bounded_ne_zero
  (f_mul : ∃ (c : nnreal) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y) 
  (f_ne_zero : ∃ x : α, f x ≠ 0) :
  ∃ x : α, seminorm_from_bounded f x ≠ 0 :=
begin
  obtain ⟨x, hx⟩ := f_ne_zero,
  use x,
  rw [ne.def, seminorm_from_bounded_eq_zero_iff x f_mul],
  exact hx,
end

lemma seminorm_from_bounded_ker 
(f_mul : ∃ (c : nnreal) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y) :
  (seminorm_from_bounded f)⁻¹' {0} = f⁻¹' {0} := 
begin
  ext x,
  simp only [set.mem_preimage, set.mem_singleton_iff],
  exact seminorm_from_bounded_eq_zero_iff x f_mul,
end

lemma seminorm_from_bounded_is_norm_iff (f_zero : f 0 = 0)
  (f_mul : ∃ (c : nnreal) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y) :
  is_norm (seminorm_from_bounded f) ↔ f⁻¹' {0} = {0} :=
begin
  refine ⟨λ h_norm, _, λ h_ker, _⟩,
  { rw ← seminorm_from_bounded_ker f_mul,
    ext x,
    simp only [set.mem_preimage, set.mem_singleton_iff],
    have h_ne_zero := h_norm.ne_zero,
    refine ⟨λ h, _, λ h, by {rw h, exact seminorm_from_bounded_zero f_zero}⟩,
    { specialize h_ne_zero x,
      contrapose! h_ne_zero,
      exact ⟨h_ne_zero, le_of_eq h⟩, }},
  { refine ⟨seminorm_from_bounded_is_seminorm f_zero f_mul, _⟩,
    intros x hx,
    apply lt_of_le_of_ne (zero_le _),
    rw [ne.def, eq_comm, seminorm_from_bounded_eq_zero_iff x f_mul],
    intro h0,
    rw [← set.mem_singleton_iff, ← set.mem_preimage, h_ker, set.mem_singleton_iff] at h0,
    exact hx h0, }
end

lemma seminorm_from_bounded_of_mul_is_mul {x : α} 
  (f_mul : ∃ (c : nnreal) (hc : 0 < c), ∀ (x y : α), f (x * y) ≤ c * f x * f y)
  (hx : ∀ (y : α), f (x * y) = f x * f y) (y : α) : 
  seminorm_from_bounded f (x * y) = (seminorm_from_bounded f x) * (seminorm_from_bounded f y) :=
begin
  rw [seminorm_from_bounded_of_mul_apply f_mul hx],
  simp only [seminorm_from_bounded, mul_assoc, hx, mul_div_assoc],
  rw nnreal.mul_csupr,
  exact seminorm_from_bounded_bdd_range _ f_mul, 
end

end seminorm_from_bounded

section smoothing_seminorm

variable {f}

def smoothing_seminorm_seq (hsn : is_seminorm f) (x : α) : ℕ → nnreal :=
λ n, (f (x ^n))^(1/n : ℝ)

variables (hsn : is_seminorm f) (x : α)

lemma pow_n_n_inv (r : nnreal) {n : ℕ} (hn : 0 < n) : (r ^ n)^(1/n : ℝ) = r :=
begin
  have hn1 : (n : ℝ) * (1/n) = 1,
  { apply mul_one_div_cancel,
    exact (nat.cast_ne_zero.mpr (nat.one_le_iff_ne_zero.mp hn)) },
  conv_rhs { rw [← nnreal.rpow_one r, ← hn1] },
  rw [nnreal.rpow_mul, nnreal.rpow_nat_cast],
end

/- exists_lt_of_cinfi_lt -/

private lemma smoothing_seminorm_seq_has_limit_m (f : α → nnreal) (x : α) {ε : nnreal} (hε : 0 < ε) : 
  ∃ (m : pnat), (f (x ^(m : ℕ)))^(1/m : ℝ) < 
    infi (λ (n : pnat), (f(x ^(n : ℕ)))^(1/(n : ℝ))) + ε/2 :=
begin
  exact exists_lt_of_cinfi_lt (lt_add_of_le_of_pos (le_refl _) (nnreal.half_pos hε)), 
end

/- private lemma smoothing_seminorm_seq_has_limit_m {x : α} {ε : nnreal} (hε : 0 < ε) : 
  ∃ (m : ℕ) (hm : 0 < m), (f (x ^m))^(1/m : ℝ) < 
    infi (λ (n : pnat), (f(x ^(n : ℕ)))^(1/(n : ℝ))) + ε/2:=
begin
  set L := infi (λ (n : pnat), (f(x ^(n : ℕ)))^(1/(n : ℝ))) with hL,
  by_contradiction h,
  push_neg at h,
  have h_bdd : bdd_below (set.range (λ (n : pnat), (f(x ^ (n : ℕ)))^(1/(n : ℝ)))),
    { use 0, rw mem_lower_bounds, intros y hy, exact zero_le _,},
  have hL_inf := is_glb_cinfi h_bdd,
  rw [is_glb, ← hL] at hL_inf,
  have hLε : L + ε/2 ∈ 
    (lower_bounds (set.range (λ (n : ℕ+), f (x ^ (n : ℕ)) ^ (1 / (n : ℝ))))),
  { rw mem_lower_bounds,
    intros r hr,
    obtain ⟨n, hn⟩ := set.mem_range.mpr hr,
    simp_rw ← hn,
    exact (h (n : ℕ) (pnat.pos _)), },
  simp only [← le_is_glb_iff hL_inf, add_le_iff_nonpos_right, le_zero_iff, div_eq_zero_iff,
    two_ne_zero, or_false] at hLε,
  exact (ne_of_gt hε) hLε,
end -/


private lemma smoothing_seminorm_seq_has_limit_aux {x : α} (L : nnreal) {ε : nnreal} (hε : 0 < ε)
  {m1 : ℕ} (hm1 : 0 < m1) (hx : f x ≠ 0) : 
  filter.tendsto (λ (n : ℕ), (L + ε)^
    (-(((n % m1 : ℕ) : ℝ)/(n : ℝ)))*((f x) ^(n % m1)) ^ (1 / (n : ℝ))) filter.at_top (𝓝 1) := 
begin
  rw ← mul_one (1 : nnreal),
  have h_exp : filter.tendsto (λ (n: ℕ), (((n % m1 : ℕ) : ℝ) * (1 / (n : ℝ))))
    filter.at_top (𝓝 0),
  { have h_ge : filter.tendsto (λ (n : ℕ), (m1 : ℝ) * (1 / (n : ℝ))) filter.at_top (𝓝 0),
    { simp_rw ← mul_div_assoc,
      exact tendsto_const_div_at_top_nhds_0_nat _, },
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_ge _ _,
    { simp only [filter.eventually_at_top, ge_iff_le],
      use 1,
      intros n hn,
      apply mul_nonneg (nat.cast_nonneg _) (nat.one_div_cast_nonneg n), },
    { simp only [filter.eventually_at_top, ge_iff_le],
      use 1,
      intros n hn,
      rw [mul_le_mul_right (nat.one_div_cast_pos hn), nat.cast_le],
      exact le_of_lt (nat.mod_lt _ hm1), }},
  apply filter.tendsto.mul,
  { have h0 : filter.tendsto (λ (t : ℕ), -(((t % m1 : ℕ) : ℝ) / (t : ℝ))) filter.at_top (𝓝 0),
    { rw ← neg_zero,
      convert filter.tendsto.neg h_exp,
      ext n,
      rw mul_one_div, },
    rw [← nnreal.rpow_zero (L + ε), ← nnreal.tendsto_coe],
    simp_rw nnreal.coe_rpow,
    apply filter.tendsto.rpow tendsto_const_nhds h0,
    left,
    rw [nnreal.coe_ne_zero, ne.def, add_eq_zero_iff],
    exact not_and_of_not_right _ (ne_of_gt hε) },
  { simp_rw [← nnreal.rpow_nat_cast, ← nnreal.rpow_mul],
    rw [← nnreal.rpow_zero (f x), ← nnreal.tendsto_coe],
    simp_rw nnreal.coe_rpow,
    exact filter.tendsto.rpow tendsto_const_nhds h_exp (or.inl (nnreal.coe_ne_zero.mpr hx)), },
end

lemma smoothing_seminorm_seq_has_limit :
  ∃ r : nnreal, filter.tendsto (smoothing_seminorm_seq hsn x) filter.at_top (𝓝 r) :=
begin
  by_cases hx : f x = 0,
  { use (0 : nnreal),
    simp only [smoothing_seminorm_seq],
    suffices h : ∀ (n : ℕ) (hn : 1 ≤ n), (f (x ^ n))^(1/(n : ℝ)) = 0,
    { exact tendsto_at_top_of_eventually_const h },
    intros n hn,
    have hfn : f (x^n) = 0,
    { have hfn_le : f (x ^ n) ≤ 0,
      { calc f (x ^ n) ≤ f x ^ n : hsn.pow_le x hn
                   ... = 0 ^ n : by rw hx
                   ... = 0 : zero_pow hn },
      exact le_antisymm hfn_le (zero_le _) },
    rw [hfn, nnreal.zero_rpow (nat.one_div_cast_ne_zero hn)], },
  { set L := infi (λ (n : pnat), (f(x ^(n : ℕ)))^(1/(n : ℝ))) with hL,
    use L,
    have h_bdd : bdd_below (set.range (λ (n : pnat), (f(x ^ (n : ℕ)))^(1/(n : ℝ)))),
    { use 0, rw mem_lower_bounds, intros y hy, exact zero_le _,},
    rw metric.tendsto_at_top,
    intros ε hε,
    have hLε : 0 < L + ⟨ε, (le_of_lt hε)⟩,
        { exact add_pos_of_nonneg_of_pos (zero_le _) hε },
    have hm1 : ∃ (m : ℕ) (hm : 0 < m), (f (x^m))^(1/m : ℝ) < L + (⟨ε, (le_of_lt hε)⟩/2),
    { have : (0 : nnreal) < ⟨ε, (le_of_lt hε)⟩ := hε,
      obtain ⟨m, hm⟩ := smoothing_seminorm_seq_has_limit_m f x this,
      use [m, pnat.pos m],
      convert hm,
        },
    obtain ⟨m1, hm10, hm1⟩ := hm1,
    have hm2 : ∃ m : ℕ, ∀ (n ≥ m), (L + ⟨ε, (le_of_lt hε)⟩/2)^
      (-(((n % m1 : ℕ) : ℝ)/(n : ℝ)))*((f x) ^(n % m1)) ^ (1 / (n : ℝ)) - 1 ≤
      ⟨ε, (le_of_lt hε)⟩/(2 * (L + ⟨ε, (le_of_lt hε)⟩/2)),
    { have hε2 : (0 : nnreal) < ⟨ε, (le_of_lt hε)⟩/2 := nnreal.half_pos hε,
      have hL2  := smoothing_seminorm_seq_has_limit_aux L hε2 hm10 hx,
      rw metric.tendsto_at_top at hL2,
      set δ : nnreal := ⟨ε, (le_of_lt hε)⟩/(2 * (L + ⟨ε, (le_of_lt hε)⟩/2)) with hδ_def,
      have hδ : 0 < δ,
      { rw [hδ_def, div_mul_eq_div_mul_one_div],
        apply mul_pos hε2,
        rw [one_div, nnreal.inv_pos],
        exact add_pos_of_nonneg_of_pos (zero_le L) hε2, },
      obtain ⟨N, hN⟩ := hL2 δ hδ,
      use N,
      intros n hn,
      specialize hN n hn,
      rw [nnreal.dist_eq, abs_lt] at hN,
      rw [← nnreal.coe_le_coe, nnreal.coe_sub_def],
      exact max_le (le_of_lt hN.right) (nnreal.coe_nonneg _), },
    obtain ⟨m2, hm2⟩ := hm2,
    let N := max m1 m2,
    use N,
    intros n hn,
    have hn0 : 0 < n := lt_of_lt_of_le (lt_of_lt_of_le hm10 (le_max_left m1 m2)) hn,
    rw [nnreal.dist_eq, abs_lt],
    have hL_le : L ≤ smoothing_seminorm_seq hsn x n,
    { simp only [smoothing_seminorm_seq],
      rw ← pnat.mk_coe n hn0,
      apply cinfi_le h_bdd,  },
    refine ⟨lt_of_lt_of_le (neg_lt_zero.mpr hε) _, _⟩,
    { rw ← nnreal.coe_sub hL_le,
        simp only [nnreal.zero_le_coe], },
    { suffices h : smoothing_seminorm_seq hsn x n < L + ⟨ε, (le_of_lt hε)⟩, 
      { rw [← nnreal.coe_sub hL_le, ← subtype.coe_mk ε (le_of_lt hε), nnreal.coe_lt_coe,
          tsub_lt_iff_left hL_le],
        exact h, },
      by_cases hxn : f (x ^(n % m1)) = 0,
      { simp only [smoothing_seminorm_seq],
        nth_rewrite 0 ← nat.div_add_mod n m1,
        
        apply lt_of_le_of_lt _ hLε,
        rw [pow_add, ← mul_zero ((f (x ^ (m1 * (n / m1)))) ^ (1/(n : ℝ))), 
          ← nnreal.zero_rpow (nat.one_div_cast_ne_zero hn0), ← hxn, ← nnreal.mul_rpow],
        exact nnreal.rpow_le_rpow (hsn.mul _ _) (nat.one_div_cast_nonneg _), },
      { have hn0' : 0 ≤ 1 / (n : ℝ) := nat.one_div_cast_nonneg _,
        simp only [smoothing_seminorm_seq],
        nth_rewrite 0 ← nat.div_add_mod n m1,
        
        have h : f (x ^ (m1 * (n / m1))) ^ (1 / (n : ℝ))  ≤ (f (x ^ m1) ^ (n / m1)) ^ (1 / (n : ℝ)),
        { apply nnreal.rpow_le_rpow _ hn0',
          rw pow_mul,
          exact hsn.pow_le _ (nat.div_pos (le_trans (le_max_left m1 m2) hn) hm10), },
        
        have h1 : (f (x ^ m1) ^ (n / m1)) ^ (1 / (n : ℝ))  <
          (L + ⟨ε, (le_of_lt hε)⟩/2) * ((L + ⟨ε, (le_of_lt hε)⟩/2) ^ -(((n % m1 : ℕ) : ℝ)/(n : ℝ))),
        { have hm10' : (m1 : ℝ) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_gt hm10),
          rw ←  nnreal.rpow_nat_cast,
          rw [← nnreal.rpow_lt_rpow_iff (nat.cast_pos.mpr hm10), ← nnreal.rpow_mul,
            one_div_mul_cancel hm10', nnreal.rpow_one] at hm1,
          
          nth_rewrite 0 ← nnreal.rpow_one (L + ⟨ε, _⟩ / 2),
          rw ← nnreal.rpow_add,
          have : (n : ℝ)/n = 1 := div_self (nat.cast_ne_zero.mpr (ne_of_gt hn0)),
          nth_rewrite 1 ← this, clear this,
          rw ← neg_div,
          rw div_add_div_same,
          nth_rewrite 2 ← nat.div_add_mod n m1,
          have : 0 < ((n / m1 : ℕ) : ℝ) / (n : ℝ),
          { apply div_pos,
            { exact nat.cast_pos.mpr (nat.div_pos (le_trans (le_max_left m1 m2) hn) hm10), },
            { exact nat.cast_pos.mpr hn0}
          },
          rw [nat.cast_add, add_neg_cancel_right, nat.cast_mul, ← nnreal.rpow_mul, mul_one_div,
            mul_div_assoc, nnreal.rpow_mul],
          exact nnreal.rpow_lt_rpow hm1 this,
          { exact zero_lt_iff.mp (add_pos_of_nonneg_of_pos (zero_le _) (nnreal.half_pos hε)),},
        },

        
        have h2 : f (x ^(n % m1)) ^ (1 / (n : ℝ)) ≤ (f x ^(n % m1)) ^ (1 / (n : ℝ)),
        { by_cases hnm1 : n % m1 = 0,
          { rw hnm1, rw pow_zero, rw pow_zero,
          exact nnreal.rpow_le_rpow hsn.one hn0', },
          { exact nnreal.rpow_le_rpow (hsn.pow_le _ (nat.pos_of_ne_zero hnm1)) hn0', }},

        have h3 : (L + ⟨ε, (le_of_lt hε)⟩/2) * ((L + ⟨ε, (le_of_lt hε)⟩/2) ^ -(((n%m1 : ℕ) : ℝ)/(n : ℝ))) *
                (f x ^(n % m1)) ^ (1 / (n : ℝ)) ≤ L + ⟨ε, (le_of_lt hε)⟩,
        { have heq :  L + ⟨ε, (le_of_lt hε)⟩ = L + ⟨ε, (le_of_lt hε)⟩/2 + ⟨ε, (le_of_lt hε)⟩/2,
          { have h20 : (2 : nnreal) ≠ 0 := two_ne_zero,
            rw [add_assoc, nnreal.div_add_div_same, ← mul_two, mul_div_cancel _ h20], },
          have hL0 : L + ⟨ε, (le_of_lt hε)⟩ / 2 ≠ 0,
          { apply ne_of_gt,
            exact (add_pos_of_nonneg_of_pos (zero_le _) (nnreal.half_pos hε)), },
          rw [heq, ← tsub_le_iff_left],
          nth_rewrite 2 ← mul_one (L + ⟨ε, _⟩ / 2),
          rw [mul_assoc, ← mul_tsub, mul_comm, ← le_div_iff₀ hL0, div_div_eq_div_mul],
          refine hm2 n (le_trans (le_max_right m1 m2) hn), },


      calc f (x ^ (m1 * (n / m1) + n % m1)) ^ (1 / (n : ℝ)) = 
              f (x ^ (m1 * (n / m1)) * x ^(n % m1)) ^ (1 / (n : ℝ)) : by rw pow_add
        ... ≤ (f (x ^ (m1 * (n / m1))) * f (x ^(n % m1))) ^ (1 / (n : ℝ)) :
              nnreal.rpow_le_rpow (hsn.mul _ _) hn0'
        ... = f (x ^ (m1 * (n / m1))) ^ (1 / (n : ℝ)) * f (x ^(n % m1)) ^ (1 / (n : ℝ)) :
              nnreal.mul_rpow
        ... ≤ (f (x ^ m1) ^ (n / m1)) ^ (1 / (n : ℝ)) * f (x ^(n % m1)) ^ (1 / (n : ℝ)) : 
              mul_le_mul_right' h _
        ... < (L + ⟨ε, (le_of_lt hε)⟩/2) * ((L + ⟨ε, (le_of_lt hε)⟩/2) ^ -(((n%m1 : ℕ) : ℝ)/(n : ℝ))) *
              f (x ^(n % m1)) ^ (1 / (n : ℝ)) :
              mul_lt_mul h1 (le_refl _) (nnreal.rpow_pos (zero_lt_iff.mpr hxn)) (zero_le _)
        ... ≤ (L + ⟨ε, (le_of_lt hε)⟩/2) * ((L + ⟨ε, (le_of_lt hε)⟩/2) ^ -(((n%m1 : ℕ) : ℝ)/(n : ℝ))) *
              (f x ^(n % m1)) ^ (1 / (n : ℝ)) : mul_le_mul_left' h2 _
        ... ≤  L + ⟨ε, (le_of_lt hε)⟩ : h3, }}}
end

def smoothing_seminorm_seq_lim : nnreal :=
classical.some (smoothing_seminorm_seq_has_limit hsn x)

lemma smoothing_seminorm_seq_lim_is_limit :
  filter.tendsto ((smoothing_seminorm_seq hsn x)) filter.at_top
    (𝓝 (smoothing_seminorm_seq_lim hsn x)) :=
classical.some_spec (smoothing_seminorm_seq_has_limit hsn x)

def smoothing_seminorm : α → nnreal := λ x, smoothing_seminorm_seq_lim hsn x

lemma smoothing_seminorm_nonneg : 0 ≤ smoothing_seminorm hsn x :=
begin
  apply ge_of_tendsto (smoothing_seminorm_seq_lim_is_limit hsn x),
  simp only [filter.eventually_at_top, ge_iff_le],
  use 1,
  rintros n hn,
  simp only [smoothing_seminorm_seq],
  rw ← nnreal.coe_le_coe,
  exact real.rpow_nonneg_of_nonneg (nnreal.coe_nonneg _) _,
end

lemma smoothing_seminorm_zero : smoothing_seminorm hsn 0 = 0 :=
begin
  apply tendsto_nhds_unique_of_eventually_eq (smoothing_seminorm_seq_lim_is_limit hsn 0)
    tendsto_const_nhds,
  simp only [filter.eventually_eq, filter.eventually_at_top, ge_iff_le],
  use 1,
  intros n hn,
  simp only [smoothing_seminorm_seq],
  rw [zero_pow (nat.succ_le_iff.mp hn), hsn.zero, nnreal.zero_rpow],
  apply one_div_ne_zero,
  exact nat.cast_ne_zero.mpr (nat.one_le_iff_ne_zero.mp hn),
end

lemma smoothing_seminorm_mul (y : α) :
  smoothing_seminorm hsn (x * y) ≤ smoothing_seminorm hsn x * smoothing_seminorm hsn y :=
begin
  apply le_of_tendsto_of_tendsto' (smoothing_seminorm_seq_lim_is_limit hsn (x *y))
    (filter.tendsto.mul (smoothing_seminorm_seq_lim_is_limit hsn x)
      (smoothing_seminorm_seq_lim_is_limit hsn y)),
  intro n,
  have hn : 0 ≤ 1 / (n : ℝ),
  { simp only [one_div, inv_nonneg, nat.cast_nonneg] },
  simp only [smoothing_seminorm_seq],
  rw [← nnreal.mul_rpow, mul_pow],
  exact nnreal.rpow_le_rpow (hsn.mul _ _) hn,
end

lemma smoothing_seminorm_one : smoothing_seminorm hsn 1 ≤ 1 := 
begin
  apply le_of_tendsto (smoothing_seminorm_seq_lim_is_limit hsn (1 : α)),
  simp only [filter.eventually_at_top, ge_iff_le],
  use 1,
  rintros n hn,
  simp only [smoothing_seminorm_seq],
  rw [one_pow],
  conv_rhs{rw ← nnreal.one_rpow (1/n : ℝ)},
  have hn1 : 0 < (1/n : ℝ),
  { have h01 : (0 : ℝ) < 1 := zero_lt_one,
    apply div_pos h01,
    rw [← nat.cast_zero, nat.cast_lt],
    exact (nat.succ_le_iff.mp hn) },
  exact (nnreal.rpow_le_rpow_iff hn1).mpr hsn.one,
end

lemma smoothing_seminorm_is_seminorm : is_seminorm (smoothing_seminorm hsn) :=
{ zero   := smoothing_seminorm_zero hsn,
  mul    := smoothing_seminorm_mul hsn,
  one    := smoothing_seminorm_one hsn }

lemma smoothing_seminorm_is_nonarchimedean (hna : is_nonarchimedean f) :
  is_nonarchimedean (smoothing_seminorm hsn) :=
begin
  sorry
end


lemma smoothing_seminorm_is_pow_mult : is_pow_mult (smoothing_seminorm hsn) :=
begin
  intros x m hm,
  simp only [smoothing_seminorm],
  have hlim : filter.tendsto (λ n, smoothing_seminorm_seq hsn (x) (m*n)) filter.at_top
    (𝓝 (smoothing_seminorm_seq_lim hsn x )),
  { refine filter.tendsto.comp (smoothing_seminorm_seq_lim_is_limit hsn x) _,
    apply filter.tendsto_at_top_at_top_of_monotone,
    { intros n k hnk, exact mul_le_mul_left' hnk m, },
    { rintro n, use n, exact le_mul_of_one_le_left' hm, }},
  apply tendsto_nhds_unique _ (filter.tendsto.pow hlim m),
  have h_eq : ∀ (n : ℕ), smoothing_seminorm_seq hsn x (m * n) ^ m =
    smoothing_seminorm_seq hsn (x^m) n,
  { have hm' : (m : ℝ) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hm)), 
    intro n,
    simp only [smoothing_seminorm_seq],
    rw [pow_mul, ← nnreal.rpow_nat_cast, ← nnreal.rpow_mul, nat.cast_mul, ← one_div_mul_one_div,
      mul_comm (1 / (m : ℝ)), mul_assoc, one_div_mul_cancel hm', mul_one] },
  simp_rw h_eq,
  exact smoothing_seminorm_seq_lim_is_limit hsn _
end

lemma smoothing_seminorm_le : smoothing_seminorm hsn x ≤ f x :=
begin
  apply le_of_tendsto (smoothing_seminorm_seq_lim_is_limit hsn x),
  simp only [filter.eventually_at_top, ge_iff_le],
  use 1,
  rintros n hn,
  have hn1 : (n : ℝ) * (1/n) = 1,
  { apply mul_one_div_cancel,
    exact (nat.cast_ne_zero.mpr (nat.one_le_iff_ne_zero.mp hn)) },
  have hn' : 0 < (1/n : ℝ),
  { have h01 : (0 : ℝ) < 1 := zero_lt_one,
    apply div_pos h01,
    rw [← nat.cast_zero, nat.cast_lt],
    exact (nat.succ_le_iff.mp hn) },
  simp only [smoothing_seminorm_seq],
  rw [← nnreal.rpow_one (f x)],
  conv_rhs { rw ← hn1 },
  rw [nnreal.rpow_mul, nnreal.rpow_le_rpow_iff hn', nnreal.rpow_nat_cast],
  exact hsn.pow_le x (nat.succ_le_iff.mp hn),
end

variable {x}

lemma smoothing_seminorm_of_pow_mult (hx : ∀ (n : ℕ) (hn : 1 ≤ n), f (x ^ n) = f x ^ n) :
  smoothing_seminorm hsn x = f x :=
begin
  apply tendsto_nhds_unique_of_eventually_eq (smoothing_seminorm_seq_lim_is_limit hsn x)
    tendsto_const_nhds,
  simp only [filter.eventually_eq, filter.eventually_at_top, ge_iff_le],
  use 1,
  intros n hn,
  simp only [smoothing_seminorm_seq],
  have hn0 : (n : ℝ) ≠ 0 := nat.cast_ne_zero.mpr (nat.one_le_iff_ne_zero.mp hn),
  rw [hx n hn, ← nnreal.rpow_nat_cast, ← nnreal.rpow_mul, mul_one_div_cancel hn0,
    nnreal.rpow_one],
end


lemma f_is_mult_pow_of_is_mult (hx : ∀ y : α, f (x * y) = f x * f y) :
   ∀ (n : ℕ) (y : α), f (x ^ n * y) = f x ^ n * f y :=
begin
  { intros n,
    induction n with n hn,
    { intro y, rw [pow_zero, pow_zero, one_mul, one_mul]},
    { intro y, rw [pow_succ', pow_succ', mul_assoc, mul_assoc, ← hx y], exact hn _, }},
end

lemma smoothing_seminorm_apply_of_is_mult (hx : ∀ y : α, f (x * y) = f x * f y) :
  smoothing_seminorm hsn x = f x :=
begin
  apply tendsto_nhds_unique_of_eventually_eq (smoothing_seminorm_seq_lim_is_limit hsn x)
    tendsto_const_nhds,
  simp only [filter.eventually_eq, filter.eventually_at_top, ge_iff_le],
  use 1,
  intros n hn,
  simp only [smoothing_seminorm_seq],
  by_cases hx0 : f x = 0,
  { have hxn : f (x ^ n) = 0,
    { apply le_antisymm _ (zero_le _),
      apply le_trans (hsn.pow_le x (lt_of_lt_of_le zero_lt_one hn)),
      rw [hx0, zero_pow (lt_of_lt_of_le zero_lt_one hn)], },
    rw [hx0, hxn, nnreal.zero_rpow (nat.one_div_cast_ne_zero hn)] },
  { have h1 : f 1 = 1,
    { rw [← nnreal.mul_eq_mul_left hx0, ← hx 1, mul_one, mul_one], },
    have hn0 : (n : ℝ) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hn)),
    rw [← mul_one (x ^ n), f_is_mult_pow_of_is_mult hx, ← nnreal.rpow_nat_cast, h1, mul_one,
      ← nnreal.rpow_mul, mul_one_div_cancel hn0, nnreal.rpow_one], },
end

lemma smoothing_seminorm_of_mult (hx : ∀ (y : α), f (x * y) = f x * f y) (y : α) :
  smoothing_seminorm hsn (x * y) = smoothing_seminorm hsn x * smoothing_seminorm hsn y :=
begin
  have hlim : filter.tendsto (λ n, f x * smoothing_seminorm_seq hsn y n) filter.at_top
    (𝓝 (smoothing_seminorm hsn x * smoothing_seminorm hsn  y)),
  { rw [smoothing_seminorm_apply_of_is_mult hsn hx],
    exact filter.tendsto.const_mul _ (smoothing_seminorm_seq_lim_is_limit hsn y), },
  apply tendsto_nhds_unique_of_eventually_eq (smoothing_seminorm_seq_lim_is_limit hsn (x * y)) hlim,
  simp only [filter.eventually_eq, filter.eventually_at_top, ge_iff_le],
  use 1,
  intros n hn1,
  have hn0 : (n : ℝ) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hn1)),
  simp only [smoothing_seminorm_seq],
  rw [mul_pow, f_is_mult_pow_of_is_mult hx, nnreal.mul_rpow, ← nnreal.rpow_nat_cast,
    ← nnreal.rpow_mul, mul_one_div_cancel hn0, nnreal.rpow_one],
end

end smoothing_seminorm
