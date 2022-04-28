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
{ zero   := seminorm_from_bounded_zero f_zero,
  mul    := seminorm_from_bounded_mul f_mul,
  one    := seminorm_from_bounded_one f_mul }

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

lemma smoothing_seminorm_seq_has_limit :
  ∃ r : nnreal, filter.tendsto (smoothing_seminorm_seq hsn x) filter.at_top (𝓝 r) := sorry

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
  smoothing_seminorm hsn (x * y) ≤ smoothing_seminorm hsn x * smoothing_seminorm hsn y := sorry

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
  is_nonarchimedean (smoothing_seminorm hsn) := sorry

lemma smoothing_seminorm_is_pow_mult : is_pow_mult (smoothing_seminorm hsn) :=
sorry

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

lemma smoothing_seminorm_of_mult (hx : ∀ (y : α), f (x *y) = f x * f y) (y : α) :
  smoothing_seminorm hsn (x * y) = smoothing_seminorm hsn x * smoothing_seminorm hsn x :=
begin
  sorry
end

end smoothing_seminorm
