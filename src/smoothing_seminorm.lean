import filter
import ring_seminorm

import algebra.order.pointwise
import analysis.special_functions.pow

import order.filter.countable_Inter
--import csupr

noncomputable theory

/- lemma mul_le_mul_iff_nonneg_left {α : Type*} {a b c : α} [has_mul α] [has_zero α] [preorder α]
  [pos_mul_mono α] (h : b ≤ c) (a0 : 0 ≤ a):
a * b ≤ a * c ↔ b ≤ c := sorry -/


namespace filter

lemma limsup_nonneg_of_nonneg {α β : Type*} [has_zero α]
  [conditionally_complete_linear_order α] {f : filter β} [hf_ne_bot : f.ne_bot] {u : β → α}
  (hf : is_bounded_under has_le.le f u) (h :  ∀ (n : β), 0 ≤ u n ) :
  0 ≤ limsup u f := 
le_limsup_of_frequently_le (frequently_of_forall h) hf
/- 
lemma eventually_le_of_limsup_le {α γ : Type*} [conditionally_complete_lattice α]
  
--[linear_order α] [order_closed_topology α] 
  {f : filter γ} {u : γ → α} [semilattice_sup γ] [hγ : nonempty γ] {y : α} --(hv : y < x)
  (h : filter.limsup u at_top ≤ y) :
  ∀ᶠ (a : γ) in at_top, u a ≤ y := 
begin
  simp only [limsup, Limsup, eventually_map] at h,
  rw cInf_le_iff at h,
  { 
    /- simp only [eventually_at_top, ge_iff_le, mem_lower_bounds, set.mem_set_of_eq, 
      forall_exists_index] at h, -/
    /- by_contra' h',
    obtain ⟨b, hb_ge, hbu⟩ := h' hγ.some,
    specialize h (u b),
    have : u b ≤ y,
    { apply h,
      intros x n hxn,},

    exact hbu this, -/

sorry

    --apply hbu,
    --apply h,
    --intros x n hxn,
     },
  { sorry },
  { sorry },
end



lemma real.eventually_le_limsup {α : Type*}  [semilattice_sup α] [hα : nonempty α] --[countable_Inter_filter f]
  (u : α → ℝ) :
  ∀ᶠ (y : α) in filter.at_top, u y ≤ filter.limsup u filter.at_top := 
begin

  
  rw filter.eventually_at_top,
  by_contra' h,

  set a : α := hα.some with ha,

  obtain ⟨b, hba, hb⟩ := h a,

  
  
  --simp_rw [filter.limsup, filter.Limsup],
  --simp only [real.Inf_def, ge_iff_le, eventually_map, eventually_at_top],
  --simp_rw le_neg_
  /- by_contra' h,
  simp_rw real.Inf_def at h,
  squeeze_simp at h, -/
  --rw real.le_Inf_iff,
  /- simp only [ge_iff_le, eventually_map, eventually_at_top],
  by_contra' h, -/
  
  /- by_contra' h,
  simp only [not_eventually, not_le] at h, -/
  sorry
end -/

/- lemma real.limsup_mul_le {α : Type*} {f : filter α} [f.ne_bot] --[countable_Inter_filter f]
  (u v : α → ℝ) 
  (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x)
  --(h_bdd : bdd_below {a : ℝ | ∀ᶠ (n : ℝ) in map (u * v) f, n ≤ a})
  :
  filter.limsup (u * v) f ≤ filter.limsup u f * filter.limsup v f := 
begin
  calc f.limsup (u * v) ≤ f.limsup (λ x, (f.limsup u) * v x) :
  begin
    refine cInf_le_cInf _ _ _,
    { use 0,
      simp only [mem_lower_bounds, eventually_map, pi.mul_apply, set.mem_set_of_eq],
      intros x hx,
      obtain ⟨y, hy⟩ := hx.exists,
      exact le_trans (mul_nonneg (hu y) (hv y)) hy },
    { --simp only [eventually_map],
      use (limsup u f) * (limsup v f),
      simp only [eventually_map, set.mem_set_of_eq],
      have hf : ∀ᶠ (y : α) in f, v y ≤ filter.limsup v f := real.eventually_le_limsup f v,
      --obtain ⟨y, hy⟩ := hf.exists,
      --simp only [filter.eventually] at hf ⊢,
     /-  have h : {x : α | v x ≤ limsup v f} = {x : α | limsup u f * v x ≤ limsup u f * limsup v f},
      { ext x, simp only [set.mem_set_of_eq],
        rw mul_le_mul_iff_nonneg_left, },
      rw ← h,
      exact hf, -/ },
    { sorry }
  end
... = f.limsup u * f.limsup v : by sorry
end
 -/

end filter

open_locale topological_space nnreal

variables {R : Type*} [comm_ring R] (f : ring_seminorm R)  

-- Prop. 1.3.2/1 from BGR
section smoothing_seminorm

def smoothing_seminorm_seq (x : R) : ℕ → ℝ :=
λ n, (f (x ^ n))^(1/n : ℝ)

variables {f} (hf1 : f 1 ≤ 1)

lemma nnreal.pow_n_n_inv (r : nnreal) {n : ℕ} (hn : 0 < n) : (r ^ n)^(1/n : ℝ) = r :=
begin
  have hn1 : (n : ℝ) * (1/n) = 1,
  { apply mul_one_div_cancel,
    exact (nat.cast_ne_zero.mpr (nat.one_le_iff_ne_zero.mp hn)) },
  conv_rhs { rw [← nnreal.rpow_one r, ← hn1] },
  rw [nnreal.rpow_mul, nnreal.rpow_nat_cast],
end

lemma real.pow_n_n_inv {r : ℝ} (hr : 0 ≤ r) {n : ℕ} (hn : 0 < n) :
  (r ^ n)^(1/n : ℝ) = r :=
begin
  have hn1 : (n : ℝ) * (1/n) = 1,
  { apply mul_one_div_cancel,
    exact (nat.cast_ne_zero.mpr (nat.one_le_iff_ne_zero.mp hn)) },
  conv_rhs { rw [← real.rpow_one r, ← hn1] },
  rw [real.rpow_mul hr, real.rpow_nat_cast],
end

variable (f)

private lemma smoothing_seminorm_seq_has_limit_m (x : R) {ε : ℝ} (hε : 0 < ε) : 
  ∃ (m : pnat), (f (x ^(m : ℕ)))^(1/m : ℝ) < 
    infi (λ (n : pnat), (f(x ^(n : ℕ)))^(1/(n : ℝ))) + ε/2 :=
exists_lt_of_cinfi_lt (lt_add_of_le_of_pos (le_refl _) (half_pos hε))

variable {f}

lemma tendsto_bdd_div_at_top_nhds_0_nat (f : ℕ → ℝ)
 (hfb : ∃ b : ℝ, ∀ᶠ (n : ℕ) in filter.at_top, b ≤ f n)
 (hfB : ∃ B : ℝ, ∀ᶠ (n : ℕ) in filter.at_top, f n ≤ B) : 
  filter.tendsto (λ (n: ℕ), ((f n / (n : ℝ)))) filter.at_top (𝓝 0) :=
begin
  obtain ⟨b, hb⟩ := hfb,
  obtain ⟨B, hB⟩ := hfB,
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_div_at_top_nhds_0_nat b)
    (tendsto_const_div_at_top_nhds_0_nat B) _ _,
  { simp only [filter.eventually_at_top, ge_iff_le] at hb ⊢,
    obtain ⟨N, hN⟩ := hb,
    use N, intros n hn,
    exact div_le_div_of_le (nat.cast_nonneg _) (hN n hn) },
  { simp only [filter.eventually_at_top, ge_iff_le] at hB ⊢,
    obtain ⟨N, hN⟩ := hB,
    use N, intros n hn,
    exact div_le_div_of_le (nat.cast_nonneg _) (hN n hn) },
end

lemma tendsto_mod_div_at_top_nhds_0_nat {m : ℕ} (hm : 0 < m) : 
  filter.tendsto (λ (n: ℕ), (((n % m : ℕ) : ℝ) / (n : ℝ))) filter.at_top (𝓝 0) :=
begin
  apply tendsto_bdd_div_at_top_nhds_0_nat (λ (n: ℕ), ((n % m : ℕ) : ℝ)),
  { use 0,
    apply filter.eventually_of_forall,
    intros n,
    simp only [nat.cast_nonneg], },
  { use m,
    apply filter.eventually_of_forall,
    intros n, 
    simp only [nat.cast_le,le_of_lt (nat.mod_lt n hm)], }
end

private lemma smoothing_seminorm_seq_has_limit_aux {L : ℝ} (hL : 0 ≤ L) {ε : ℝ} (hε : 0 < ε)
  {m1 : ℕ} (hm1 : 0 < m1) {x : R} (hx : f x ≠ 0) : 
  filter.tendsto (λ (n : ℕ), (L + ε)^
    (-(((n % m1 : ℕ) : ℝ)/(n : ℝ)))*((f x) ^(n % m1)) ^ (1 / (n : ℝ))) filter.at_top (𝓝 1) := 
begin
  rw ← mul_one (1 : ℝ),
  have h_exp : filter.tendsto (λ (n: ℕ), (((n % m1 : ℕ) : ℝ) / (n : ℝ)))
    filter.at_top (𝓝 0) := tendsto_mod_div_at_top_nhds_0_nat hm1,
  apply filter.tendsto.mul,
  { have h0 : filter.tendsto (λ (t : ℕ), -(((t % m1 : ℕ) : ℝ) / (t : ℝ))) filter.at_top (𝓝 0),
    { rw ← neg_zero, exact filter.tendsto.neg h_exp, },
    rw [← real.rpow_zero (L + ε)],
    apply filter.tendsto.rpow tendsto_const_nhds h0,
    rw [ne.def, add_eq_zero_iff' hL (le_of_lt hε)],
    exact or.inl (not_and_of_not_right _ (ne_of_gt hε)) },
  { simp_rw [mul_one, ← real.rpow_nat_cast, ← real.rpow_mul (map_nonneg f x), ← mul_div_assoc,
      mul_one, ← real.rpow_zero (f x)],
    exact filter.tendsto.rpow tendsto_const_nhds h_exp (or.inl hx), },
end
include hf1

private lemma smoothing_seminorm_seq_bdd (x : R) : 
  bdd_below (set.range (λ (n : ℕ+), f (x ^(n : ℕ)) ^ (1 / (n : ℝ)))) := 
begin
  use 0,
  rintros y ⟨n, rfl⟩,
  exact real.rpow_nonneg_of_nonneg (map_nonneg f _) _, 
end

def smoothing_seminorm_seq_lim (x : R) : ℝ := infi (λ (n : pnat), (f(x^(n : ℕ)))^(1/(n : ℝ)))

private lemma smoothing_seminorm_seq_lim_is_limit_zero {x : R} (hx : f x = 0) :
  filter.tendsto ((smoothing_seminorm_seq f x)) filter.at_top
    (𝓝 (smoothing_seminorm_seq_lim hf1 x)) := 
begin
  have h0 : ∀ (n : ℕ) (hn : 1 ≤ n), (f (x ^ n))^(1/(n : ℝ)) = 0,
  { intros n hn,
    have hfn : f (x ^ n) = 0,
    { apply le_antisymm _ (map_nonneg f _),
      rw [← zero_pow hn, ← hx], 
      exact map_pow_le_pow _ x (nat.one_le_iff_ne_zero.mp hn) },
    rw [hfn, real.zero_rpow (nat.one_div_cast_ne_zero (nat.one_le_iff_ne_zero.mp hn))], },
  have hL0 : infi (λ (n : pnat), (f(x^(n : ℕ)))^(1/(n : ℝ))) = 0 :=
  le_antisymm (cinfi_le_of_le (smoothing_seminorm_seq_bdd hf1 x) (1 : pnat)
    (le_of_eq (h0 1 (le_refl _)))) (le_cinfi (λ n, real.rpow_nonneg_of_nonneg (map_nonneg f _) _)),
  simp only [hL0, smoothing_seminorm_seq, smoothing_seminorm_seq_lim],
  exact tendsto_at_top_of_eventually_const h0,
end

private lemma smoothing_seminorm_seq_lim_is_limit_ne_zero {x : R} (hx : f x ≠ 0) :
  filter.tendsto ((smoothing_seminorm_seq f x)) filter.at_top
    (𝓝 (smoothing_seminorm_seq_lim hf1 x)) := 
begin
  simp only [smoothing_seminorm_seq_lim],
  set L := infi (λ (n : pnat), (f(x^(n : ℕ)))^(1/(n : ℝ))) with hL,
  have hL0 : 0 ≤ L := le_cinfi (λ x, real.rpow_nonneg_of_nonneg (map_nonneg _ _) _),
  rw metric.tendsto_at_top,
  intros ε hε,
  obtain ⟨m1, hm1⟩ := smoothing_seminorm_seq_has_limit_m f x hε,
  obtain ⟨m2, hm2⟩ : ∃ m : ℕ, ∀ (n ≥ m), (L + ε/2)^
    (-(((n % m1 : ℕ) : ℝ)/(n : ℝ)))*((f x) ^(n % m1)) ^ (1 / (n : ℝ)) - 1 ≤
    ε/(2 * (L + ε/2)),
  { have hε2 : 0 < ε/2 := half_pos hε,
    have hL2  := smoothing_seminorm_seq_has_limit_aux hL0 hε2 (pnat.pos m1) hx,
    rw metric.tendsto_at_top at hL2,
    set δ : ℝ := ε/(2 * (L + ε/2)) with hδ_def,
    have hδ : 0 < δ,
    { rw [hδ_def, div_mul_eq_div_mul_one_div],
      exact mul_pos hε2 
        ((one_div (L + ε/2)).symm ▸ inv_pos_of_pos (add_pos_of_nonneg_of_pos hL0 hε2)), },
    obtain ⟨N, hN⟩ := hL2 δ hδ,
    use N,
    intros n hn,
    specialize hN n hn,
    rw [real.dist_eq, abs_lt] at hN,
    exact le_of_lt hN.right },
  use max (m1 : ℕ) m2,
  intros n hn,
  have hn0 : 0 < n := lt_of_lt_of_le (lt_of_lt_of_le (pnat.pos m1) (le_max_left m1 m2)) hn,
  rw [real.dist_eq, abs_lt],
  have hL_le : L ≤ smoothing_seminorm_seq f x n,
  { simp only [smoothing_seminorm_seq],
    rw ← pnat.mk_coe n hn0,
    apply cinfi_le (smoothing_seminorm_seq_bdd hf1 x), },
  refine ⟨lt_of_lt_of_le (neg_lt_zero.mpr hε) (sub_nonneg.mpr hL_le), _⟩,
  { suffices h : smoothing_seminorm_seq f x n < L + ε, 
    { rw tsub_lt_iff_left hL_le, exact h },
    by_cases hxn : f (x ^(n % m1)) = 0,
    { simp only [smoothing_seminorm_seq],
      nth_rewrite 0 ← nat.div_add_mod n m1,
      have hLε : 0 < L + ε := add_pos_of_nonneg_of_pos hL0 hε,
      apply lt_of_le_of_lt _ hLε,
      rw [pow_add, ← mul_zero ((f (x ^ ((m1 : ℕ) * (n / (m1 : ℕ))))) ^ (1/(n : ℝ))), 
        ← real.zero_rpow (nat.one_div_cast_ne_zero (pos_iff_ne_zero.mp hn0)), ← hxn,
          ← real.mul_rpow (map_nonneg f _) (map_nonneg f _)],
      exact real.rpow_le_rpow (map_nonneg f _) (map_mul_le_mul f _ _)
        (nat.one_div_cast_nonneg _) },
    { have hxn' : 0 < f (x ^ (n % ↑m1)) := lt_of_le_of_ne (map_nonneg _ _) (ne.symm hxn),
      simp only [smoothing_seminorm_seq],
      nth_rewrite 0 ← nat.div_add_mod n m1,
      have h : f (x ^ ((m1 : ℕ) * (n / (m1 : ℕ)))) ^ (1 / (n : ℝ))  ≤
        (f (x ^ (m1 : ℕ)) ^ (n / (m1 : ℕ))) ^ (1 / (n : ℝ)),
      { apply real.rpow_le_rpow (map_nonneg f _) _ (nat.one_div_cast_nonneg _),
        rw pow_mul,
        exact  map_pow_le_pow f (x^(m1 : ℕ)) 
          (pos_iff_ne_zero.mp (nat.div_pos (le_trans (le_max_left m1 m2) hn) (pnat.pos m1))) },
       have hL0' : 0 < L + ε / 2,
        { exact (add_pos_of_nonneg_of_pos hL0 (half_pos hε)), },
      have h1 : (f (x ^ (m1 : ℕ)) ^ (n / (m1 : ℕ))) ^ (1 / (n : ℝ))  <
        (L + ε/2) * ((L + ε/2) ^ -(((n % m1 : ℕ) : ℝ)/(n : ℝ))),
      { have hm10 : (m1 : ℝ) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_gt (pnat.pos m1)),
        rw [← real.rpow_lt_rpow_iff (real.rpow_nonneg_of_nonneg (map_nonneg f _) _) (le_of_lt hL0')
          (nat.cast_pos.mpr (pnat.pos m1)), ← real.rpow_mul (map_nonneg f _), ← coe_coe, 
          one_div_mul_cancel hm10, real.rpow_one] at hm1, 
        nth_rewrite 0 ← real.rpow_one (L + ε/2),
        have : (n : ℝ)/n = 1 := div_self (nat.cast_ne_zero.mpr (ne_of_gt hn0)),
        nth_rewrite 2 ← this, clear this,
        nth_rewrite 2 ← nat.div_add_mod n m1,
        have h_lt : 0 < ((n / m1 : ℕ) : ℝ) / (n : ℝ),
        { apply div_pos,
          { exact nat.cast_pos.mpr (nat.div_pos (le_trans (le_max_left _ _) hn) (pnat.pos m1)) },
          { exact nat.cast_pos.mpr hn0 }},
        rw [← real.rpow_nat_cast, ← real.rpow_add hL0', ← neg_div, div_add_div_same, nat.cast_add, 
          add_neg_cancel_right, nat.cast_mul, ← real.rpow_mul (map_nonneg f _), mul_one_div,
          mul_div_assoc, real.rpow_mul (le_of_lt hL0')],
        exact real.rpow_lt_rpow (map_nonneg f _) hm1 h_lt },
      have h2 : f (x ^(n % m1)) ^ (1 / (n : ℝ)) ≤ (f x ^(n % m1)) ^ (1 / (n : ℝ)),
      { by_cases hnm1 : n % m1 = 0,
        { simpa[hnm1, pow_zero] using 
            real.rpow_le_rpow (map_nonneg f _) hf1 (nat.one_div_cast_nonneg _) },
        { exact real.rpow_le_rpow (map_nonneg f _) (map_pow_le_pow f _ hnm1)
            (nat.one_div_cast_nonneg _), }},
      have h3 : (L + ε/2) * ((L + ε/2) ^
        -(((n%m1 : ℕ) : ℝ)/(n : ℝ))) * (f x ^(n % m1)) ^ (1 / (n : ℝ)) ≤ L + ε,
      { have heq :  L + ε = L + ε/2 + ε/2,
        { rw [add_assoc, add_halves']},
        have hL0' : 0 < L + ε / 2 ,
        { exact (add_pos_of_nonneg_of_pos hL0 (half_pos hε)), },
        rw [heq, ← tsub_le_iff_left],
        nth_rewrite 2 ← mul_one (L + ε / 2),
        rw [mul_assoc, ← mul_sub, mul_comm, ← le_div_iff hL0', div_div],
        exact hm2 n (le_trans (le_max_right m1 m2) hn) },
      have h4 : 0 < f (x ^ (n % ↑m1)) ^ (1 / (n : ℝ)) := real.rpow_pos_of_pos hxn' _,
      have h5 : 0 < (L + ε / 2) * (L + ε / 2) ^ -(↑(n % ↑m1) / (n : ℝ)) :=
      mul_pos hL0' (real.rpow_pos_of_pos hL0' _), 
    calc f (x ^ ((m1 : ℕ) * (n / (m1 : ℕ)) + n % m1)) ^ (1 / (n : ℝ)) = 
            f (x ^ ((m1 : ℕ) * (n /(m1 : ℕ))) * x ^(n % m1)) ^ (1 / (n : ℝ)) : by rw pow_add
      ... ≤ (f (x ^ ((m1 : ℕ) * (n / (m1 : ℕ)))) * f (x ^(n % m1))) ^ (1 / (n : ℝ)) : 
            real.rpow_le_rpow (map_nonneg f _) (map_mul_le_mul f _ _) (nat.one_div_cast_nonneg _) 
      ... = f (x ^ ((m1 : ℕ) * (n /(m1 : ℕ)))) ^ (1 / (n : ℝ)) * f (x ^(n % m1)) ^ (1 / (n : ℝ)) :
            real.mul_rpow (map_nonneg f _) (map_nonneg f _)
      ... ≤ (f (x ^ (m1 : ℕ)) ^ (n /(m1 : ℕ))) ^ (1 / (n : ℝ)) * f (x ^(n % m1)) ^ (1 / (n : ℝ)) : 
            (mul_le_mul_right h4).mpr h
      ... < (L + ε/2) * ((L + ε/2) ^
            -(((n%m1 : ℕ) : ℝ)/(n : ℝ))) * f (x ^(n % m1)) ^ (1 / (n : ℝ)) : mul_lt_mul h1 
              (le_refl _) h4 (le_of_lt h5)
      ... ≤ (L + ε/2) * ((L + ε/2) ^
            -(((n%m1 : ℕ) : ℝ)/(n : ℝ))) * (f x ^(n % m1)) ^ (1 / (n : ℝ)) : 
            (mul_le_mul_left h5).mpr h2
      ... ≤  L + ε : h3  }}
end

lemma smoothing_seminorm_seq_lim_is_limit (x : R) :
  filter.tendsto ((smoothing_seminorm_seq f x)) filter.at_top
    (𝓝 (smoothing_seminorm_seq_lim hf1 x)) :=
begin
  by_cases hx : f x = 0,
  { exact smoothing_seminorm_seq_lim_is_limit_zero hf1 hx },
  { exact smoothing_seminorm_seq_lim_is_limit_ne_zero hf1 hx }
end

def smoothing_seminorm_def : R → ℝ := smoothing_seminorm_seq_lim hf1  

lemma smoothing_seminorm_nonneg (x : R) : 0 ≤ smoothing_seminorm_def hf1 x :=
begin
  apply ge_of_tendsto (smoothing_seminorm_seq_lim_is_limit hf1 x),
  simp only [filter.eventually_at_top, ge_iff_le],
  use 1,
  rintros n hn,
  simp only [smoothing_seminorm_seq],
  exact real.rpow_nonneg_of_nonneg (map_nonneg f _) _,
end

lemma smoothing_seminorm_zero : smoothing_seminorm_def hf1 0 = 0 :=
begin
  apply tendsto_nhds_unique_of_eventually_eq (smoothing_seminorm_seq_lim_is_limit hf1 0)
    tendsto_const_nhds,
  simp only [filter.eventually_eq, filter.eventually_at_top, ge_iff_le],
  use 1,
  intros n hn,
  simp only [smoothing_seminorm_seq],
  rw [zero_pow (nat.succ_le_iff.mp hn), map_zero, real.zero_rpow],
  apply one_div_ne_zero,
  exact nat.cast_ne_zero.mpr (nat.one_le_iff_ne_zero.mp hn), 
end

lemma smoothing_seminorm_neg (f_neg : ∀ x : R, f (-x) = f x) (x : R) : 
  smoothing_seminorm_def hf1 (-x) = smoothing_seminorm_def hf1 x :=
begin
  simp only [smoothing_seminorm_def, smoothing_seminorm_seq_lim],
  congr, ext n,
  rw neg_pow,
  cases neg_one_pow_eq_or R n with hpos hneg,
  { rw [hpos, one_mul] },
  { rw [hneg, neg_one_mul, f_neg], },
end

lemma smoothing_seminorm_mul (x y : R) : smoothing_seminorm_def hf1 (x * y) ≤
  smoothing_seminorm_def hf1 x * smoothing_seminorm_def hf1 y :=
begin
  apply le_of_tendsto_of_tendsto' (smoothing_seminorm_seq_lim_is_limit hf1 (x *y))
    (filter.tendsto.mul (smoothing_seminorm_seq_lim_is_limit hf1 x)
      (smoothing_seminorm_seq_lim_is_limit hf1 y)),
  intro n,
  have hn : 0 ≤ 1 / (n : ℝ),
  { simp only [one_div, inv_nonneg, nat.cast_nonneg] },
  simp only [smoothing_seminorm_seq],
  rw [← real.mul_rpow (map_nonneg f _) (map_nonneg f _), mul_pow],
  exact real.rpow_le_rpow (map_nonneg f _) (map_mul_le_mul f _ _) hn,
end

lemma smoothing_seminorm_one : smoothing_seminorm_def hf1 1 ≤ 1 := 
begin
  apply le_of_tendsto (smoothing_seminorm_seq_lim_is_limit  hf1 (1 : R) ),
  simp only [filter.eventually_at_top, ge_iff_le],
  use 1,
  rintros n hn,
  simp only [smoothing_seminorm_seq],
  rw [one_pow],
  conv_rhs{rw ← real.one_rpow (1/n : ℝ)},
  have hn1 : 0 < (1/n : ℝ),
  { have h01 : (0 : ℝ) < 1 := zero_lt_one,
    apply div_pos h01,
    rw [← nat.cast_zero, nat.cast_lt],
    exact (nat.succ_le_iff.mp hn) },
    exact (real.rpow_le_rpow_iff (map_nonneg f _) zero_le_one hn1).mpr hf1,
end

lemma smoothing_seminorm_le (x : R) : smoothing_seminorm_def hf1 x ≤ f x :=
begin
  apply le_of_tendsto (smoothing_seminorm_seq_lim_is_limit hf1 x),
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
  rw [← real.rpow_one (f x)],
  conv_rhs { rw ← hn1 },
  rw [real.rpow_mul (map_nonneg f _), real.rpow_le_rpow_iff (map_nonneg f _)
    (real.rpow_nonneg_of_nonneg (map_nonneg f _) _) hn', real.rpow_nat_cast],
  exact map_pow_le_pow f x (nat.one_le_iff_ne_zero.mp hn),
end

section is_nonarchimedean

lemma exists_index_le (hna : is_nonarchimedean f) (x y : R) (n : pnat) : 
  ∃ (m : ℕ) (hm : m ∈ finset.range (n + 1)), 
    smoothing_seminorm_def hf1 (x + y) ≤ (f (x ^ m) * f (y ^ (n - m : ℕ)))^(1/(n : ℝ)) :=
begin
  obtain ⟨m, hm_lt, hm⟩ := is_nonarchimedean_add_pow hna n x y,
  use [m, hm_lt],
  have hn_le : smoothing_seminorm_def hf1 (x + y) ≤ f ((x + y)^(n : ℕ))^(1/n : ℝ),
  { apply cinfi_le,
    use 0, 
    rw mem_lower_bounds, 
    rintros z hz, 
    obtain ⟨m, hm⟩ := set.mem_range.mp hz,
    rw ← hm,
    exact real.rpow_nonneg_of_nonneg (map_nonneg _ _) _,},
  exact le_trans hn_le (real.rpow_le_rpow (map_nonneg f _) hm (nat.one_div_cast_nonneg (n : ℕ))), 
end

def mu {x y : R} (hn : ∀ (n : pnat), ∃ (m : ℕ) (hm : m ∈ finset.range (n + 1)), 
    smoothing_seminorm_def hf1 (x + y) ≤ (f (x ^ m) * f (y ^ (n - m : ℕ)))^(1/(n : ℝ))) :
    ℕ → ℕ := 
λ n, if h : n = 0 then 0 else (classical.some (hn (⟨n, nat.pos_of_ne_zero h⟩ : pnat)))

lemma mu_le {x y : R} (hn : ∀ (n : pnat), ∃ (m : ℕ) (hm : m ∈ finset.range (n + 1)), 
  smoothing_seminorm_def hf1 (x + y) ≤ (f (x ^ m) * f (y ^ (n - m : ℕ)))^(1/(n : ℝ))) (n : ℕ) :
  mu hf1 hn n ≤ n :=
begin
  by_cases hn0 : n = 0,
  { simp only [mu, dif_pos hn0], exact eq.ge hn0 },
  { simp only [mu, dif_neg hn0, ← nat.lt_succ_iff, ← finset.mem_range],
    exact classical.some (classical.some_spec (hn (⟨n, nat.pos_of_ne_zero hn0⟩ : pnat))), }
end

lemma mu_bdd {x y : R} (hn : ∀ (n : pnat), ∃ (m : ℕ) (hm : m ∈ finset.range (n + 1)), 
  smoothing_seminorm_def hf1 (x + y) ≤ (f (x ^ m) * f (y ^ (n - m : ℕ)))^(1/(n : ℝ))) (n : ℕ) : 
  (mu hf1 hn n : ℝ)/n ∈ set.Icc (0 : ℝ) 1 :=
begin
  refine set.mem_Icc.mpr ⟨_, _⟩,
  { exact div_nonneg (nat.cast_nonneg (mu hf1 hn n)) (nat.cast_nonneg n), },
  {by_cases hn0 : n = 0,
    { rw [hn0, nat.cast_zero, div_zero], exact zero_le_one, },
    { have hn' : 0 < (n : ℝ) := nat.cast_pos.mpr (nat.pos_of_ne_zero hn0),
      rw [div_le_one hn', nat.cast_le],
      exact mu_le _ _ _, }}
end

private lemma f_bdd_below (s : ℕ → ℕ) {x y : R}  (hn : ∀ (n : pnat), ∃ (m : ℕ)
    (hm : m ∈ finset.range (n + 1)), smoothing_seminorm_def hf1 (x + y) ≤ 
    (f (x ^ m) * f (y ^ (n - m : ℕ)))^(1/(n : ℝ))) (a : ℝ) (φ: ℕ → ℕ) :
  bdd_below {a : ℝ | ∀ᶠ (n : ℝ) in filter.map 
    (λ (n : ℕ), f x ^ (↑(s (φ n)) * (1 / (φ n : ℝ)))) filter.at_top, n ≤ a} := 
begin
  use (0 : ℝ),
  simp only [mem_lower_bounds, filter.eventually_map, filter.eventually_at_top, ge_iff_le,
    set.mem_set_of_eq, forall_exists_index],
  intros r m hm,
  exact le_trans (real.rpow_nonneg_of_nonneg (map_nonneg f _) _) (hm m (le_refl _)),
end

private lemma f_nonempty {s : ℕ → ℕ} (hs_le : ∀ n : ℕ, s n ≤ n) {x y : R} 
  (hn : ∀ (n : pnat), ∃ (m : ℕ) (hm : m ∈ finset.range (n + 1)), smoothing_seminorm_def hf1 (x + y) 
    ≤ (f (x ^ m) * f (y ^ (n - m : ℕ)))^(1/(n : ℝ))) (φ : ℕ → ℕ) :
  {a : ℝ | ∀ᶠ (n : ℝ) in filter.map
    (λ (n : ℕ), f x ^ (↑(s (φ n)) * (1 / (φ n : ℝ)))) filter.at_top, n ≤ a}.nonempty :=
begin
  by_cases hfx : f x < 1,
  { use 1,
    simp only [filter.eventually_map, filter.eventually_at_top, ge_iff_le, set.mem_set_of_eq],
    use 0,
    intros b hb,
    exact real.rpow_le_one (map_nonneg _ _) (le_of_lt hfx) 
        (mul_nonneg (nat.cast_nonneg _)  (one_div_nonneg.mpr (nat.cast_nonneg _))) },
  { use f x,
    simp only [filter.eventually_map, filter.eventually_at_top, ge_iff_le, set.mem_set_of_eq],
    use 0,
    intros b hb,
    nth_rewrite 1 ← real.rpow_one (f x),
    apply real.rpow_le_rpow_of_exponent_le (not_lt.mp hfx),
    rw [mul_one_div],
    exact div_le_one_of_le (nat.cast_le.mpr (hs_le (φ b))) (nat.cast_nonneg _) }
end

private lemma f_limsup_le_one {s : ℕ → ℕ} (hs_le : ∀ n : ℕ, s n ≤ n) {x y : R} (hn : ∀ (n : pnat), 
  ∃ (m : ℕ) (hm : m ∈ finset.range (n + 1)), smoothing_seminorm_def hf1 (x + y) ≤ 
    (f (x ^ m) * f (y ^ (n - m : ℕ)))^(1/(n : ℝ))) {φ: ℕ → ℕ}
  (hφ_lim: filter.tendsto ((λ (n : ℕ), ↑(s n) / (n : ℝ)) ∘ φ) filter.at_top (𝓝 0)) :
  filter.limsup (λ (n : ℕ), f x ^ ((s (φ n) : ℝ) * (1 / (φ n : ℝ)))) filter.at_top ≤ 1 :=
begin
  simp only [filter.limsup, filter.Limsup],
  rw cInf_le_iff,
  { intros c hc_bd,
    simp only [mem_lower_bounds, filter.eventually_map, filter.eventually_at_top, ge_iff_le, 
      set.mem_set_of_eq, forall_exists_index] at hc_bd,
    by_cases hfx : f x < 1,
    { apply hc_bd (1 : ℝ) 0,
      rintros b -,
      exact real.rpow_le_one (map_nonneg _ _) (le_of_lt hfx) 
        (mul_nonneg (nat.cast_nonneg _)  (one_div_nonneg.mpr (nat.cast_nonneg _))), },
    { have hf_lim : filter.tendsto (λ (n : ℕ), f x ^ (↑(s(φ n)) * (1 / (φ n : ℝ)))) 
          filter.at_top (𝓝 1), 
        { nth_rewrite 0 ← real.rpow_zero (f x),
          refine filter.tendsto.rpow tendsto_const_nhds _ 
            (or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one (not_lt.mp hfx)))),
          { convert hφ_lim, -- TODO: rewrite hypothesis?
            simp only [function.comp_app, mul_one_div] }},
        rw tendsto_at_top_nhds at hf_lim,
      apply le_of_forall_pos_le_add,
      intros ε hε,
      have h1 : (1 : ℝ) ∈ set.Ioo 0 (1 + ε),
      { simp only [set.mem_Ioo, zero_lt_one, lt_add_iff_pos_right, true_and, hε], },
      obtain ⟨k, hk⟩ := hf_lim (set.Ioo (0 : ℝ) (1 + ε)) h1 is_open_Ioo,
      exact hc_bd (1 + ε) k (λ b hb, le_of_lt (set.mem_Ioo.mp (hk b hb)).2), }},
  { exact f_bdd_below hf1 s hn (0 : ℝ) φ },
  { exact f_nonempty hf1 hs_le hn φ  }
end

private lemma f_limsup_le_one' {x y : R} (hn : ∀ (n : pnat),
  ∃ (m : ℕ) (hm : m ∈ finset.range (n + 1)),  smoothing_seminorm_def hf1 (x + y) ≤ 
    (f (x ^ m) * f (y ^ (n - m : ℕ)))^(1/(n : ℝ))) {φ: ℕ → ℕ}
  (hφ_lim: filter.tendsto ((λ (n : ℕ), ↑(mu hf1 hn n) / (n : ℝ)) ∘ φ) filter.at_top (𝓝 0)) :
  filter.limsup (λ (n : ℕ), f x ^ ((mu hf1 hn (φ n) : ℝ) * (1 / (φ n : ℝ)))) filter.at_top ≤ 1 :=
begin
  simp only [filter.limsup, filter.Limsup],
  rw cInf_le_iff,
  { intros c hc_bd,
    simp only [mem_lower_bounds, filter.eventually_map, filter.eventually_at_top, ge_iff_le, 
      set.mem_set_of_eq, forall_exists_index] at hc_bd,
    by_cases hfx : f x < 1,
    { apply hc_bd (1 : ℝ) 0,
      rintros b -,
      exact real.rpow_le_one (map_nonneg _ _) (le_of_lt hfx) 
        (mul_nonneg (nat.cast_nonneg _)  (one_div_nonneg.mpr (nat.cast_nonneg _))), },
    { have hf_lim : filter.tendsto (λ (n : ℕ), f x ^ (↑(mu hf1 hn (φ n)) * (1 / (φ n : ℝ)))) 
          filter.at_top (𝓝 1), 
        { nth_rewrite 0 ← real.rpow_zero (f x),
          refine filter.tendsto.rpow tendsto_const_nhds _ 
            (or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one (not_lt.mp hfx)))),
          { convert hφ_lim, -- TODO: rewrite hypothesis?
            simp only [function.comp_app, mul_one_div] }},
        rw tendsto_at_top_nhds at hf_lim,
      apply le_of_forall_pos_le_add,
      intros ε hε,
      have h1 : (1 : ℝ) ∈ set.Ioo 0 (1 + ε),
      { simp only [set.mem_Ioo, zero_lt_one, lt_add_iff_pos_right, true_and, hε], },
      obtain ⟨k, hk⟩ := hf_lim (set.Ioo (0 : ℝ) (1 + ε)) h1 is_open_Ioo,
      exact hc_bd (1 + ε) k (λ b hb, le_of_lt (set.mem_Ioo.mp (hk b hb)).2), }},
  { exact f_bdd_below hf1 (mu hf1 hn) hn (0 : ℝ) φ },
  { exact f_nonempty hf1 (mu_le hf1 hn) hn φ  }
end

/- def smoothing_seminorm_seq (x : R) : ℕ → ℝ :=
λ n, (f (x ^ n))^(1/n : ℝ)-/

lemma smoothing_seminorm_seq_lim_is_limit_comp {s : ℕ → ℕ} (hs_le : ∀ n : ℕ, s n ≤ n) (x : R) 
 {a : ℝ} (a_in: a ∈ set.Ioc (0 : ℝ) 1) {φ : ℕ → ℕ} (hφ_mono: strict_mono φ) 
  (hφ_lim: filter.tendsto ((λ (n : ℕ), ↑(s n) / ↑n) ∘ φ) filter.at_top (𝓝 a)) :
  filter.tendsto (λ (n : ℕ), (f (x ^ (φ n)))^(1/(φ n) : ℝ)) filter.at_top
    (𝓝 (smoothing_seminorm_seq_lim hf1 x)) :=
begin
  have hφ_lim' : filter.tendsto φ filter.at_top filter.at_top,
  { exact strict_mono.tendsto_at_top hφ_mono },

  exact (smoothing_seminorm_seq_lim_is_limit hf1 x).comp hφ_lim',
end

lemma limsup_mu_le {s : ℕ → ℕ} (hs_le : ∀ n : ℕ, s n ≤ n) {x y : R}
  (hn : ∀ (n : pnat), ∃ (m : ℕ) (hm : m ∈ finset.range (n + 1)), 
  smoothing_seminorm_def hf1 (x + y) ≤ (f (x ^ m) * f (y ^ (n - m : ℕ)))^(1/(n : ℝ))) {a : ℝ} 
  (a_in: a ∈ set.Icc (0 : ℝ) 1) {φ: ℕ → ℕ} (hφ_mono: strict_mono φ)
  (hφ_lim: filter.tendsto ((λ (n : ℕ), ↑(s n) / ↑n) ∘ φ) filter.at_top (𝓝 a)) :
  filter.limsup (λ (n : ℕ), (f (x ^ (s (φ n))))^(1/(φ n : ℝ))) filter.at_top ≤
    (smoothing_seminorm_def hf1 x)^a :=
begin
  by_cases ha : a = 0,
  { rw ha at hφ_lim,
    calc filter.limsup (λ (n : ℕ), f (x ^ s (φ n)) ^ (1 / (φ n : ℝ))) filter.at_top ≤ 
      filter.limsup (λ (n : ℕ), f x ^ ((s (φ n) : ℝ) * (1 / (φ n : ℝ)))) filter.at_top : 
      begin
        apply cInf_le_cInf,
        { use (0 : ℝ),
          simp only [mem_lower_bounds, filter.eventually_map, filter.eventually_at_top, ge_iff_le,
            set.mem_set_of_eq, forall_exists_index],
          intros r m hm,
          exact le_trans (real.rpow_nonneg_of_nonneg (map_nonneg f _) _) (hm m (le_refl _)) },
        { exact f_nonempty hf1 hs_le hn φ, },
        { intros b hb,
          simp only [filter.eventually_map, filter.eventually_at_top, ge_iff_le, 
            set.mem_set_of_eq] at hb ⊢,
          obtain ⟨m, hm⟩ := hb,
          use m,
          intros k hkm,
          apply le_trans _ (hm k hkm),
          rw [real.rpow_mul (map_nonneg f x), real.rpow_nat_cast],
          exact real.rpow_le_rpow (map_nonneg f _) (map_pow_le_pow' hf1 x _) 
            (one_div_nonneg.mpr (nat.cast_nonneg _)), }
      end
    ... ≤ 1 : f_limsup_le_one hf1 hs_le hn hφ_lim
    ... = smoothing_seminorm_def hf1 x ^ a : by rw [ha, real.rpow_zero] },
  { apply le_of_eq,
    sorry }
  --simp only [smoothing_seminorm_def,smoothing_seminorm_seq_lim],
end

omit hf1
lemma sub_mem_closure {a b : ℝ} (h : a ∈ set.Icc (0 : ℝ) b) :
  b - a ∈ set.Icc (0 : ℝ) b := 
begin
  rw [set.mem_Icc] at h ⊢,
  rw [sub_le_self_iff],
  exact ⟨sub_nonneg_of_le h.2, h.1⟩
end

include hf1

private lemma filter_is_bdd_under {s : ℕ → ℕ} (hs_le : ∀ n : ℕ, s n ≤ n) {x : R} (φ : ℕ → ℕ) :
  filter.is_bounded_under has_le.le filter.at_top (λ (n : ℕ), f (x ^ s (φ n)) ^ (1 / (φ n : ℝ))) :=
begin
  have h_le : ∀ m : ℕ, f (x ^ s (φ m)) ^ (1 / (φ m : ℝ)) ≤ (f x) ^ ((s (φ m) : ℝ) / (φ m : ℝ)),
    { intro m,
      rw [← mul_one_div (s (φ m) : ℝ), real.rpow_mul (map_nonneg f x), real.rpow_nat_cast],
      exact real.rpow_le_rpow (map_nonneg _ _) (map_pow_le_pow' hf1 x _)
        (one_div_nonneg.mpr (nat.cast_nonneg _)) }, -- TODO: I think I have a similar proof somewhere...
  apply filter.is_bounded_under_of,
  by_cases hfx : f x ≤ 1,
  { use [1, λ m, le_trans (h_le m) (real.rpow_le_one (map_nonneg _ _) hfx
      (div_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _)))] },
  { use (f x),
    intro m,
    apply le_trans (h_le m),
    conv_rhs{ rw ← real.rpow_one (f x) },
    exact real.rpow_le_rpow_of_exponent_le (le_of_lt (not_le.mp hfx))
      (div_le_one_of_le (nat.cast_le.mpr (hs_le _)) (nat.cast_nonneg _)), } 
end

lemma smoothing_seminorm_is_nonarchimedean (hna : is_nonarchimedean f) :
  is_nonarchimedean (smoothing_seminorm_def hf1) :=
begin
  intros x y,
  have hn : ∀ (n : pnat), ∃ (m : ℕ) (hm : m ∈ finset.range (n + 1)), 
    smoothing_seminorm_def hf1 (x + y) ≤ (f (x ^ m) * f (y ^ (n - m : ℕ)))^(1/(n : ℝ)) :=
  λ n, exists_index_le hf1 hna x y n, 
  set mu : ℕ → ℕ := λ n, mu hf1 hn n with hmu,
  set nu : ℕ → ℕ := λ n, n - (mu n) with hnu,
  have hmu_le : ∀ n : ℕ, mu n ≤ n := λ n, mu_le hf1 hn n,
  have hmu_bdd : ∀ n : ℕ, (mu n : ℝ)/n ∈ set.Icc (0 : ℝ) 1 := λ n, mu_bdd hf1 hn n,
  have hs : metric.bounded (set.Icc (0 : ℝ) 1) := metric.bounded_Icc 0 1,
  obtain ⟨a, a_in, φ, hφ_mono, hφ_lim⟩ := tendsto_subseq_of_bounded hs hmu_bdd,
  rw closure_Icc at a_in,

  set b := 1 - a with hb,
  have hb_lim : filter.tendsto ((λ (n : ℕ), ↑(nu n) / ↑n) ∘ φ) filter.at_top (𝓝 b),
  { apply filter.tendsto.congr' _ (filter.tendsto.const_sub 1 hφ_lim),
    simp only [filter.eventually_eq,function.comp_app, filter.eventually_at_top, ge_iff_le],
    use 1,
    intros m hm,
    have h0 : (φ m : ℝ ) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_gt (lt_of_le_of_lt (zero_le _) 
      (hφ_mono (nat.pos_of_ne_zero (nat.one_le_iff_ne_zero.mp hm))))),
    rw [← div_self h0, ← sub_div],
    simp only [hnu],
    rw nat.cast_sub,
    exact hmu_le _ },

  have b_in : b ∈ set.Icc (0 : ℝ) 1 := sub_mem_closure a_in,
  have hnu_le : ∀ n : ℕ, nu n ≤ n := λ n, by simp only [hnu, tsub_le_self],

  have hx : filter.limsup (λ (n : ℕ), (f (x ^ (mu (φ n))))^(1/(φ n : ℝ))) filter.at_top ≤
    (smoothing_seminorm_def hf1 x)^a,
  { exact limsup_mu_le hf1 hmu_le hn a_in hφ_mono hφ_lim },
  have hy : filter.limsup (λ (n : ℕ), (f (y ^ (nu (φ n))))^(1/(φ n : ℝ))) filter.at_top ≤
    (smoothing_seminorm_def hf1 y)^b,
  { exact limsup_mu_le hf1 hnu_le (exists_index_le hf1 hna y x) b_in hφ_mono hb_lim },

  have hxy : filter.limsup (λ (n : ℕ), 
    (f (x ^ (mu (φ n))))^(1/(φ n : ℝ) * f (y ^ (nu (φ n))))^(1/(φ n : ℝ))) filter.at_top ≤
    (smoothing_seminorm_def hf1 x)^a * (smoothing_seminorm_def hf1 y)^b ,
  { have : filter.limsup (λ (n : ℕ),
    (f (x ^ (mu (φ n))))^(1/(φ n : ℝ) * f (y ^ (nu (φ n))))^(1/(φ n : ℝ)))  filter.at_top ≤
    (filter.limsup (λ (n : ℕ), (f (x ^ (mu (φ n))))^(1/(φ n : ℝ)))) filter.at_top *
    (filter.limsup (λ (n : ℕ), (f (y ^ (nu (φ n))))^(1/(φ n : ℝ)))) filter.at_top,
    { --rw cInf_mul,
      
      sorry },
    apply le_trans this,
    apply mul_le_mul hx hy _ (real.rpow_nonneg_of_nonneg (smoothing_seminorm_nonneg hf1 x) _),

    have h_bdd : filter.is_bounded_under 
          has_le.le filter.at_top (λ (n : ℕ), f (y ^ nu (φ n)) ^ (1 / (φ n : ℝ))),
    { exact filter_is_bdd_under hf1 hnu_le φ },
    exact filter.limsup_nonneg_of_nonneg h_bdd (λ m, real.rpow_nonneg_of_nonneg (map_nonneg _ _) _),
    /- exact filter.le_limsup_of_frequently_le 
      (filter.frequently_of_forall (λ m, real.rpow_nonneg_of_nonneg (map_nonneg _ _) _)) h_bdd, -/ },

  conv_lhs { simp only [smoothing_seminorm_def, smoothing_seminorm_seq_lim], },
  --rw ← nnreal.coe_le_coe,
  apply le_of_forall_sub_le,
  intros ε hε,
  --have hε_nnr : ε = ((⟨ε, le_of_lt hε⟩ : nnreal) : ℝ) := rfl,
  rw sub_le_iff_le_add, --rw hε_nnr, --rw ← nnreal.coe_add, rw nnreal.coe_le_coe,

  have hxy' : filter.limsup (λ (n : ℕ), 
    (f (x ^ (mu (φ n))))^(1/(φ n : ℝ) * f (y ^ (nu (φ n))))^(1/(φ n : ℝ)))  filter.at_top <
    (smoothing_seminorm_def hf1 x)^a * (smoothing_seminorm_def hf1 y)^b + ε,
  { sorry },

  have h_mul : (smoothing_seminorm_def hf1 x)^a * (smoothing_seminorm_def hf1 y)^b + ε ≤
    max (smoothing_seminorm_def hf1 x) (smoothing_seminorm_def hf1 y) + ε,
  { rw max_def,
    split_ifs with h, -- TODO: rw using wlog or similar
    { rw [add_le_add_iff_right],
      apply le_trans (mul_le_mul_of_nonneg_right (real.rpow_le_rpow 
        (smoothing_seminorm_nonneg hf1 _) h a_in.1)
        (real.rpow_nonneg_of_nonneg (smoothing_seminorm_nonneg hf1 _) _)),
      rw [hb, ← real.rpow_add_of_nonneg (smoothing_seminorm_nonneg hf1 _) a_in.1
        (sub_nonneg.mpr a_in.2), add_sub, add_sub_cancel', real.rpow_one], },
    { rw [add_le_add_iff_right],
      apply le_trans (mul_le_mul_of_nonneg_left (real.rpow_le_rpow 
        (smoothing_seminorm_nonneg hf1 _) (le_of_lt (not_le.mp h)) b_in.1)
        (real.rpow_nonneg_of_nonneg (smoothing_seminorm_nonneg hf1 _) _)),
      rw [hb, ← real.rpow_add_of_nonneg (smoothing_seminorm_nonneg hf1 _) a_in.1
        (sub_nonneg.mpr a_in.2), add_sub, add_sub_cancel', real.rpow_one] }},
  
  apply le_trans _ h_mul,

  have hex : ∃ n : pnat,
    (f (x ^ (mu (φ n))))^(1/(φ n : ℝ) * f (y ^ (nu (φ n))))^(1/(φ n : ℝ)) <
    (smoothing_seminorm_def hf1 x)^a * (smoothing_seminorm_def hf1 y)^b + ε,
  { sorry },

  obtain ⟨N, hN⟩ := hex,

  have hf : bdd_below (set.range (λ n : pnat, f ((x + y) ^ (n : ℕ)) ^ (1 / (n : ℝ)))),
  { sorry },
  --simp only [smoothing_seminorm_def, smoothing_seminorm_seq_lim],
  apply le_trans (cinfi_le hf N),
  
  sorry
  --sorry,
   /-  have h := filter.eventually_lt_of_limsup_lt hxy' _,

    { sorry },

    { simp only [auto_param_eq],
      
      --refine filter.is_bounded_under_of _,
      sorry }, -/

    --rw ← filter.limsup_const ((smoothing_seminorm hf1 x)^a) at hx,
    --apply cinfi_le_of_le,

end

end is_nonarchimedean

/- 
lemma smoothing_seminorm_is_nonarchimedean (hna : is_nonarchimedean f) :
  is_nonarchimedean (smoothing_seminorm_def hf1) :=
begin
  intros x y,
  have hn : ∀ (n : pnat), ∃ (m : ℕ) (hm : m ∈ finset.range (n + 1)), 
    smoothing_seminorm_def hf1 (x + y) ≤ (f (x ^ m) * f (y ^ (n - m : ℕ)))^(1/(n : ℝ)) :=
  λ n, exists_index_le hf1 hna x y n, 
  set mu : ℕ → ℕ := λ n, if h : n = 0 then 0 else
    (classical.some (hn (⟨n, nat.pos_of_ne_zero h⟩ : pnat))) with hmu,
  set nu : ℕ → ℕ := λ n, n - (mu n) with hnu,
  have hmu_le : ∀ n : ℕ, mu n ≤ n,
  { intro n,
    by_cases hn0 : n = 0,
    { simp only [hmu, dif_pos hn0], exact eq.ge hn0 },
    { simp only [hmu, dif_neg hn0, ← nat.lt_succ_iff, ← finset.mem_range],
      exact classical.some (classical.some_spec (hn (⟨n, nat.pos_of_ne_zero hn0⟩ : pnat))), }},
  have hmu_bdd : ∀ n : ℕ, (mu n : ℝ)/n ∈ set.Icc (0 : ℝ) 1,
  { intro n,
    refine set.mem_Icc.mpr ⟨_, _⟩,
    { simp only [min_eq_left, zero_le_one],
      exact div_nonneg (nat.cast_nonneg (mu n)) (nat.cast_nonneg n), },
    { simp only [zero_le_one, max_eq_right],
      by_cases hn0 : n = 0,
      { rw [hn0, nat.cast_zero, div_zero], exact zero_le_one, },
      { have hn' : 0 < (n : ℝ) := nat.cast_pos.mpr (nat.pos_of_ne_zero hn0),
        rw [div_le_one hn', nat.cast_le],
        exact hmu_le _, }}},
  have hs : metric.bounded (set.Icc (0 : ℝ) 1),
  { exact metric.bounded_Icc (min 0 1) (max 0 1)},
  obtain ⟨a, a_in, φ, hφ_mono, hφ_lim⟩ := tendsto_subseq_of_bounded hs hmu_bdd,
  set b := 1 - a with hb,
  have hb_lim : filter.tendsto ((λ (n : ℕ), ↑(nu n) / ↑n) ∘ φ) filter.at_top (𝓝 b),
  { apply filter.tendsto.congr' _ (filter.tendsto.const_sub 1 hφ_lim),
    simp only [filter.eventually_eq,function.comp_app, filter.eventually_at_top, ge_iff_le],
    use 1,
    intros m hm,
    have h0 : (φ m : ℝ ) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_gt (lt_of_le_of_lt (zero_le _) 
      (hφ_mono (nat.pos_of_ne_zero (nat.one_le_iff_ne_zero.mp hm))))),
    rw [← div_self h0, ← sub_div],
    simp only [hnu],
    rw nat.cast_sub,
    exact hmu_le _ },

  have hx : filter.limsup (λ (n : ℕ), (f (x ^ (mu (φ n))))^(1/(φ n : ℝ))) filter.at_top ≤
    (smoothing_seminorm_def hf1 x)^a,
  { sorry },
  have hy : filter.limsup (λ (n : ℕ), (f (y ^ (nu (φ n))))^(1/(φ n : ℝ))) filter.at_top ≤
    (smoothing_seminorm_def hf1 y)^b,
  { sorry },

  have hxy : filter.limsup (λ (n : ℕ), 
    (f (x ^ (mu (φ n))))^(1/(φ n : ℝ) * f (y ^ (nu (φ n))))^(1/(φ n : ℝ))) filter.at_top ≤
    (smoothing_seminorm_def hf1 x)^a * (smoothing_seminorm_def hf1 y)^b ,
  { have : filter.limsup (λ (n : ℕ),
    (f (x ^ (mu (φ n))))^(1/(φ n : ℝ) * f (y ^ (nu (φ n))))^(1/(φ n : ℝ)))  filter.at_top ≤
    (filter.limsup (λ (n : ℕ), (f (x ^ (mu (φ n))))^(1/(φ n : ℝ)))) filter.at_top *
    ( filter.limsup (λ (n : ℕ), (f (y ^ (nu (φ n))))^(1/(φ n : ℝ)))) filter.at_top,
    { sorry },
    apply le_trans this,
    apply mul_le_mul hx hy _ (real.rpow_nonneg_of_nonneg (smoothing_seminorm_nonneg hf1 x) _),

    have h_bdd : filter.is_bounded_under 
          has_le.le filter.at_top (λ (n : ℕ), f (y ^ nu (φ n)) ^ (1 / (φ n : ℝ))),
    { apply filter.is_bounded_under_of,
      sorry
    },
    exact filter.limsup_nonneg_of_nonneg h_bdd (λ m, real.rpow_nonneg_of_nonneg (map_nonneg _ _) _),
    /- exact filter.le_limsup_of_frequently_le 
      (filter.frequently_of_forall (λ m, real.rpow_nonneg_of_nonneg (map_nonneg _ _) _)) h_bdd, -/ },

  conv_lhs { simp only [smoothing_seminorm_def, smoothing_seminorm_seq_lim], },
  --rw ← nnreal.coe_le_coe,
  apply le_of_forall_sub_le,
  intros ε hε,
  --have hε_nnr : ε = ((⟨ε, le_of_lt hε⟩ : nnreal) : ℝ) := rfl,
  rw sub_le_iff_le_add, --rw hε_nnr, --rw ← nnreal.coe_add, rw nnreal.coe_le_coe,

  have hxy' : filter.limsup (λ (n : ℕ), 
    (f (x ^ (mu (φ n))))^(1/(φ n : ℝ) * f (y ^ (nu (φ n))))^(1/(φ n : ℝ)))  filter.at_top <
    (smoothing_seminorm_def hf1 x)^a * (smoothing_seminorm_def hf1 y)^b + ε,
  { sorry },
  sorry
  --sorry,
   /-  have h := filter.eventually_lt_of_limsup_lt hxy' _,

    { sorry },

    { simp only [auto_param_eq],
      
      --refine filter.is_bounded_under_of _,
      sorry }, -/

    --rw ← filter.limsup_const ((smoothing_seminorm hf1 x)^a) at hx,
    --apply cinfi_le_of_le,

end -/

def smoothing_seminorm (hna : is_nonarchimedean f) : ring_seminorm R :=
{ to_fun    := smoothing_seminorm_def hf1,
  map_zero' := smoothing_seminorm_zero hf1,
  add_le'   := add_le_of_is_nonarchimedean (smoothing_seminorm_nonneg hf1)
    (smoothing_seminorm_is_nonarchimedean hf1 hna),
  neg'      := smoothing_seminorm_neg hf1 (map_neg_eq_map f),
  mul_le'   := smoothing_seminorm_mul hf1 }

lemma smoothing_seminorm_is_seminorm_is_norm_le_one_class (hna : is_nonarchimedean f) : 
  smoothing_seminorm hf1 hna 1 ≤ 1 := 
smoothing_seminorm_one hf1

lemma smoothing_seminorm_is_pow_mul :
  is_pow_mul (smoothing_seminorm_def hf1) :=
begin
  intros x m hm,
  simp only [smoothing_seminorm_def],
  have hlim : filter.tendsto (λ n, smoothing_seminorm_seq  f x (m*n)) filter.at_top
    (𝓝 (smoothing_seminorm_seq_lim hf1 x )),
  { refine filter.tendsto.comp (smoothing_seminorm_seq_lim_is_limit hf1 x) _,
    apply filter.tendsto_at_top_at_top_of_monotone,
    { intros n k hnk, exact mul_le_mul_left' hnk m, },
    { rintro n, use n, exact le_mul_of_one_le_left' hm, }},
  apply tendsto_nhds_unique _ (filter.tendsto.pow hlim m),
  have h_eq : ∀ (n : ℕ), smoothing_seminorm_seq f x (m * n) ^ m =
    smoothing_seminorm_seq f (x^m) n,
  { have hm' : (m : ℝ) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hm)), 
    intro n,
    simp only [smoothing_seminorm_seq],
    rw [pow_mul, ← real.rpow_nat_cast, ← real.rpow_mul (map_nonneg f _), nat.cast_mul, 
      ← one_div_mul_one_div, mul_comm (1 / (m : ℝ)), mul_assoc, one_div_mul_cancel hm', mul_one] },
  simp_rw h_eq,
  exact smoothing_seminorm_seq_lim_is_limit hf1 _
end

lemma smoothing_seminorm_of_pow_mult {x : R} (hx : ∀ (n : ℕ) (hn : 1 ≤ n), f (x ^ n) = f x ^ n) :
  smoothing_seminorm_def hf1 x = f x :=
begin
  apply tendsto_nhds_unique_of_eventually_eq (smoothing_seminorm_seq_lim_is_limit hf1 x)
    tendsto_const_nhds,
  simp only [filter.eventually_eq, filter.eventually_at_top, ge_iff_le],
  use 1,
  intros n hn,
  simp only [smoothing_seminorm_seq],
  have hn0 : (n : ℝ) ≠ 0 := nat.cast_ne_zero.mpr (nat.one_le_iff_ne_zero.mp hn),
  rw [hx n hn, ← real.rpow_nat_cast, ← real.rpow_mul (map_nonneg f _), mul_one_div_cancel hn0,
    real.rpow_one],
end

lemma f_is_mult_pow_of_is_mult  {x : R} (hx : ∀ y : R, f (x * y) = f x * f y) :
   ∀ (n : ℕ) (y : R), f (x ^ n * y) = f x ^ n * f y :=
begin
  { intros n,
    induction n with n hn,
    { intro y, rw [pow_zero, pow_zero, one_mul, one_mul]},
    { intro y, rw [pow_succ', pow_succ', mul_assoc, mul_assoc, ← hx y], exact hn _, }},
end

lemma smoothing_seminorm_apply_of_is_mult' {x : R} (hx : ∀ y : R, f (x * y) = f x * f y) :
  smoothing_seminorm_def hf1 x = f x :=
begin
  apply tendsto_nhds_unique_of_eventually_eq (smoothing_seminorm_seq_lim_is_limit hf1 x)
    tendsto_const_nhds,
  simp only [filter.eventually_eq, filter.eventually_at_top, ge_iff_le],
  use 1,
  intros n hn,
  simp only [smoothing_seminorm_seq],
  by_cases hx0 : f x = 0,
  { have hxn : f (x ^ n) = 0,
    { apply le_antisymm _ (map_nonneg f _),
      apply le_trans (map_pow_le_pow f x (nat.one_le_iff_ne_zero.mp hn)),
      rw [hx0, zero_pow (lt_of_lt_of_le zero_lt_one hn)], },
    rw [hx0, hxn, real.zero_rpow (nat.one_div_cast_ne_zero (nat.one_le_iff_ne_zero.mp hn))] },
  { have h1 : f 1 = 1,
    { rw [← mul_right_inj' hx0, ← hx 1, mul_one, mul_one] },
    have hn0 : (n : ℝ) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hn)),
    rw [← mul_one (x ^ n), f_is_mult_pow_of_is_mult hf1 hx, ← real.rpow_nat_cast, h1, mul_one,
      ← real.rpow_mul (map_nonneg f _), mul_one_div_cancel hn0, real.rpow_one] },
end

lemma smoothing_seminorm_apply_of_is_mult {x : R} (hx : ∀ y : R, f (x * y) = f x * f y)
  (hna : is_nonarchimedean f) : smoothing_seminorm hf1 hna x = f x :=
smoothing_seminorm_apply_of_is_mult' hf1 hx

lemma smoothing_seminorm_of_mult' {x : R} (hx : ∀ (y : R), f (x * y) = f x * f y) (y : R) :
  smoothing_seminorm_def hf1 (x * y) = 
    smoothing_seminorm_def hf1 x * smoothing_seminorm_def hf1 y :=
begin
  have hlim : filter.tendsto (λ n, f x * smoothing_seminorm_seq f y n) filter.at_top
    (𝓝 (smoothing_seminorm_def hf1 x * smoothing_seminorm_def hf1 y)),
  { rw [smoothing_seminorm_apply_of_is_mult' hf1 hx],
    exact filter.tendsto.const_mul _ (smoothing_seminorm_seq_lim_is_limit hf1 y), },
  apply tendsto_nhds_unique_of_eventually_eq (smoothing_seminorm_seq_lim_is_limit hf1 (x * y))
    hlim,
  simp only [filter.eventually_eq, filter.eventually_at_top, ge_iff_le],
  use 1,
  intros n hn1,
  have hn0 : (n : ℝ) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hn1)),
  simp only [smoothing_seminorm_seq],
  rw [mul_pow, f_is_mult_pow_of_is_mult hf1 hx, real.mul_rpow (pow_nonneg (map_nonneg f _) _)
    (map_nonneg f _), ← real.rpow_nat_cast, ← real.rpow_mul (map_nonneg f _),
    mul_one_div_cancel hn0, real.rpow_one]
end

lemma smoothing_seminorm_of_mult {x : R} (hx : ∀ (y : R), f (x * y) = f x * f y)
  (hna : is_nonarchimedean f) (y : R) :
  smoothing_seminorm hf1 hna (x * y) = 
    smoothing_seminorm hf1 hna x * smoothing_seminorm hf1 hna y :=
smoothing_seminorm_of_mult' hf1 hx y

end smoothing_seminorm