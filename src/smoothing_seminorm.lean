/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/

import analysis.special_functions.pow
import limsup
import ring_seminorm

/-!
# smoothing_seminorm
In this file, we prove [BGR, Proposition 1.3.2/1] : if `f` is a nonarchimedean seminorm on `R`, 
then `infi (λ (n : pnat), (f(x^(n : ℕ)))^(1/(n : ℝ)))` is a power-multiplicative nonarchimedean
seminorm on `R`.

## Main Definitions

* `smoothing_seminorm_seq` : the `ℝ`-valued sequence sending `n` to `(f (x ^ n))^(1/n : ℝ)`.
* `smoothing_seminorm_def` : The infi of the sequence `f(x^(n : ℕ)))^(1/(n : ℝ)`. 
* `smoothing_seminorm` : iIf `f 1 ≤ 1` and `f` is nonarchimedean, then `smoothing_seminorm_def`
  is a ring seminorm. 

## Main Results

* `smoothing_seminorm_def_is_limit` :if `f 1 ≤ 1`, then `smoothing_seminorm_def f x` is the limit
  of `smoothing_seminorm_seq f x` as `n` tends to infinity. 
* `smoothing_seminorm_is_nonarchimedean` : if `f 1 ≤ 1` and `f` is nonarchimedean, then
  `smoothing_seminorm_def` is nonarchimedean.
* `smoothing_seminorm_is_pow_mul` : if `f 1 ≤ 1` and `f` is nonarchimedean, then
  `smoothing_seminorm_def f` is power-multiplicative. 

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

smoothing_seminorm, seminorm, nonarchimedean
-/

noncomputable theory

open real

open_locale topological_space nnreal

-- In this section we prove auxiliary lemmas, which will be PR'd to the appropriate mathlib files.
section aux_lemmas

/-- If `a` belongs to the interval `[0, b]`, then so does `b - a`. -/
lemma sub_mem_closure {a b : ℝ} (h : a ∈ set.Icc (0 : ℝ) b) :
  b - a ∈ set.Icc (0 : ℝ) b := 
begin
  rw [set.mem_Icc] at h ⊢,
  rw [sub_le_self_iff],
  exact ⟨sub_nonneg_of_le h.2, h.1⟩
end

/-- If `x` is multiplicative with respect to `f`, then so is any `x^n`. -/
lemma is_mul_pow_of_is_mul {R : Type*} [comm_ring R] (f : R → ℝ) {x : R}
  (hx : ∀ y : R, f (x * y) = f x * f y) :
  ∀ (n : ℕ) (y : R), f (x ^ n * y) = f x ^ n * f y :=
begin
  { intros n,
    induction n with n hn,
    { intro y, rw [pow_zero, pow_zero, one_mul, one_mul]},
    { intro y, rw [pow_succ', pow_succ', mul_assoc, mul_assoc, ← hx y], exact hn _, }},
end

/-- For any `r : ℝ≥0` and any positive `n : ℕ`,  `(r ^ n)^(1/n : ℝ) = r`. -/
lemma nnreal.pow_n_n_inv (r : ℝ≥0) {n : ℕ} (hn : 0 < n) : (r ^ n)^(1/n : ℝ) = r :=
begin
  have hn1 : (n : ℝ) * (1/n) = 1,
  { apply mul_one_div_cancel,
    exact (nat.cast_ne_zero.mpr (nat.one_le_iff_ne_zero.mp hn)) },
  conv_rhs { rw [← nnreal.rpow_one r, ← hn1] },
  rw [nnreal.rpow_mul, nnreal.rpow_nat_cast],
end

/-- For any nonnegative `r : ℝ` and any positive `n : ℕ`,  `(r ^ n)^(1/n : ℝ) = r`. -/
lemma real.pow_n_n_inv {r : ℝ} (hr : 0 ≤ r) {n : ℕ} (hn : 0 < n) : (r ^ n)^(1/n : ℝ) = r :=
begin
  have hn1 : (n : ℝ) * (1/n) = 1,
  { apply mul_one_div_cancel,
    exact (nat.cast_ne_zero.mpr (nat.one_le_iff_ne_zero.mp hn)) },
  conv_rhs { rw [← rpow_one r, ← hn1] },
  rw [real.rpow_mul hr, rpow_nat_cast],
end

namespace filter

/-- If there exists real constants `b`and `B` such that for `n` big enough, `b ≤ f n ≤ B`, then
  `f n / (n : ℝ)` tends to `0` as `n` tends to infinity. -/
lemma tendsto_bdd_div_at_top_nhds_0_nat (f : ℕ → ℝ) (hfb : ∃ b : ℝ, ∀ᶠ (n : ℕ) in at_top, b ≤ f n)
  (hfB : ∃ B : ℝ, ∀ᶠ (n : ℕ) in at_top, f n ≤ B) : 
  tendsto (λ (n: ℕ), ((f n / (n : ℝ)))) at_top (𝓝 0) :=
begin
  obtain ⟨b, hb⟩ := hfb,
  obtain ⟨B, hB⟩ := hfB,
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_div_at_top_nhds_0_nat b)
    (tendsto_const_div_at_top_nhds_0_nat B) _ _,
  { simp only [eventually_at_top, ge_iff_le] at hb ⊢,
    obtain ⟨N, hN⟩ := hb,
    use N, intros n hn,
    exact div_le_div_of_le (nat.cast_nonneg _) (hN n hn) },
  { simp only [eventually_at_top, ge_iff_le] at hB ⊢,
    obtain ⟨N, hN⟩ := hB,
    use N, intros n hn,
    exact div_le_div_of_le (nat.cast_nonneg _) (hN n hn) },
end

/-- For any positive `m : ℕ`, `((n % m : ℕ) : ℝ) / (n : ℝ)` tends to `0` as `n` tends to `∞`. -/
lemma tendsto_mod_div_at_top_nhds_0_nat {m : ℕ} (hm : 0 < m) : 
  tendsto (λ (n: ℕ), (((n % m : ℕ) : ℝ) / (n : ℝ))) at_top (𝓝 0) :=
begin
  apply tendsto_bdd_div_at_top_nhds_0_nat (λ (n: ℕ), ((n % m : ℕ) : ℝ)),
  { use 0,
    apply eventually_of_forall,
    intros n,
    simp only [nat.cast_nonneg], },
  { use m,
    apply eventually_of_forall,
    intros n, 
    simp only [nat.cast_le,le_of_lt (nat.mod_lt n hm)] }
end

/-- If `u` tends to `∞` as `n` tends to `∞`, then for `n` big enough
`((s n : ℝ) / (u n : ℝ)) * (u n : ℝ) = (s n : ℝ)` holds. -/
lemma div_mul_eventually_cancel (s : ℕ → ℕ) {u : ℕ → ℕ} (hu : tendsto u at_top at_top) :
  (λ n, ((s n : ℝ) / (u n : ℝ)) * (u n : ℝ)) =ᶠ[at_top] (λ n, (s n : ℝ)) :=
begin
  simp only [eventually_eq, eventually_at_top, ge_iff_le],
  simp only [tendsto_at_top, eventually_at_top, ge_iff_le] at hu,
  obtain ⟨n, hn⟩ := hu 1,
  use n,
  intros m hm,
  rw div_mul_cancel (s m : ℝ) (nat.cast_ne_zero.mpr (nat.one_le_iff_ne_zero.mp (hn m hm))),
end

/-- If when `n` tends to `∞`, `u` tends to `∞` and `(s n : ℝ) / (u n : ℝ))` tends to a nonzero
  constant, then `s` tends to `∞`. -/
lemma tendsto.num {s u : ℕ → ℕ} (hu : tendsto u at_top at_top) {a : ℝ} (ha : 0 < a) 
  (hlim : tendsto (λ (n : ℕ), (s n : ℝ) / (u n : ℝ)) at_top (𝓝 a)) : tendsto s at_top at_top :=
tendsto_coe_nat_at_top_iff.mp (tendsto.congr' (div_mul_eventually_cancel s hu)
  (tendsto.mul_at_top ha hlim (tendsto_coe_nat_at_top_iff.mpr hu)))

/-- If `f` is a ring seminorm on `R` with `f 1 ≤ 1` and `s : ℕ → ℕ` is bounded by `n`, then 
  `f (x ^ s (φ n)) ^ (1 / (φ n : ℝ))` is eventually bounded. -/
lemma is_bdd_under {R : Type*} [comm_ring R] (f : ring_seminorm R) (hf1 : f 1 ≤ 1)
  {s : ℕ → ℕ} (hs_le : ∀ n : ℕ, s n ≤ n) {x : R} (φ : ℕ → ℕ) :
  is_bounded_under has_le.le at_top (λ (n : ℕ), f (x ^ s (φ n)) ^ (1 / (φ n : ℝ))) :=
begin
  have h_le : ∀ m : ℕ, f (x ^ s (φ m)) ^ (1 / (φ m : ℝ)) ≤ (f x) ^ ((s (φ m) : ℝ) / (φ m : ℝ)),
    { intro m,
      rw [← mul_one_div (s (φ m) : ℝ), rpow_mul (map_nonneg f x), rpow_nat_cast],
      exact rpow_le_rpow (map_nonneg _ _) (map_pow_le_pow' hf1 x _)
        (one_div_nonneg.mpr (nat.cast_nonneg _)) },
  apply is_bounded_under_of,
  by_cases hfx : f x ≤ 1,
  { use [1, λ m, le_trans (h_le m) (real.rpow_le_one (map_nonneg _ _) hfx
      (div_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _)))] },
  { use (f x),
    intro m,
    apply le_trans (h_le m),
    conv_rhs{ rw ← rpow_one (f x) },
    exact rpow_le_rpow_of_exponent_le (le_of_lt (not_le.mp hfx))
      (div_le_one_of_le (nat.cast_le.mpr (hs_le _)) (nat.cast_nonneg _)), } 
end

end filter

end aux_lemmas

open filter

variables {R : Type*} [comm_ring R] (f : ring_seminorm R)  

section smoothing_seminorm

/-- The `ℝ`-valued sequence sending `n` to `(f (x ^ n))^(1/n : ℝ)`. -/
def smoothing_seminorm_seq (x : R) : ℕ → ℝ := λ n, (f (x ^ n))^(1/n : ℝ)

/-- For any positive `ε`, there exists a positive natural number `m` such that
  `infi (λ (n : pnat), (f(x ^(n : ℕ)))^(1/(n : ℝ))) + ε/2`. -/
lemma smoothing_seminorm_seq_has_limit_m (x : R) {ε : ℝ} (hε : 0 < ε) : 
  ∃ (m : pnat), (f (x ^(m : ℕ)))^(1/m : ℝ) < 
    infi (λ (n : pnat), (f(x ^(n : ℕ)))^(1/(n : ℝ))) + ε/2 :=
exists_lt_of_cinfi_lt (lt_add_of_le_of_pos (le_refl _) (half_pos hε))

lemma smoothing_seminorm_seq_has_limit_aux {L : ℝ} (hL : 0 ≤ L) {ε : ℝ} (hε : 0 < ε)
  {m1 : ℕ} (hm1 : 0 < m1) {x : R} (hx : f x ≠ 0) : 
  tendsto (λ (n : ℕ), (L + ε)^
    (-(((n % m1 : ℕ) : ℝ)/(n : ℝ)))*((f x) ^(n % m1)) ^ (1 / (n : ℝ))) at_top (𝓝 1) := 
begin
  rw ← mul_one (1 : ℝ),
  have h_exp : tendsto (λ (n: ℕ), (((n % m1 : ℕ) : ℝ) / (n : ℝ))) at_top (𝓝 0) := 
  tendsto_mod_div_at_top_nhds_0_nat hm1,
  apply tendsto.mul,
  { have h0 : tendsto (λ (t : ℕ), -(((t % m1 : ℕ) : ℝ) / (t : ℝ))) at_top (𝓝 0),
    { rw ← neg_zero, exact tendsto.neg h_exp, },
    rw [← rpow_zero (L + ε)],
    apply tendsto.rpow tendsto_const_nhds h0,
    rw [ne.def, add_eq_zero_iff' hL (le_of_lt hε)],
    exact or.inl (not_and_of_not_right _ (ne_of_gt hε)) },
  { simp_rw [mul_one, ← rpow_nat_cast, ← rpow_mul (map_nonneg f x), ← mul_div_assoc,
      mul_one, ← rpow_zero (f x)],
    exact tendsto.rpow tendsto_const_nhds h_exp (or.inl hx), },
end

/-- `smoothing_seminorm_seq` is bounded below by zero. -/
lemma smoothing_seminorm_seq_bdd (x : R) : 
  bdd_below (set.range (λ (n : ℕ+), f (x ^(n : ℕ)) ^ (1 / (n : ℝ)))) := 
begin
  use 0,
  rintros y ⟨n, rfl⟩,
  exact rpow_nonneg_of_nonneg (map_nonneg f _) _, 
end

/-- The infi of the sequence `f(x^(n : ℕ)))^(1/(n : ℝ)`. -/
def smoothing_seminorm_def (x : R) : ℝ := infi (λ (n : pnat), (f(x^(n : ℕ)))^(1/(n : ℝ)))

/-- If `f x = 0`, then `smoothing_seminorm_def f x` is the limit of `smoothing_seminorm_seq f x`. -/
lemma smoothing_seminorm_def_is_limit_zero {x : R} (hx : f x = 0) :
  tendsto ((smoothing_seminorm_seq f x)) at_top (𝓝 (smoothing_seminorm_def f x)) := 
begin
  have h0 : ∀ (n : ℕ) (hn : 1 ≤ n), (f (x ^ n))^(1/(n : ℝ)) = 0,
  { intros n hn,
    have hfn : f (x ^ n) = 0,
    { apply le_antisymm _ (map_nonneg f _),
      rw [← zero_pow hn, ← hx], 
      exact map_pow_le_pow _ x (nat.one_le_iff_ne_zero.mp hn) },
    rw [hfn, zero_rpow (nat.one_div_cast_ne_zero (nat.one_le_iff_ne_zero.mp hn))], },
  have hL0 : infi (λ (n : pnat), (f(x^(n : ℕ)))^(1/(n : ℝ))) = 0 :=
  le_antisymm (cinfi_le_of_le (smoothing_seminorm_seq_bdd f x) (1 : pnat)
    (le_of_eq (h0 1 (le_refl _)))) (le_cinfi (λ n, rpow_nonneg_of_nonneg (map_nonneg f _) _)),
  simp only [hL0, smoothing_seminorm_seq, smoothing_seminorm_def],
  exact tendsto_at_top_of_eventually_const h0,
end

/-- If `f 1 ≤ 1` and `f x ≠  0`, then `smoothing_seminorm_def f x` is the limit of
`smoothing_seminorm_seq f x`. -/
lemma smoothing_seminorm_def_is_limit_ne_zero (hf1 : f 1 ≤ 1) {x : R} (hx : f x ≠ 0) :
  tendsto ((smoothing_seminorm_seq f x)) at_top (𝓝 (smoothing_seminorm_def f x)) := 
begin
  simp only [smoothing_seminorm_def],
  set L := infi (λ (n : pnat), (f(x^(n : ℕ)))^(1/(n : ℝ))) with hL,
  have hL0 : 0 ≤ L := le_cinfi (λ x, rpow_nonneg_of_nonneg (map_nonneg _ _) _),
  rw metric.tendsto_at_top,
  intros ε hε,
  obtain ⟨m1, hm1⟩ := smoothing_seminorm_seq_has_limit_m f x hε,
  obtain ⟨m2, hm2⟩ : ∃ m : ℕ, ∀ (n ≥ m), (L + ε/2)^
    (-(((n % m1 : ℕ) : ℝ)/(n : ℝ)))*((f x) ^(n % m1)) ^ (1 / (n : ℝ)) - 1 ≤
    ε/(2 * (L + ε/2)),
  { have hε2 : 0 < ε/2 := half_pos hε,
    have hL2  := smoothing_seminorm_seq_has_limit_aux f hL0 hε2 (pnat.pos m1) hx,
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
    apply cinfi_le (smoothing_seminorm_seq_bdd f x), },
  refine ⟨lt_of_lt_of_le (neg_lt_zero.mpr hε) (sub_nonneg.mpr hL_le), _⟩,
  { suffices h : smoothing_seminorm_seq f x n < L + ε, 
    { rw tsub_lt_iff_left hL_le, exact h },
    by_cases hxn : f (x ^(n % m1)) = 0,
    { simp only [smoothing_seminorm_seq],
      nth_rewrite 0 ← nat.div_add_mod n m1,
      have hLε : 0 < L + ε := add_pos_of_nonneg_of_pos hL0 hε,
      apply lt_of_le_of_lt _ hLε,
      rw [pow_add, ← mul_zero ((f (x ^ ((m1 : ℕ) * (n / (m1 : ℕ))))) ^ (1/(n : ℝ))), 
        ← zero_rpow (nat.one_div_cast_ne_zero (pos_iff_ne_zero.mp hn0)), ← hxn,
          ← mul_rpow (map_nonneg f _) (map_nonneg f _)],
      exact rpow_le_rpow (map_nonneg f _) (map_mul_le_mul f _ _)
        (nat.one_div_cast_nonneg _) },
    { have hxn' : 0 < f (x ^ (n % ↑m1)) := lt_of_le_of_ne (map_nonneg _ _) (ne.symm hxn),
      simp only [smoothing_seminorm_seq],
      nth_rewrite 0 ← nat.div_add_mod n m1,
      have h : f (x ^ ((m1 : ℕ) * (n / (m1 : ℕ)))) ^ (1 / (n : ℝ))  ≤
        (f (x ^ (m1 : ℕ)) ^ (n / (m1 : ℕ))) ^ (1 / (n : ℝ)),
      { apply rpow_le_rpow (map_nonneg f _) _ (nat.one_div_cast_nonneg _),
        rw pow_mul,
        exact  map_pow_le_pow f (x^(m1 : ℕ)) 
          (pos_iff_ne_zero.mp (nat.div_pos (le_trans (le_max_left m1 m2) hn) (pnat.pos m1))) },
       have hL0' : 0 < L + ε / 2,
        { exact (add_pos_of_nonneg_of_pos hL0 (half_pos hε)), },
      have h1 : (f (x ^ (m1 : ℕ)) ^ (n / (m1 : ℕ))) ^ (1 / (n : ℝ))  <
        (L + ε/2) * ((L + ε/2) ^ -(((n % m1 : ℕ) : ℝ)/(n : ℝ))),
      { have hm10 : (m1 : ℝ) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_gt (pnat.pos m1)),
        rw [← rpow_lt_rpow_iff (real.rpow_nonneg_of_nonneg (map_nonneg f _) _) (le_of_lt hL0')
          (nat.cast_pos.mpr (pnat.pos m1)), ← rpow_mul (map_nonneg f _), ← coe_coe, 
          one_div_mul_cancel hm10, rpow_one] at hm1, 
        nth_rewrite 0 ← rpow_one (L + ε/2),
        have : (n : ℝ)/n = 1 := div_self (nat.cast_ne_zero.mpr (ne_of_gt hn0)),
        nth_rewrite 2 ← this, clear this,
        nth_rewrite 2 ← nat.div_add_mod n m1,
        have h_lt : 0 < ((n / m1 : ℕ) : ℝ) / (n : ℝ),
        { apply div_pos,
          { exact nat.cast_pos.mpr (nat.div_pos (le_trans (le_max_left _ _) hn) (pnat.pos m1)) },
          { exact nat.cast_pos.mpr hn0 }},
        rw [← rpow_nat_cast, ← rpow_add hL0', ← neg_div, div_add_div_same, nat.cast_add, 
          add_neg_cancel_right, nat.cast_mul, ← rpow_mul (map_nonneg f _), mul_one_div,
          mul_div_assoc, rpow_mul (le_of_lt hL0')],
        exact rpow_lt_rpow (map_nonneg f _) hm1 h_lt },
      have h2 : f (x ^(n % m1)) ^ (1 / (n : ℝ)) ≤ (f x ^(n % m1)) ^ (1 / (n : ℝ)),
      { by_cases hnm1 : n % m1 = 0,
        { simpa[hnm1, pow_zero] using 
            rpow_le_rpow (map_nonneg f _) hf1 (nat.one_div_cast_nonneg _) },
        { exact rpow_le_rpow (map_nonneg f _) (map_pow_le_pow f _ hnm1)
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
      have h4 : 0 < f (x ^ (n % ↑m1)) ^ (1 / (n : ℝ)) := rpow_pos_of_pos hxn' _,
      have h5 : 0 < (L + ε / 2) * (L + ε / 2) ^ -(↑(n % ↑m1) / (n : ℝ)) :=
      mul_pos hL0' (real.rpow_pos_of_pos hL0' _), 
    calc f (x ^ ((m1 : ℕ) * (n / (m1 : ℕ)) + n % m1)) ^ (1 / (n : ℝ)) = 
            f (x ^ ((m1 : ℕ) * (n /(m1 : ℕ))) * x ^(n % m1)) ^ (1 / (n : ℝ)) : by rw pow_add
      ... ≤ (f (x ^ ((m1 : ℕ) * (n / (m1 : ℕ)))) * f (x ^(n % m1))) ^ (1 / (n : ℝ)) : 
            rpow_le_rpow (map_nonneg f _) (map_mul_le_mul f _ _) (nat.one_div_cast_nonneg _) 
      ... = f (x ^ ((m1 : ℕ) * (n /(m1 : ℕ)))) ^ (1 / (n : ℝ)) * f (x ^(n % m1)) ^ (1 / (n : ℝ)) :
            mul_rpow (map_nonneg f _) (map_nonneg f _)
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

/-- If `f 1 ≤ 1`, then `smoothing_seminorm_def f x` is the limit of `smoothing_seminorm_seq f x`
  as `n` tends to infinity. -/
lemma smoothing_seminorm_def_is_limit (hf1 : f 1 ≤ 1) (x : R) :
  tendsto ((smoothing_seminorm_seq f x)) at_top (𝓝 (smoothing_seminorm_def f x)) :=
begin
  by_cases hx : f x = 0,
  { exact smoothing_seminorm_def_is_limit_zero f hx },
  { exact smoothing_seminorm_def_is_limit_ne_zero f hf1 hx }
end

/-- If `f 1 ≤ 1`, then `smoothing_seminorm_def f x` is nonnegative. -/
lemma smoothing_seminorm_nonneg (hf1 : f 1 ≤ 1) (x : R) : 0 ≤ smoothing_seminorm_def f x :=
begin
  apply ge_of_tendsto (smoothing_seminorm_def_is_limit f hf1 x),
  simp only [eventually_at_top, ge_iff_le],
  use 1,
  rintros n hn,
  simp only [smoothing_seminorm_seq],
  exact rpow_nonneg_of_nonneg (map_nonneg f _) _,
end

/-- If `f 1 ≤ 1`, then `smoothing_seminorm_def f 0 = 0`. -/
lemma smoothing_seminorm_zero (hf1 : f 1 ≤ 1) : smoothing_seminorm_def f 0 = 0 :=
begin
  apply tendsto_nhds_unique_of_eventually_eq (smoothing_seminorm_def_is_limit f hf1 0)
    tendsto_const_nhds,
  simp only [eventually_eq, eventually_at_top, ge_iff_le],
  use 1,
  intros n hn,
  simp only [smoothing_seminorm_seq],
  rw [zero_pow (nat.succ_le_iff.mp hn), map_zero, zero_rpow],
  apply one_div_ne_zero,
  exact nat.cast_ne_zero.mpr (nat.one_le_iff_ne_zero.mp hn), 
end

/-- If `f (-x) = f x`, the same holds for `smoothing_seminorm_def f`. -/
lemma smoothing_seminorm_neg (f_neg : ∀ x : R, f (-x) = f x) (x : R) : 
  smoothing_seminorm_def f (-x) = smoothing_seminorm_def f x :=
begin
  simp only [smoothing_seminorm_def, smoothing_seminorm_def],
  congr, ext n,
  rw neg_pow,
  cases neg_one_pow_eq_or R n with hpos hneg,
  { rw [hpos, one_mul] },
  { rw [hneg, neg_one_mul, f_neg], },
end

/-- If `f 1 ≤ 1`, then `smoothing_seminorm_def f` is submultiplicative. -/
lemma smoothing_seminorm_mul (hf1 : f 1 ≤ 1) (x y : R) : smoothing_seminorm_def f (x * y) ≤
  smoothing_seminorm_def f x * smoothing_seminorm_def f y :=
begin
  apply le_of_tendsto_of_tendsto' (smoothing_seminorm_def_is_limit f hf1 (x *y))
    (tendsto.mul (smoothing_seminorm_def_is_limit f hf1 x)
      (smoothing_seminorm_def_is_limit f hf1 y)),
  intro n,
  have hn : 0 ≤ 1 / (n : ℝ),
  { simp only [one_div, inv_nonneg, nat.cast_nonneg] },
  simp only [smoothing_seminorm_seq],
  rw [← mul_rpow (map_nonneg f _) (map_nonneg f _), mul_pow],
  exact rpow_le_rpow (map_nonneg f _) (map_mul_le_mul f _ _) hn,
end

/-- If `f 1 ≤ 1`, then `smoothing_seminorm_def f 1 ≤ 1`. -/
lemma smoothing_seminorm_one (hf1 : f 1 ≤ 1) : smoothing_seminorm_def f 1 ≤ 1 := 
begin
  apply le_of_tendsto (smoothing_seminorm_def_is_limit f hf1 (1 : R) ),
  simp only [eventually_at_top, ge_iff_le],
  use 1,
  rintros n hn,
  simp only [smoothing_seminorm_seq],
  rw [one_pow],
  conv_rhs{rw ← one_rpow (1/n : ℝ)},
  have hn1 : 0 < (1/n : ℝ),
  { have h01 : (0 : ℝ) < 1 := zero_lt_one,
    apply div_pos h01,
    rw [← nat.cast_zero, nat.cast_lt],
    exact (nat.succ_le_iff.mp hn) },
    exact (real.rpow_le_rpow_iff (map_nonneg f _) zero_le_one hn1).mpr hf1,
end

/-- For any `x` and any positive `n`, `smoothing_seminorm_def f x  ≤ f (x^(n : ℕ))^(1/n : ℝ)`. -/
lemma smoothing_seminorm_le_term (x : R) (n : pnat) : 
  smoothing_seminorm_def f x  ≤ f (x^(n : ℕ))^(1/n : ℝ) :=
cinfi_le (smoothing_seminorm_seq_bdd f x) _

/-- For all `x : R`, `smoothing_seminorm_def f x ≤ f x`. -/
lemma smoothing_seminorm_le (x : R) : smoothing_seminorm_def f x ≤ f x :=
begin
  convert smoothing_seminorm_le_term f x 1,
  simp only [positive.coe_one, algebra_map.coe_one, coe_coe, div_one, pow_one, rpow_one],
end

/- In this section, we prove that if `f` is nonarchimedean, then `smoothing_seminorm_def f` is
  nonarchimedean. -/
 section is_nonarchimedean

lemma exists_index_le (hna : is_nonarchimedean f) (x y : R) (n : ℕ) : 
  ∃ (m : ℕ) (hm : m ∈ finset.range (n + 1)), 
    (f ((x + y)^(n : ℕ))) ^(1/(n : ℝ)) ≤ (f (x ^ m) * f (y ^ (n - m : ℕ)))^(1/(n : ℝ)) :=
begin
  obtain ⟨m, hm_lt, hm⟩ := is_nonarchimedean_add_pow hna n x y,
  exact ⟨m, hm_lt, rpow_le_rpow (map_nonneg f _) hm (nat.one_div_cast_nonneg (n : ℕ))⟩,
end

/-- Auxiliary sequence for the proof that `smoothing_seminorm_def` is nonarchimedean. -/
def mu {x y : R} (hn : ∀ (n : ℕ), ∃ (m : ℕ) (hm : m ∈ finset.range (n + 1)), 
    (f ((x + y)^(n : ℕ))) ^(1/(n : ℝ)) ≤ (f (x ^ m) * f (y ^ (n - m : ℕ)))^(1/(n : ℝ))) :
  ℕ → ℕ := 
λ n, classical.some (hn n)

lemma mu_property {x y : R} (hn : ∀ (n : ℕ), ∃ (m : ℕ) (hm : m ∈ finset.range (n + 1)), 
    (f ((x + y)^(n : ℕ))) ^(1/(n : ℝ)) ≤ (f (x ^ m) * f (y ^ (n - m : ℕ)))^(1/(n : ℝ))) (n : ℕ) :
  f ((x + y)^(n : ℕ)) ^(1/(n : ℝ)) ≤ 
    (f (x ^ (mu f hn n)) * f (y ^ (n - (mu f hn n) : ℕ)))^(1/(n : ℝ)) := 
classical.some_spec (classical.some_spec (hn n))

lemma mu_le {x y : R} (hn : ∀ (n : ℕ), ∃ (m : ℕ) (hm : m ∈ finset.range (n + 1)), 
    (f ((x + y)^(n : ℕ))) ^(1/(n : ℝ)) ≤ (f (x ^ m) * f (y ^ (n - m : ℕ)))^(1/(n : ℝ))) (n : ℕ) :
  mu f hn n ≤ n :=
begin
  simp only [mu, ← nat.lt_succ_iff, ← finset.mem_range],
  exact classical.some (classical.some_spec (hn n)),   
end

lemma mu_bdd {x y : R} (hn : ∀ (n : ℕ), ∃ (m : ℕ) (hm : m ∈ finset.range (n + 1)), 
    (f ((x + y)^(n : ℕ))) ^(1/(n : ℝ)) ≤ (f (x ^ m) * f (y ^ (n - m : ℕ)))^(1/(n : ℝ))) (n : ℕ) : 
  (mu f hn n : ℝ)/n ∈ set.Icc (0 : ℝ) 1 :=
begin
  refine set.mem_Icc.mpr ⟨_, _⟩,
  { exact div_nonneg (nat.cast_nonneg (mu f hn n)) (nat.cast_nonneg n), },
  {by_cases hn0 : n = 0,
    { rw [hn0, nat.cast_zero, div_zero], exact zero_le_one, },
    { have hn' : 0 < (n : ℝ) := nat.cast_pos.mpr (nat.pos_of_ne_zero hn0),
      rw [div_le_one hn', nat.cast_le],
      exact mu_le _ _ _, }}
end

private lemma f_bdd_below (s : ℕ → ℕ) {x y : R} (hn : ∀ (n : ℕ), ∃ (m : ℕ) 
    (hm : m ∈ finset.range (n + 1)), (f ((x + y)^(n : ℕ))) ^(1/(n : ℝ)) ≤ 
    (f (x ^ m) * f (y ^ (n - m : ℕ)))^(1/(n : ℝ))) (a : ℝ) (φ: ℕ → ℕ) :
  bdd_below {a : ℝ | ∀ᶠ (n : ℝ) in map 
    (λ (n : ℕ), f x ^ (↑(s (φ n)) * (1 / (φ n : ℝ)))) at_top, n ≤ a} := 
begin
  use (0 : ℝ),
  simp only [mem_lower_bounds, eventually_map, eventually_at_top, ge_iff_le,
    set.mem_set_of_eq, forall_exists_index],
  intros r m hm,
  exact le_trans (real.rpow_nonneg_of_nonneg (map_nonneg f _) _) (hm m (le_refl _)),
end

private lemma f_bdd_above (hf1 : f 1 ≤ 1) {s : ℕ → ℕ} (hs : ∀ n : ℕ, s n ≤ n) (x : R) (φ : ℕ → ℕ) :
  bdd_above (set.range (λ (n : ℕ), f (x ^ s (φ n)) ^ (1 / (φ n : ℝ)))) := 
begin
  have hφ : ∀ n : ℕ, 0 ≤ 1 / (φ n : ℝ),
  { intro n,
    simp only [one_div, inv_nonneg, nat.cast_nonneg], },
  by_cases hx : f x ≤ 1,
  { use 1,
    simp only [mem_upper_bounds, set.mem_range, forall_exists_index,
      forall_apply_eq_imp_iff'],
    intros n,
    apply le_trans (real.rpow_le_rpow (map_nonneg _ _) (map_pow_le_pow' hf1 _ _) (hφ n)),
    rw [← rpow_nat_cast, ← rpow_mul (map_nonneg _ _), mul_one_div],
    exact rpow_le_one (map_nonneg _ _) hx 
      (div_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _)) },
  { use f x,
    simp only [mem_upper_bounds, set.mem_range, forall_exists_index, 
      forall_apply_eq_imp_iff'],
    intros n,
    apply le_trans (real.rpow_le_rpow (map_nonneg _ _) (map_pow_le_pow' hf1 _ _) (hφ n)),
    rw [← rpow_nat_cast, ← rpow_mul (map_nonneg _ _), mul_one_div],
    conv_rhs {rw ← rpow_one (f x)},
    rw rpow_le_rpow_left_iff (not_le.mp hx),
    exact div_le_one_of_le (nat.cast_le.mpr (hs (φ n))) (nat.cast_nonneg _) }
end

private lemma f_nonempty {s : ℕ → ℕ} (hs_le : ∀ n : ℕ, s n ≤ n) {x y : R} (hn : ∀ (n : ℕ), 
    ∃ (m : ℕ) (hm : m ∈ finset.range (n + 1)), (f ((x + y)^(n : ℕ))) ^(1/(n : ℝ)) ≤ 
    (f (x ^ m) * f (y ^ (n - m : ℕ)))^(1/(n : ℝ))) (φ : ℕ → ℕ) :
  {a : ℝ | ∀ᶠ (n : ℝ) in map
    (λ (n : ℕ), f x ^ (↑(s (φ n)) * (1 / (φ n : ℝ)))) at_top, n ≤ a}.nonempty :=
begin
  by_cases hfx : f x < 1,
  { use 1,
    simp only [eventually_map, eventually_at_top, ge_iff_le, set.mem_set_of_eq],
    use 0,
    intros b hb,
    exact rpow_le_one (map_nonneg _ _) (le_of_lt hfx) 
        (mul_nonneg (nat.cast_nonneg _)  (one_div_nonneg.mpr (nat.cast_nonneg _))) },
  { use f x,
    simp only [eventually_map, eventually_at_top, ge_iff_le, set.mem_set_of_eq],
    use 0,
    intros b hb,
    nth_rewrite 1 ← rpow_one (f x),
    apply rpow_le_rpow_of_exponent_le (not_lt.mp hfx),
    rw [mul_one_div],
    exact div_le_one_of_le (nat.cast_le.mpr (hs_le (φ b))) (nat.cast_nonneg _) }
end

private lemma f_limsup_le_one {s : ℕ → ℕ} (hs_le : ∀ n : ℕ, s n ≤ n) {x y : R} (hn : ∀ (n : ℕ),
    ∃ (m : ℕ) (hm : m ∈ finset.range (n + 1)), (f ((x + y)^(n : ℕ))) ^(1/(n : ℝ)) ≤ 
    (f (x ^ m) * f (y ^ (n - m : ℕ)))^(1/(n : ℝ))) {φ : ℕ → ℕ}
  (hφ_lim: tendsto ((λ (n : ℕ), ↑(s n) / (n : ℝ)) ∘ φ) at_top (𝓝 0)) :
  limsup (λ (n : ℕ), f x ^ ((s (φ n) : ℝ) * (1 / (φ n : ℝ)))) at_top ≤ 1 :=
begin
  simp only [limsup, Limsup],
  rw cInf_le_iff,
  { intros c hc_bd,
    simp only [mem_lower_bounds, eventually_map, eventually_at_top, ge_iff_le, 
      set.mem_set_of_eq, forall_exists_index] at hc_bd,
    by_cases hfx : f x < 1,
    { apply hc_bd (1 : ℝ) 0,
      rintros b -,
      exact rpow_le_one (map_nonneg _ _) (le_of_lt hfx) 
        (mul_nonneg (nat.cast_nonneg _)  (one_div_nonneg.mpr (nat.cast_nonneg _))), },
    { have hf_lim : tendsto (λ (n : ℕ), f x ^ (↑(s(φ n)) * (1 / (φ n : ℝ)))) 
          at_top (𝓝 1), 
        { nth_rewrite 0 ← rpow_zero (f x),
          refine tendsto.rpow tendsto_const_nhds _ 
            (or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one (not_lt.mp hfx)))),
          { convert hφ_lim,
            simp only [function.comp_app, mul_one_div] }},
        rw tendsto_at_top_nhds at hf_lim,
      apply le_of_forall_pos_le_add,
      intros ε hε,
      have h1 : (1 : ℝ) ∈ set.Ioo 0 (1 + ε),
      { simp only [set.mem_Ioo, zero_lt_one, lt_add_iff_pos_right, true_and, hε], },
      obtain ⟨k, hk⟩ := hf_lim (set.Ioo (0 : ℝ) (1 + ε)) h1 is_open_Ioo,
      exact hc_bd (1 + ε) k (λ b hb, le_of_lt (set.mem_Ioo.mp (hk b hb)).2), }},
  { exact f_bdd_below f s hn (0 : ℝ) φ },
  { exact f_nonempty f hs_le hn φ  }
end

lemma smoothing_seminorm_def_is_limit_comp (hf1 : f 1 ≤ 1) (x : R) {φ : ℕ → ℕ}
  (hφ_mono : strict_mono φ) :
  tendsto (λ (n : ℕ), (f (x ^ (φ n)))^(1/(φ n) : ℝ)) at_top (𝓝 (smoothing_seminorm_def f x)) :=
begin
  have hφ_lim' : tendsto φ at_top at_top,
  { exact strict_mono.tendsto_at_top hφ_mono },
  exact (smoothing_seminorm_def_is_limit f  hf1 x).comp hφ_lim',
end

lemma limsup_mu_le (hf1 : f 1 ≤ 1) {s : ℕ → ℕ} (hs_le : ∀ n : ℕ, s n ≤ n) {x y : R}
  (hn : ∀ (n : ℕ), ∃ (m : ℕ) (hm : m ∈ finset.range (n + 1)), 
    (f ((x + y)^(n : ℕ))) ^(1/(n : ℝ)) ≤ (f (x ^ m) * f (y ^ (n - m : ℕ)))^(1/(n : ℝ))) {a : ℝ} 
  (a_in: a ∈ set.Icc (0 : ℝ) 1) {φ: ℕ → ℕ} (hφ_mono: strict_mono φ)
  (hφ_lim: tendsto ((λ (n : ℕ), ↑(s n) / ↑n) ∘ φ) at_top (𝓝 a)) :
  limsup (λ (n : ℕ), (f (x ^ (s (φ n))))^(1/(φ n : ℝ))) at_top ≤
    (smoothing_seminorm_def f x)^a :=
begin
  by_cases ha : a = 0,
  { rw ha at hφ_lim,
    calc limsup (λ (n : ℕ), f (x ^ s (φ n)) ^ (1 / (φ n : ℝ))) at_top ≤ 
      limsup (λ (n : ℕ), f x ^ ((s (φ n) : ℝ) * (1 / (φ n : ℝ)))) at_top : 
      begin
        apply cInf_le_cInf,
        { use (0 : ℝ),
          simp only [mem_lower_bounds, eventually_map, eventually_at_top, ge_iff_le,
            set.mem_set_of_eq, forall_exists_index],
          intros r m hm,
          exact le_trans (real.rpow_nonneg_of_nonneg (map_nonneg f _) _) (hm m (le_refl _)) },
        { exact f_nonempty f hs_le hn φ, },
        { intros b hb,
          simp only [eventually_map, eventually_at_top, ge_iff_le, 
            set.mem_set_of_eq] at hb ⊢,
          obtain ⟨m, hm⟩ := hb,
          use m,
          intros k hkm,
          apply le_trans _ (hm k hkm),
          rw [real.rpow_mul (map_nonneg f x), rpow_nat_cast],
          exact rpow_le_rpow (map_nonneg f _) (map_pow_le_pow' hf1 x _) 
            (one_div_nonneg.mpr (nat.cast_nonneg _)), }
      end
    ... ≤ 1 : f_limsup_le_one f hs_le hn hφ_lim
    ... = smoothing_seminorm_def f x ^ a : by rw [ha, rpow_zero] },
  { have ha_pos : 0 < a := lt_of_le_of_ne a_in.1 (ne.symm ha),
    have h_eq : (λ (n : ℕ), (f (x ^ s (φ n))^ (1 / (s (φ n) : ℝ))) ^ ((s (φ n) : ℝ)/(φ n : ℝ)))
      =ᶠ[at_top] (λ (n : ℕ), f (x ^ s (φ n)) ^ (1 / (φ n : ℝ))),
    { have h : (λ (n : ℕ),  (1 : ℝ) / (s (φ n) : ℝ) * (s (φ n) : ℝ)) =ᶠ[at_top] 1,
      { convert div_mul_eventually_cancel 1 
          (tendsto.num hφ_mono.tendsto_at_top ha_pos hφ_lim);
        { ext n, simp only [pi.one_apply, algebra_map.coe_one], }},
      simp_rw [← rpow_mul (map_nonneg f _), mul_div],
      exact (eventually_eq.comp₂ eventually_eq.rfl pow (h.div eventually_eq.rfl)) },
    exact le_of_eq (tendsto.limsup_eq (tendsto.congr' h_eq
      (tendsto.rpow ((smoothing_seminorm_def_is_limit f hf1 x).comp
      (tendsto.num hφ_mono.tendsto_at_top ha_pos hφ_lim)) hφ_lim (or.inr ha_pos)))) }
end

/-- If `f 1 ≤ 1` and `f` is nonarchimedean, then `smoothing_seminorm_def` is nonarchimedean. -/
lemma smoothing_seminorm_is_nonarchimedean (hf1 : f 1 ≤ 1) (hna : is_nonarchimedean f) :
  is_nonarchimedean (smoothing_seminorm_def f) :=
begin
  intros x y,
  have hn : ∀ (n : ℕ), ∃ (m : ℕ) (hm : m ∈ finset.range (n + 1)), 
    (f ((x + y)^(n : ℕ))) ^(1/(n : ℝ)) ≤ (f (x ^ m) * f (y ^ (n - m : ℕ)))^(1/(n : ℝ)) :=
  λ n, exists_index_le f hna x y n, 
  set mu : ℕ → ℕ := λ n, mu f hn n with hmu,
  set nu : ℕ → ℕ := λ n, n - (mu n) with hnu,
  have hmu_le : ∀ n : ℕ, mu n ≤ n := λ n, mu_le f hn n,
  have hmu_bdd : ∀ n : ℕ, (mu n : ℝ)/n ∈ set.Icc (0 : ℝ) 1 := λ n, mu_bdd f hn n,
  have hs : metric.bounded (set.Icc (0 : ℝ) 1) := metric.bounded_Icc 0 1,
  obtain ⟨a, a_in, φ, hφ_mono, hφ_lim⟩ := tendsto_subseq_of_bounded hs hmu_bdd,
  rw closure_Icc at a_in,
  set b := 1 - a with hb,
  have hb_lim : tendsto ((λ (n : ℕ), ↑(nu n) / ↑n) ∘ φ) at_top (𝓝 b),
  { apply tendsto.congr' _ (tendsto.const_sub 1 hφ_lim),
    simp only [eventually_eq, function.comp_app, eventually_at_top, ge_iff_le],
    use 1,
    intros m hm,
    have h0 : (φ m : ℝ ) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_gt (lt_of_le_of_lt (zero_le _) 
      (hφ_mono (nat.pos_of_ne_zero (nat.one_le_iff_ne_zero.mp hm))))),
    rw [← div_self h0, ← sub_div],
    simp only [hnu],
    rw nat.cast_sub (hmu_le _) },

  have b_in : b ∈ set.Icc (0 : ℝ) 1 := sub_mem_closure a_in,
  have hnu_le : ∀ n : ℕ, nu n ≤ n := λ n, by simp only [hnu, tsub_le_self],

  have hx : limsup (λ (n : ℕ), (f (x ^ (mu (φ n))))^(1/(φ n : ℝ))) at_top ≤
    (smoothing_seminorm_def f x)^a,
  { exact limsup_mu_le f hf1 hmu_le hn a_in hφ_mono hφ_lim },
  have hy : limsup (λ (n : ℕ), (f (y ^ (nu (φ n))))^(1/(φ n : ℝ))) at_top ≤
    (smoothing_seminorm_def f y)^b,
  { exact limsup_mu_le f hf1 hnu_le (exists_index_le f hna y x) b_in hφ_mono hb_lim },

  have hxy : limsup (λ (n : ℕ), 
    ((f (x ^ (mu (φ n))))^(1/(φ n : ℝ)) * (f (y ^ (nu (φ n))))^(1/(φ n : ℝ)))) at_top ≤
    (smoothing_seminorm_def f x)^a * (smoothing_seminorm_def f y)^b ,
  { have hxy' : limsup (λ (n : ℕ), 
    ((f (x ^ (mu (φ n))))^(1/(φ n : ℝ)) * (f (y ^ (nu (φ n))))^(1/(φ n : ℝ)))) at_top ≤ 
      (limsup (λ (n : ℕ), (f (x ^ (mu (φ n))))^(1/(φ n : ℝ))) at_top) *
      (limsup (λ (n : ℕ), (f (y ^ (nu (φ n))))^(1/(φ n : ℝ))) at_top),
    { exact limsup_mul_le (f_bdd_above f hf1 hmu_le x φ)
        (λ n, rpow_nonneg_of_nonneg (map_nonneg _ _) _) (f_bdd_above f hf1 hnu_le y φ)
        (λ n, rpow_nonneg_of_nonneg (map_nonneg _ _) _) },
    have h_bdd : is_bounded_under has_le.le at_top 
      (λ (n : ℕ), f (y ^ nu (φ n)) ^ (1 / (φ n : ℝ))),
    { exact is_bdd_under f hf1 hnu_le φ },
    exact le_trans hxy' (mul_le_mul hx hy 
      (limsup_nonneg_of_nonneg h_bdd (λ m, rpow_nonneg_of_nonneg (map_nonneg _ _) _)) 
      (real.rpow_nonneg_of_nonneg (smoothing_seminorm_nonneg f hf1 x) _)) },

  conv_lhs { simp only [smoothing_seminorm_def], },
  apply le_of_forall_sub_le,
  intros ε hε,
  rw sub_le_iff_le_add, 
  have h_mul : (smoothing_seminorm_def f x)^a * (smoothing_seminorm_def f y)^b + ε ≤
    max (smoothing_seminorm_def f x) (smoothing_seminorm_def f y) + ε,
  { rw max_def,
    split_ifs with h,
    { rw [add_le_add_iff_right],
      apply le_trans (mul_le_mul_of_nonneg_right (real.rpow_le_rpow 
        (smoothing_seminorm_nonneg f hf1 _) h a_in.1)
        (real.rpow_nonneg_of_nonneg (smoothing_seminorm_nonneg f hf1 _) _)),
      rw [hb, ← rpow_add_of_nonneg (smoothing_seminorm_nonneg f hf1 _) a_in.1
        (sub_nonneg.mpr a_in.2), add_sub, add_sub_cancel', rpow_one], },
    { rw [add_le_add_iff_right],
      apply le_trans (mul_le_mul_of_nonneg_left (real.rpow_le_rpow 
        (smoothing_seminorm_nonneg f hf1 _) (le_of_lt (not_le.mp h)) b_in.1)
        (real.rpow_nonneg_of_nonneg (smoothing_seminorm_nonneg f hf1 _) _)),
      rw [hb, ← rpow_add_of_nonneg (smoothing_seminorm_nonneg f hf1 _) a_in.1
        (sub_nonneg.mpr a_in.2), add_sub, add_sub_cancel', rpow_one] }},
  apply le_trans _ h_mul,
  have hex : ∃ n : pnat,
    (f (x ^ (mu (φ n))))^(1/(φ n : ℝ)) * f (y ^ (nu (φ n)))^(1/(φ n : ℝ)) <
    (smoothing_seminorm_def f x)^a * (smoothing_seminorm_def f y)^b + ε,
  { exact exists_lt_of_limsup_le (real.range_bdd_above_mul (f_bdd_above f hf1 hmu_le _ _) 
      (λ n, rpow_nonneg_of_nonneg (map_nonneg _ _) _) (f_bdd_above f hf1 hnu_le _ _)
      (λ n, rpow_nonneg_of_nonneg (map_nonneg _ _) _)).is_bounded_under hxy hε, },
  obtain ⟨N, hN⟩ := hex,
  apply le_trans (cinfi_le (smoothing_seminorm_seq_bdd f _) 
    ⟨φ N, lt_of_le_of_lt (zero_le (φ 0)) (hφ_mono.lt_iff_lt.mpr N.pos)⟩),
  apply le_trans _ hN.le,
  simp only [pnat.mk_coe, coe_coe, hnu, ← mul_rpow (map_nonneg f _) (map_nonneg f _)],
  exact mu_property f hn (φ N),
end

end is_nonarchimedean

/-- If `f 1 ≤ 1` and `f` is nonarchimedean, then `smoothing_seminorm_def` is a ring seminorm. -/
def smoothing_seminorm (hf1 : f 1 ≤ 1) (hna : is_nonarchimedean f) : ring_seminorm R :=
{ to_fun    := smoothing_seminorm_def f,
  map_zero' := smoothing_seminorm_zero f hf1,
  add_le'   := add_le_of_is_nonarchimedean (smoothing_seminorm_nonneg f hf1)
    (smoothing_seminorm_is_nonarchimedean f hf1 hna),
  neg'      := smoothing_seminorm_neg f (map_neg_eq_map f),
  mul_le'   := smoothing_seminorm_mul f hf1 }

/-- If `f 1 ≤ 1` and `f` is nonarchimedean, then `smoothing_seminorm f hf1 hna 1 ≤ 1`. -/
lemma smoothing_seminorm_is_seminorm_is_norm_le_one_class (hf1 : f 1 ≤ 1)
  (hna : is_nonarchimedean f) : smoothing_seminorm f hf1 hna 1 ≤ 1 := 
smoothing_seminorm_one f hf1

/-- If `f 1 ≤ 1` and `f` is nonarchimedean, then `smoothing_seminorm_def f` is
  power-multiplicative. -/
lemma smoothing_seminorm_is_pow_mul (hf1 : f 1 ≤ 1) : is_pow_mul (smoothing_seminorm_def f) :=
begin
  intros x m hm,
  simp only [smoothing_seminorm_def],
  have hlim : tendsto (λ n, smoothing_seminorm_seq  f x (m*n)) at_top
    (𝓝 (smoothing_seminorm_def f  x )),
  { refine tendsto.comp (smoothing_seminorm_def_is_limit f hf1 x) _,
    apply tendsto_at_top_at_top_of_monotone,
    { intros n k hnk, exact mul_le_mul_left' hnk m, },
    { rintro n, use n, exact le_mul_of_one_le_left' hm, }},
  apply tendsto_nhds_unique _ (tendsto.pow hlim m),
  have h_eq : ∀ (n : ℕ), smoothing_seminorm_seq f x (m * n) ^ m =
    smoothing_seminorm_seq f (x^m) n,
  { have hm' : (m : ℝ) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hm)), 
    intro n,
    simp only [smoothing_seminorm_seq],
    rw [pow_mul, ← rpow_nat_cast, ← rpow_mul (map_nonneg f _), nat.cast_mul, 
      ← one_div_mul_one_div, mul_comm (1 / (m : ℝ)), mul_assoc, one_div_mul_cancel hm', mul_one] },
  simp_rw h_eq,
  exact smoothing_seminorm_def_is_limit f hf1 _
end

/-- If `f 1 ≤ 1` and `∀ (1 ≤ n), f (x ^ n) = f x ^ n`, then `smoothing_seminorm_def f x = f x`. -/
lemma smoothing_seminorm_of_pow_mult (hf1 : f 1 ≤ 1) {x : R} 
  (hx : ∀ (n : ℕ) (hn : 1 ≤ n), f (x ^ n) = f x ^ n) : smoothing_seminorm_def f x = f x :=
begin
  apply tendsto_nhds_unique_of_eventually_eq (smoothing_seminorm_def_is_limit f hf1 x)
    tendsto_const_nhds,
  simp only [eventually_eq, eventually_at_top, ge_iff_le],
  use 1,
  intros n hn,
  simp only [smoothing_seminorm_seq],
  have hn0 : (n : ℝ) ≠ 0 := nat.cast_ne_zero.mpr (nat.one_le_iff_ne_zero.mp hn),
  rw [hx n hn, ← rpow_nat_cast, ← rpow_mul (map_nonneg f _), mul_one_div_cancel hn0,
    rpow_one],
end

/-- If `f 1 ≤ 1` and `∀ y : R, f (x * y) = f x * f y`, then `smoothing_seminorm_def f x = f x`. -/
lemma smoothing_seminorm_apply_of_is_mul' (hf1 : f 1 ≤ 1) {x : R}
  (hx : ∀ y : R, f (x * y) = f x * f y) : smoothing_seminorm_def f x = f x :=
begin
  apply tendsto_nhds_unique_of_eventually_eq (smoothing_seminorm_def_is_limit f hf1 x)
    tendsto_const_nhds,
  simp only [eventually_eq, eventually_at_top, ge_iff_le],
  use 1,
  intros n hn,
  simp only [smoothing_seminorm_seq],
  by_cases hx0 : f x = 0,
  { have hxn : f (x ^ n) = 0,
    { apply le_antisymm _ (map_nonneg f _),
      apply le_trans (map_pow_le_pow f x (nat.one_le_iff_ne_zero.mp hn)),
      rw [hx0, zero_pow (lt_of_lt_of_le zero_lt_one hn)], },
    rw [hx0, hxn, zero_rpow (nat.one_div_cast_ne_zero (nat.one_le_iff_ne_zero.mp hn))] },
  { have h1 : f 1 = 1,
    { rw [← mul_right_inj' hx0, ← hx 1, mul_one, mul_one] },
    have hn0 : (n : ℝ) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hn)),
    rw [← mul_one (x ^ n), is_mul_pow_of_is_mul f hx, ← rpow_nat_cast, h1, mul_one,
      ← rpow_mul (map_nonneg f _), mul_one_div_cancel hn0, rpow_one] },
end

/-- If `f 1 ≤ 1`, `f` is nonarchimedean, and `∀ y : R, f (x * y) = f x * f y`, then
  `smoothing_seminorm f hf1 hna x = f x`. -/
lemma smoothing_seminorm_apply_of_is_mul (hf1 : f 1 ≤ 1) (hna : is_nonarchimedean f)  {x : R} 
  (hx : ∀ y : R, f (x * y) = f x * f y) :
  smoothing_seminorm f hf1 hna x = f x :=
smoothing_seminorm_apply_of_is_mul' f hf1 hx

/-- If `f 1 ≤ 1`, and `x` is multiplicative for `f`, then it is multiplicative for 
  `smoothing_seminorm_def`. -/
lemma smoothing_seminorm_of_mul' (hf1 : f 1 ≤ 1) {x : R} (hx : ∀ (y : R), f (x * y) = f x * f y)
  (y : R) : smoothing_seminorm_def f (x * y) = 
    smoothing_seminorm_def f x * smoothing_seminorm_def f y :=
begin
  have hlim : tendsto (λ n, f x * smoothing_seminorm_seq f y n) at_top
    (𝓝 (smoothing_seminorm_def f x * smoothing_seminorm_def f y)),
  { rw [smoothing_seminorm_apply_of_is_mul' f hf1 hx],
    exact tendsto.const_mul _ (smoothing_seminorm_def_is_limit f hf1 y), },
  apply tendsto_nhds_unique_of_eventually_eq (smoothing_seminorm_def_is_limit f hf1 (x * y))
    hlim,
  simp only [eventually_eq, eventually_at_top, ge_iff_le],
  use 1,
  intros n hn1,
  have hn0 : (n : ℝ) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hn1)),
  simp only [smoothing_seminorm_seq],
  rw [mul_pow, is_mul_pow_of_is_mul  f hx, mul_rpow (pow_nonneg (map_nonneg f _) _)
    (map_nonneg f _), ← rpow_nat_cast, ← rpow_mul (map_nonneg f _),
    mul_one_div_cancel hn0, rpow_one]
end

/-- If `f 1 ≤ 1`, `f` is nonarchimedean, and `x` is multiplicative for `f`, then `x` is
  multiplicative for `smoothing_seminorm`. -/
lemma smoothing_seminorm_of_mul (hf1 : f 1 ≤ 1) (hna : is_nonarchimedean f) {x : R}
  (hx : ∀ (y : R), f (x * y) = f x * f y) (y : R) : smoothing_seminorm f hf1 hna (x * y) = 
    smoothing_seminorm f hf1 hna x * smoothing_seminorm f hf1 hna y :=
smoothing_seminorm_of_mul' f hf1 hx y

end smoothing_seminorm