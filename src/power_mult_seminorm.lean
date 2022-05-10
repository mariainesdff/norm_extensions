import filter
import seminormed_rings
import analysis.special_functions.pow

noncomputable theory

open_locale topological_space

variables {α : Type*} [comm_ring α] (c : α) (f : α → nnreal) (hf1 : is_norm_le_one_class f)
  (hc : 0 ≠ f c) (hsn : is_seminorm f) (hpm : is_pow_mult f)

def c_seminorm_seq (x : α) : ℕ → nnreal :=
λ n, (f (x * c^n))/((f c)^n)

lemma c_seminorm_is_bounded (x : α) :
  bdd_below (set.range (c_seminorm_seq c f x)) := 
begin
  use 0,
  rw mem_lower_bounds,
  intros r hr,
  obtain ⟨n, hn⟩ := hr,
  rw ← hn,
  exact zero_le',
end

variable {f}

lemma c_seminorm_seq_zero (hf : f 0 = 0) : 
  c_seminorm_seq c f 0 = 0 := 
begin
  simp only [c_seminorm_seq],
  ext n,
  rw [zero_mul, hf, zero_div],
  refl,
end

/- lemma c_seminorm_seq_nonneg (x : α) (n : ℕ) : 0 ≤ c_seminorm_seq c f x n := zero_le'
 -/

variable {c}

include hc hpm

lemma c_seminorm_seq_one (n : ℕ) (hn : 1 ≤ n) : 
  c_seminorm_seq c f 1 n = 1 := 
begin
  simp only [c_seminorm_seq],
  rw [one_mul, hpm _ hn, div_self (pow_ne_zero n (ne.symm hc))],
end

include hf1 include hsn

lemma c_seminorm_seq_antitone (x : α) :
  antitone (c_seminorm_seq c f x) := 
begin
  intros m n hmn,
  simp only [c_seminorm_seq],
  nth_rewrite 0 ← nat.add_sub_of_le hmn,
  rw [pow_add, ← mul_assoc],
  apply le_trans ((div_le_div_right₀ (pow_ne_zero _ (ne.symm hc))).mpr (hsn.mul _ _)),
  by_cases heq : m = n,
  { have : n - m = 0,
    { rw heq, exact nat.sub_self n, },
    rw [this, heq, div_le_div_right₀ (pow_ne_zero _ (ne.symm hc)), pow_zero],
    conv_rhs{rw ← mul_one (f (x * c ^ n))},
    exact mul_le_mul' (le_refl _) hf1 },
  { have h1 : 1 ≤ n - m,
    { rw [nat.one_le_iff_ne_zero, ne.def, nat.sub_eq_zero_iff_le, not_le],
    exact lt_of_le_of_ne hmn heq,},
    rw [hpm c h1, mul_div_assoc, div_eq_mul_inv, pow_sub₀ _ (ne.symm hc) hmn, mul_assoc,
      mul_comm (f c ^ m)⁻¹, ← mul_assoc (f c ^ n), mul_inv_cancel (pow_ne_zero n (ne.symm hc)),
      one_mul, div_eq_mul_inv], }
end

def c_seminorm_seq_lim (x : α) : nnreal :=
classical.some (nnreal.tendsto_of_is_bounded_antitone (c_seminorm_is_bounded c f x) 
  (c_seminorm_seq_antitone hf1 hc hsn hpm x))

lemma c_seminorm_seq_lim_is_limit (x : α) : filter.tendsto ((c_seminorm_seq c f x)) filter.at_top
  (𝓝 (c_seminorm_seq_lim hf1 hc hsn hpm x)) :=
classical.some_spec (nnreal.tendsto_of_is_bounded_antitone (c_seminorm_is_bounded c f x) 
  (c_seminorm_seq_antitone hf1 hc hsn hpm x))

def c_seminorm : α → nnreal := λ x, c_seminorm_seq_lim hf1 hc hsn hpm x

lemma c_seminorm_zero : c_seminorm hf1 hc hsn hpm 0 = 0 :=
tendsto_nhds_unique (c_seminorm_seq_lim_is_limit hf1 hc hsn hpm 0) 
  (by simpa [c_seminorm_seq_zero c hsn.zero] using tendsto_const_nhds)


lemma c_seminorm_is_norm_one_class : is_norm_one_class (c_seminorm hf1 hc hsn hpm) :=
begin
  apply tendsto_nhds_unique_of_eventually_eq (c_seminorm_seq_lim_is_limit hf1 hc hsn hpm 1)
    tendsto_const_nhds,
  simp only [filter.eventually_eq, filter.eventually_at_top, ge_iff_le],
  exact ⟨1,  c_seminorm_seq_one hc hpm⟩,
end

lemma c_seminorm_mul (x y : α) :
  c_seminorm hf1 hc hsn hpm (x * y) ≤ c_seminorm hf1 hc hsn hpm x * c_seminorm hf1 hc hsn hpm y :=
begin
  have hlim : filter.tendsto (λ n, c_seminorm_seq c f (x * y) (2 *n)) filter.at_top
    (𝓝 (c_seminorm_seq_lim hf1 hc hsn hpm (x * y) )),
  { refine filter.tendsto.comp (c_seminorm_seq_lim_is_limit hf1 hc hsn hpm (x * y)) _,
    apply filter.tendsto_at_top_at_top_of_monotone,
    { intros n m hnm, simp only [mul_le_mul_left, nat.succ_pos', hnm], },
    { rintro n, use n, linarith, }},
  apply le_of_tendsto_of_tendsto' hlim (filter.tendsto.mul
    (c_seminorm_seq_lim_is_limit hf1 hc hsn hpm x) (c_seminorm_seq_lim_is_limit hf1 hc hsn hpm y)),
  intro n,
  simp only [c_seminorm_seq],
  rw [div_mul_div_comm₀, ← pow_add, two_mul, div_le_div_right₀ (pow_ne_zero _ (ne.symm hc)),
    pow_add, ← mul_assoc, mul_comm (x * y), ← mul_assoc, mul_assoc, mul_comm (c^n)],
  exact hsn.mul (x * c ^ n) (y * c ^ n), 
end

/- lemma c_seminorm_nonneg (hc : 0 ≠ f c) (hsn : is_seminorm f) (hpm : is_pow_mult f) (x : α):
  0 ≤ c_seminorm hc hsn hpm x :=
begin
  simp only [c_seminorm],
  apply ge_of_tendsto (c_seminorm_seq_lim_is_limit hc hsn hpm x),
  simp only [filter.eventually_at_top, ge_iff_le],
  use 0,
  rintro n -,
  exact c_seminorm_seq_nonneg c hsn.nonneg x n,
end -/

lemma c_seminorm_is_seminorm :
  is_seminorm (c_seminorm hf1 hc hsn hpm)  :=
{ zero   := c_seminorm_zero hf1 hc hsn hpm,
  mul    := c_seminorm_mul hf1 hc hsn hpm/- ,
  one    := le_of_eq (c_seminorm_is_norm_one_class hc hsn hpm) -/  }

lemma c_seminorm_is_seminorm' :
  is_norm_le_one_class (c_seminorm hf1 hc hsn hpm) :=
le_of_eq (c_seminorm_is_norm_one_class hf1 hc hsn hpm) 

lemma c_seminorm_is_nonarchimedean (hna : is_nonarchimedean f) :
  is_nonarchimedean (c_seminorm hf1 hc hsn hpm)  :=
begin
  intros x y,
  apply le_of_tendsto_of_tendsto' (c_seminorm_seq_lim_is_limit hf1 hc hsn hpm (x + y))
    (filter.tendsto.max (c_seminorm_seq_lim_is_limit hf1 hc hsn hpm x)
    (c_seminorm_seq_lim_is_limit hf1 hc hsn hpm y)),
  intro n,
  have hmax : f ((x + y) * c ^ n) ≤ max (f (x * c ^ n)) (f (y * c ^ n)),
  { rw add_mul, exact hna _ _ },
  rw le_max_iff at hmax ⊢,
  cases hmax; [left, right];
  exact (div_le_div_right₀ (pow_ne_zero _ (ne.symm hc))).mpr hmax,
end

lemma c_seminorm_is_pow_mult : is_pow_mult (c_seminorm hf1 hc hsn hpm) :=
begin
  intros x m hm,
  simp only [c_seminorm],
  have hpow := filter.tendsto.pow (c_seminorm_seq_lim_is_limit hf1 hc hsn hpm x) m,
  have hlim : filter.tendsto (λ n, c_seminorm_seq c f (x^m) (m*n)) filter.at_top
    (𝓝 (c_seminorm_seq_lim hf1 hc hsn hpm (x^m) )),
  { refine filter.tendsto.comp (c_seminorm_seq_lim_is_limit hf1 hc hsn hpm (x^m)) _,
    apply filter.tendsto_at_top_at_top_of_monotone,
    { intros n k hnk, exact mul_le_mul_left' hnk m, },
    { rintro n, use n, exact le_mul_of_one_le_left' hm, }},
  apply tendsto_nhds_unique hlim,
  convert filter.tendsto.pow (c_seminorm_seq_lim_is_limit hf1 hc hsn hpm x) m,
  ext n,
  simp only [c_seminorm_seq],
  rw [div_pow, ← hpm _ hm, ← pow_mul, mul_pow, ← pow_mul, mul_comm m n],
end

lemma c_seminorm_le_seminorm (x : α) : c_seminorm hf1 hc hsn hpm x ≤ f x :=
begin
  apply le_of_tendsto (c_seminorm_seq_lim_is_limit hf1 hc hsn hpm x),
  simp only [filter.eventually_at_top, ge_iff_le],
  use 1,
  rintros n hn,
  apply le_trans ((div_le_div_right₀ (pow_ne_zero _ (ne.symm hc))).mpr (hsn.mul _ _)),
  rw [hpm c hn, mul_div_assoc, div_self (pow_ne_zero n hc.symm), mul_one],
end

lemma c_seminorm_apply_of_is_mult {x : α} (hx : ∀ y : α, f (x * y) = f x * f y) :
  c_seminorm hf1 hc hsn hpm x = f x :=
begin
  have hlim : filter.tendsto (c_seminorm_seq c f x) filter.at_top (𝓝 (f x)),
  { have hseq : c_seminorm_seq c f x = λ n, f x,
    { ext n,
      by_cases hn : n = 0,
      { simp only [c_seminorm_seq], 
        rw [hn, pow_zero, pow_zero, mul_one, div_one], },
      { simp only [c_seminorm_seq],
        rw [hx (c ^n), hpm _ (nat.one_le_iff_ne_zero.mpr hn), mul_div_assoc,
          div_self (pow_ne_zero n hc.symm), mul_one], }},
    simpa [hseq] using tendsto_const_nhds, },
  exact tendsto_nhds_unique (c_seminorm_seq_lim_is_limit hf1 hc hsn hpm x) hlim,
end

lemma c_seminorm_is_mult_of_is_mult {x : α} (hx : ∀ y : α, f (x * y) = f x * f y) (y : α) :
  c_seminorm hf1 hc hsn hpm (x * y) = c_seminorm hf1 hc hsn hpm x * c_seminorm hf1 hc hsn hpm y :=
begin
  have hlim : filter.tendsto (c_seminorm_seq c f (x * y)) filter.at_top
    (𝓝 (c_seminorm hf1 hc hsn hpm x * c_seminorm hf1 hc hsn hpm y)),
  { rw c_seminorm_apply_of_is_mult hf1 hc hsn hpm hx,
    have hseq : c_seminorm_seq c f (x * y) = λ n, f x * c_seminorm_seq c f y n,
    { ext n,
      simp only [c_seminorm_seq],
      rw [mul_assoc, hx, mul_div_assoc], },
    simpa [hseq] using filter.tendsto.const_mul _ (c_seminorm_seq_lim_is_limit hf1 hc hsn hpm y) },
  exact tendsto_nhds_unique (c_seminorm_seq_lim_is_limit hf1 hc hsn hpm (x * y)) hlim,
end

lemma c_seminorm_apply_c : c_seminorm hf1 hc hsn hpm c = f c :=
begin
  have hlim : filter.tendsto (c_seminorm_seq c f c) filter.at_top (𝓝 (f c)),
  { have hseq : c_seminorm_seq c f c = λ n, f c,
    { ext n,
      simp only [c_seminorm_seq],
      rw [← pow_succ, hpm _ le_add_self, pow_succ, mul_div_assoc, div_self (pow_ne_zero n hc.symm),
        mul_one], },
    simpa [hseq] using tendsto_const_nhds },
    exact tendsto_nhds_unique (c_seminorm_seq_lim_is_limit hf1 hc hsn hpm c) hlim,
end

lemma c_seminorm_c_is_mult (x : α) :
  c_seminorm hf1 hc hsn hpm (c * x) = c_seminorm hf1 hc hsn hpm c * c_seminorm hf1 hc hsn hpm x :=
begin
  have hlim : filter.tendsto (λ n, c_seminorm_seq c f x (n + 1)) filter.at_top
    (𝓝 (c_seminorm_seq_lim hf1 hc hsn hpm x)),
  { refine filter.tendsto.comp (c_seminorm_seq_lim_is_limit hf1 hc hsn hpm x) _,
    apply filter.tendsto_at_top_at_top_of_monotone,
    { intros n m hnm, exact succ_order.succ_le_succ_iff.mpr hnm },
    { rintro n, use n, linarith, }}, 
  rw c_seminorm_apply_c hf1 hc hsn hpm,
  apply tendsto_nhds_unique (c_seminorm_seq_lim_is_limit hf1 hc hsn hpm (c * x)),
  have hterm: c_seminorm_seq c f (c * x) = (λ n, f c * (c_seminorm_seq c f x (n + 1))),
  { simp only [c_seminorm_seq],
    ext n,
    rw [mul_comm c, pow_succ, pow_succ, mul_div_comm, div_eq_mul_inv _ (f c * f c ^ n), mul_inv₀,
      ← mul_assoc (f c), mul_inv_cancel hc.symm, one_mul, mul_assoc, div_eq_mul_inv] },
  simpa [hterm] using filter.tendsto.mul tendsto_const_nhds hlim,
end

omit hf1 hc hsn hpm

def ring_hom.is_bounded {α : Type*} [semi_normed_ring α] {β : Type*} [semi_normed_ring β] 
  (f : α →+* β) : Prop := ∃ C : nnreal, 0 < C ∧ ∀ x : α, norm (f x) ≤ C * norm x

def ring_hom.is_bounded_wrt {α : Type*} [ring α] {β : Type*} [ring β] {nα : α → nnreal}
  (hnα : is_seminorm nα) {nβ : β → nnreal} (hnβ : is_seminorm nβ) (f : α →+* β) : Prop :=
∃ C : nnreal, 0 < C ∧ ∀ x : α, nβ (f x) ≤ C * nα x

example {C : ℝ} (hC : 0 < C) : filter.tendsto (λ n : ℕ, C ^ (1 / (n : ℝ))) filter.at_top (𝓝 1) :=
begin
  apply filter.tendsto.comp _ (tendsto_const_div_at_top_nhds_0_nat 1),
  rw ← real.rpow_zero C,
  apply continuous_at.tendsto (real.continuous_at_const_rpow (ne_of_gt hC)),
end 

lemma contraction_of_is_pm_wrt {α : Type*} [ring α] {β : Type*} [ring β] {nα : α → nnreal}
  (hnα : is_seminorm nα) {nβ : β → nnreal} (hnβ : is_seminorm nβ) 
  (hβ : is_pow_mult nβ) {f : α →+* β} (hf : f.is_bounded_wrt hnα hnβ)
  (x : α) : nβ (f x) ≤ nα x :=
begin
  obtain ⟨C, hC0, hC⟩ := hf,
  have hlim : filter.tendsto (λ n : ℕ, C ^ (1 / (n : ℝ)) * nα x) filter.at_top (𝓝 (nα x)),
  { have : (𝓝 (nα x)) = (𝓝 (1 * (nα x))) := by rw one_mul,
    rw this,
    apply filter.tendsto.mul,
    { apply filter.tendsto.comp _ (tendsto_const_div_at_top_nhds_0_nat 1),
      rw ← nnreal.rpow_zero C,
      rw ← nnreal.tendsto_coe,
      apply continuous_at.tendsto (real.continuous_at_const_rpow (ne_of_gt hC0)), },
    exact tendsto_const_nhds, },
  apply ge_of_tendsto hlim,
  simp only [filter.eventually_at_top, ge_iff_le],
  use 1,
  intros n hn,
  have h : (C^(1/n : ℝ))^n  = C,
  { have hn0 : (n : ℝ) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_gt hn),
      rw [← nnreal.rpow_nat_cast, ← nnreal.rpow_mul, one_div, inv_mul_cancel hn0,
        nnreal.rpow_one] },
  apply le_of_pow_le_pow n _ hn,
  { rw [mul_pow, h, ← hβ _ hn, ← ring_hom.map_pow],
    refine le_trans (hC (x^n)) (mul_le_mul (le_refl C)
      (hnα.pow_le  _ (lt_of_lt_of_le zero_lt_one hn)) (zero_le _) (le_of_lt hC0)) },
    { exact zero_le _ },
end

lemma seminormed_ring.to_is_seminorm {α : Type*} [semi_normed_ring α]/-  (h1 : norm (1 : α) ≤ 1) -/ : 
  is_seminorm (λ x : α, (⟨∥x∥, norm_nonneg _⟩ : nnreal)) :=
{ zero   := by simp only [norm_zero, nonneg.mk_eq_zero],
  mul    := by {simp only [nonneg.mk_mul_mk, subtype.mk_le_mk], exact norm_mul_le }/- ,
  one    := begin 
    have h : (1 : nnreal) = ⟨(1 : ℝ), zero_le_one⟩ := rfl,
    simpa [h, subtype.mk_le_mk] using h1,
  end -/ }

lemma contraction_of_is_pm {α : Type*} [semi_normed_ring α] {β : Type*} [semi_normed_ring β] 
  (hβ : is_pow_mult (λ x : β, (⟨∥x∥, norm_nonneg _⟩ : nnreal))) {f : α →+* β} (hf : f.is_bounded)
  (x : α) /- (h1α : norm (1 : α) ≤ 1) (h1β : norm (1 : β) ≤ 1) -/: norm (f x) ≤ norm x :=
contraction_of_is_pm_wrt (seminormed_ring.to_is_seminorm /- h1α -/) (seminormed_ring.to_is_seminorm /- h1β -/)
  hβ hf x

lemma eq_seminorms  {α : Type*} [ring α] {f : α → nnreal} (hf : is_seminorm f) (hfpm : is_pow_mult f)
  {g : α → nnreal} (hg : is_seminorm g) (hgpm : is_pow_mult g)
  (hfg : ∃ (r : nnreal) (hr : 0 < r), ∀ (a : α), f a ≤ r * g a)
  (hgf : ∃ (r : nnreal) (hr : 0 < r), ∀ (a : α), g a ≤ r * f a) : f = g :=
begin
  obtain ⟨r, hr0, hr⟩ := hfg,
  obtain ⟨s, hs0, hs⟩ := hgf,
  have hle : ring_hom.is_bounded_wrt hf hg (ring_hom.id _) := ⟨s, hs0, hs⟩,
  have hge : ring_hom.is_bounded_wrt hg hf (ring_hom.id _) := ⟨r, hr0, hr⟩,
  ext x,
  exact le_antisymm (contraction_of_is_pm_wrt hg hf hfpm hge x)
    (contraction_of_is_pm_wrt hf hg hgpm hle x),
end

--#lint