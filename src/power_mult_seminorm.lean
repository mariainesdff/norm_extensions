import filter
import seminormed_rings

noncomputable theory

open_locale topological_space

variables {α : Type*} [ring α] (c : α) (f : α → ℝ) 

def c_seminorm_seq (x : α) : ℕ → ℝ :=
λ n, (f (x * c^n))/((f c)^n)

variable {f}

lemma c_seminorm_seq_zero (hf : f 0 = 0) : 
  c_seminorm_seq c f 0 = 0 := 
begin
  simp only [c_seminorm_seq],
  ext n,
  rw [zero_mul, hf, zero_div],
  refl,
end

lemma c_seminorm_seq_nonneg (hf : ∀ a, 0 ≤ f a) (x : α) (n : ℕ) : 0 ≤ c_seminorm_seq c f x n := 
div_nonneg (hf _) (pow_nonneg (hf _) n)

lemma c_seminorm_is_bounded (hf : ∀ a, 0 ≤ f a) (x : α) :
  bdd_below (set.range (c_seminorm_seq c f x)) := 
begin
  use 0,
  rw mem_lower_bounds,
  intros r hr,
  obtain ⟨n, hn⟩ := hr,
  rw ← hn,
  exact c_seminorm_seq_nonneg c hf x n,
end

variable {c}

lemma c_seminorm_seq_one (hc : 0 ≠ f c) (hf : is_pow_mult f): 
  c_seminorm_seq c f 1 = 1 := 
begin
  simp only [c_seminorm_seq],
  ext n,
  rw [one_mul, hf, div_self (pow_ne_zero n (ne.symm hc))],
  refl,
end

lemma c_seminorm_seq_antitone  (hc : 0 ≠ f c) (hsm : is_seminorm f) (hpm : is_pow_mult f) (x : α) :
  antitone (c_seminorm_seq c f x) := 
begin
  intros m n hmn,
  simp only [c_seminorm_seq],
  nth_rewrite 0 ← nat.add_sub_of_le hmn,
  rw [pow_add, ← mul_assoc],
  apply le_trans (div_le_div (mul_nonneg (hsm.nonneg _ ) (hsm.nonneg _ )) (hsm.mul _ _) 
      (pow_pos (lt_of_le_of_ne (hsm.nonneg c) hc) n) (le_refl _)),
  rw [hpm c (n - m), mul_div_assoc, div_eq_mul_inv, pow_sub₀ _ (ne.symm hc) hmn, mul_assoc,
    mul_comm (f c ^ m)⁻¹, ← mul_assoc (f c ^ n), mul_inv_cancel (pow_ne_zero n (ne.symm hc)),
    one_mul, div_eq_mul_inv],
end

def c_seminorm_seq_lim (hc : 0 ≠ f c) (hsm : is_seminorm f) (hpm : is_pow_mult f) (x : α) : ℝ :=
classical.some (filter.tendsto_of_is_bounded_antitone (c_seminorm_is_bounded c hsm.nonneg x) 
  (c_seminorm_seq_antitone hc hsm hpm x))

lemma c_seminorm_seq_lim_is_limit (hc : 0 ≠ f c) (hsm : is_seminorm f) (hpm : is_pow_mult f)
  (x : α) : filter.tendsto ((c_seminorm_seq c f x)) filter.at_top
  (𝓝 (c_seminorm_seq_lim hc hsm hpm x)) :=
classical.some_spec (filter.tendsto_of_is_bounded_antitone (c_seminorm_is_bounded c hsm.nonneg x) 
  (c_seminorm_seq_antitone hc hsm hpm x))

def c_seminorm (hc : 0 ≠ f c) (hsm : is_seminorm f) (hpm : is_pow_mult f) : α → ℝ :=
λ x, c_seminorm_seq_lim hc hsm hpm x

lemma c_seminorm_zero (hc : 0 ≠ f c) (hsm : is_seminorm f) (hpm : is_pow_mult f) :
  c_seminorm hc hsm hpm 0 = 0 :=
tendsto_nhds_unique (c_seminorm_seq_lim_is_limit hc hsm hpm 0) 
  (by simpa [c_seminorm_seq_zero c hsm.zero] using tendsto_const_nhds)

lemma c_seminorm_is_norm_one_class (hc : 0 ≠ f c) (hsm : is_seminorm f) (hpm : is_pow_mult f) :
  is_norm_one_class (c_seminorm hc hsm hpm) :=
tendsto_nhds_unique (c_seminorm_seq_lim_is_limit hc hsm hpm 1)
  (by simpa [c_seminorm_seq_one hc hpm] using tendsto_const_nhds)

lemma c_seminorm_mul (hc : 0 ≠ f c) (hsm : is_seminorm f) (hpm : is_pow_mult f) (x y : α) :
  c_seminorm hc hsm hpm (x * y) ≤ c_seminorm hc hsm hpm x * c_seminorm hc hsm hpm y :=
begin
  sorry
end

lemma c_seminorm_nonneg (hc : 0 ≠ f c) (hsm : is_seminorm f) (hpm : is_pow_mult f) (x : α):
  0 ≤ c_seminorm hc hsm hpm x :=
begin
  simp only [c_seminorm],
  apply ge_of_tendsto (c_seminorm_seq_lim_is_limit hc hsm hpm x),
  simp only [filter.eventually_at_top, ge_iff_le],
  use 0,
  rintro n -,
  exact c_seminorm_seq_nonneg c hsm.nonneg x n,
end

lemma c_seminorm_is_seminorm (hc : 0 ≠ f c) (hsm : is_seminorm f) (hpm : is_pow_mult f) :
  is_seminorm (c_seminorm hc hsm hpm)  :=
{ nonneg := c_seminorm_nonneg hc hsm hpm,
  zero   := c_seminorm_zero hc hsm hpm,
  mul    := c_seminorm_mul hc hsm hpm,
  one    := le_of_eq (c_seminorm_is_norm_one_class hc hsm hpm) }

lemma c_seminorm_is_nonarchimedean (hc : 0 ≠ f c) (hsm : is_seminorm f) (hpm : is_pow_mult f)
  (hna : is_nonarchimedean f) :
  is_nonarchimedean (c_seminorm hc hsm hpm)  :=
begin
  intros x y,
  apply le_of_tendsto_of_tendsto' (c_seminorm_seq_lim_is_limit hc hsm hpm (x + y))
    (filter.tendsto.max (c_seminorm_seq_lim_is_limit hc hsm hpm x)
    (c_seminorm_seq_lim_is_limit hc hsm hpm y)),
  intro n,
  have hmax : f ((x + y) * c ^ n) ≤ max (f (x * c ^ n)) (f (y * c ^ n)),
  { rw add_mul, exact hna _ _ },
  rw le_max_iff at hmax ⊢,
  cases hmax; [left, right];
  exact (div_le_div_right (pow_pos (lt_of_le_of_ne (hsm.nonneg _) hc) n)).mpr hmax,
end

lemma c_seminorm_is_pow_mult (hc : 0 ≠ f c) (hsm : is_seminorm f) (hpm : is_pow_mult f)  :
  is_pow_mult (c_seminorm hc hsm hpm) :=
begin
  intros x n,
  simp only [c_seminorm],
  have h := (c_seminorm_seq_lim_is_limit hc hsm hpm (x^n)),
  have hpow := filter.tendsto.pow (c_seminorm_seq_lim_is_limit hc hsm hpm x) n,
  
  sorry
end

lemma c_seminorm_le_seminorm (hc : 0 ≠ f c) (hsm : is_seminorm f) (hpm : is_pow_mult f) (x : α) :
  c_seminorm hc hsm hpm x ≤ f x :=
begin
  apply le_of_tendsto (c_seminorm_seq_lim_is_limit hc hsm hpm x),
  simp only [filter.eventually_at_top, ge_iff_le],
  use 0,
  rintros n -,
  apply le_trans (div_le_div  (mul_nonneg (hsm.nonneg _ ) (hsm.nonneg _ )) (hsm.mul _ _) 
      (pow_pos (lt_of_le_of_ne (hsm.nonneg c) hc) n) (le_refl _)),
  rw [hpm, mul_div_assoc, div_self (pow_ne_zero n hc.symm), mul_one],
end

lemma c_seminorm_apply_of_is_mult (hc : 0 ≠ f c) (hsm : is_seminorm f) (hpm : is_pow_mult f)
  {x : α} (hx : ∀ y : α, f (x * y) = f x * f y) :
  c_seminorm hc hsm hpm x = f x :=
begin
  have hlim : filter.tendsto (c_seminorm_seq c f x) filter.at_top (𝓝 (f x)),
  { have hseq: c_seminorm_seq c f x = λ n, f x,
    { ext n,
      simp only [c_seminorm_seq],
      rw [hx (c ^n), hpm, mul_div_assoc, div_self (pow_ne_zero n hc.symm), mul_one], },
    simpa [hseq] using tendsto_const_nhds, },
  exact tendsto_nhds_unique (c_seminorm_seq_lim_is_limit hc hsm hpm x) hlim,
end

lemma c_seminorm_is_mult_of_is_mult (hc : 0 ≠ f c) (hsm : is_seminorm f) (hpm : is_pow_mult f)
  {x : α} (hx : ∀ y : α, f (x * y) = f x * f y) (y : α) :
  c_seminorm hc hsm hpm (x * y) = c_seminorm hc hsm hpm x * c_seminorm hc hsm hpm y :=
begin
  have hlim : filter.tendsto (c_seminorm_seq c f (x * y)) filter.at_top
    (𝓝 (c_seminorm hc hsm hpm x * c_seminorm hc hsm hpm y)),
  { rw c_seminorm_apply_of_is_mult hc hsm hpm hx,
    have hseq : c_seminorm_seq c f (x * y) = λ n, f x * c_seminorm_seq c f y n,
    { ext n,
      simp only [c_seminorm_seq],
      rw [mul_assoc, hx, mul_div_assoc], },
    simpa [hseq] using filter.tendsto.const_mul _ (c_seminorm_seq_lim_is_limit hc hsm hpm y) },
  exact tendsto_nhds_unique (c_seminorm_seq_lim_is_limit hc hsm hpm (x * y)) hlim,
end

lemma c_seminorm_apply_c (hc : 0 ≠ f c) (hsm : is_seminorm f) (hpm : is_pow_mult f) :
  c_seminorm hc hsm hpm c = f c :=
begin
  have hlim : filter.tendsto (c_seminorm_seq c f c) filter.at_top (𝓝 (f c)),
  { have hseq : c_seminorm_seq c f c = λ n, f c,
    { ext n,
      simp only [c_seminorm_seq],
      rw [← pow_succ, hpm, pow_succ, mul_div_assoc, div_self (pow_ne_zero n hc.symm), mul_one],},
    simpa [hseq] using tendsto_const_nhds },
    exact tendsto_nhds_unique (c_seminorm_seq_lim_is_limit hc hsm hpm c) hlim,
end

lemma c_seminorm_c_is_mult (hc : 0 ≠ f c) (hsm : is_seminorm f) (hpm : is_pow_mult f) (x : α) :
  c_seminorm hc hsm hpm (c * x) = c_seminorm hc hsm hpm c * c_seminorm hc hsm hpm x :=
begin
  have hlim : filter.tendsto (c_seminorm_seq c f (c * x)) filter.at_top
    (𝓝 (c_seminorm hc hsm hpm c * c_seminorm hc hsm hpm x)),
  { sorry },
  exact tendsto_nhds_unique (c_seminorm_seq_lim_is_limit hc hsm hpm (c * x)) hlim,
end

def ring_hom.is_bounded {α : Type*} [semi_normed_ring α] {β : Type*} [semi_normed_ring β] 
  (f : α →+* β) : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ x : α, norm (f x) ≤ C * norm x

lemma contraction_of_is_pm {α : Type*} [semi_normed_ring α] {β : Type*} [semi_normed_ring β] 
  (hβ : is_pow_mult (@semi_normed_ring.to_has_norm β _).norm) {f : α →+* β} (hf : f.is_bounded)
  (x : α) : norm (f x) ≤ norm x :=
begin
  obtain ⟨C, hC0, hC⟩ := hf,
  have hn : ∀ n : ℕ, (norm (f x))^n ≤ C * (norm x)^n,
  { intro n,
    rw ← hβ,
    rw ← ring_hom.map_pow,
    refine le_trans (hC (x^n)) _,
    apply mul_le_mul (le_refl C) _ (norm_nonneg (x ^ n)) hC0,
    sorry, },
  sorry
end

--#lint