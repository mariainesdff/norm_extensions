import analysis.normed.field.basic
import analysis.special_functions.pow

noncomputable theory

open_locale topological_space nnreal

def is_pow_mult {α : Type*} [ring α] (f : α → nnreal) :=
∀ (a : α) {n : ℕ} (hn : 1 ≤ n), f (a^n) = (f a) ^ n

structure is_seminorm {α : Type*} [ring α] (f : α → nnreal) : Prop :=
(zero : f 0 = 0)
(add : ∀ a b, f (a + b) ≤ f a + f b)
(mul : ∀ a b, f (a * b) ≤ f a * f b)

def is_norm_le_one_class {α : Type*} [ring α] (f : α → nnreal) : Prop := f 1 ≤  1

lemma is_seminorm.pow_le {α : Type*} [ring α] {f : α → nnreal} (hf : is_seminorm f) (a : α) :
  ∀ {n : ℕ}, 0 < n → f (a ^ n) ≤ (f a) ^ n
| 1 h := by simp only [pow_one]
| (n + 2) h := by simpa [pow_succ _ (n + 1)] using le_trans (hf.mul a _)
    (mul_le_mul_left' (is_seminorm.pow_le n.succ_pos) _)

def is_norm_one_class {α : Type*} [ring α] (f : α → nnreal) : Prop := f 1 = 1

lemma is_norm_one_le_class_norm_one {α : Type*} [ring α] {f : α → nnreal} (hsn : is_seminorm f)
  (hf1 : is_norm_le_one_class f) : f 1 = 0 ∨ f 1 = 1 :=
begin
  by_cases h0 : f 1 = 0,
  { exact or.inl h0 },
  { have h1 : f 1 * 1 ≤ f 1 * f 1,
    { conv_lhs{ rw ← one_mul (1 : α)},
      convert hsn.mul 1 1,
      rw mul_one, },
    rw mul_le_mul_left (lt_of_le_of_ne (zero_le (f 1)) (ne.symm h0)) at h1,
    exact or.inr (le_antisymm hf1 h1), }
end

lemma is_norm_one_class_iff_nontrivial {α : Type*} [ring α] {f : α → nnreal} (hsn : is_seminorm f)
  (hf1 : is_norm_le_one_class f) :
  is_norm_one_class f ↔ ∃ x : α, f x ≠ 0 :=
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
    { cases is_norm_one_le_class_norm_one hsn hf1 with h0 h1,
      exacts [absurd h0 hf0, h1] }}
end

structure is_norm {α : Type*} [ring α] (f : α → nnreal) extends (is_seminorm f) : Prop :=
(ne_zero : ∀ a, a ≠ 0 → 0 < f a)

structure is_mul_norm {α : Type*} [ring α] (f : α → nnreal) extends (is_norm f) : Prop :=
(mul_eq : ∀ a b, f (a * b) = f a * f b)

structure is_algebra_norm {α : Type*} [comm_ring α] {g : α → nnreal} (hg : is_norm g) 
  {β : Type*} [ring β] [algebra α β] (f : β → nnreal) extends (is_norm f) : Prop :=
(smul : ∀ (a : α) (x : β) , f (a • x) = g a * f x)

lemma is_algebra_norm_extends' {α : Type*} [comm_ring α] {g : α → nnreal} (hg : is_norm g) 
  {β : Type*} [ring β] [algebra α β] {f : β → nnreal} (hf : is_algebra_norm hg f) 
  (hf1 : is_norm_one_class f) (a : α) : f (a • 1) = g a :=
begin
  rw is_norm_one_class at hf1,
  rw [← mul_one (g a), ← hf1],
  exact hf.smul _ _,
end

lemma is_algebra_norm_extends {α : Type*} [comm_ring α] {g : α → nnreal} (hg : is_norm g) 
  {β : Type*} [ring β] [algebra α β] {f : β → nnreal} (hf : is_algebra_norm hg f) 
  (hf1 : is_norm_one_class f) (a : α) : f (algebra_map α β a) = g a :=
begin
  rw algebra.algebra_map_eq_smul_one,
  exact is_algebra_norm_extends' hg hf hf1 _,
end

lemma is_norm.zero_iff {α : Type*} [ring α] {f : α → nnreal} (hf : is_norm f) (a : α ) :
  f a = 0 ↔ a = 0 :=
begin
  refine ⟨_, λ h, by simpa [h] using hf.to_is_seminorm.zero⟩,
  { contrapose, intro h, exact ne_of_gt (hf.ne_zero a h), },
end
/- lemma root_norm_le_spectral_value (hf_pm : is_pow_mult f) (hf_u : is_ultrametric f)
  (hf_alg_norm : is_algebra_norm (normed_ring.to_is_norm K) f) {p : K[X]} (hp : p.monic) {x : L}
  (hx : polynomial.aeval x p = 0) : f x ≤ spectral_value hp  -/



-- Def. 2.1.1/2. Probably won't need to use this, since in is_algebra_norm I already assume faithful
structure is_faithful_norm {α : Type*} [comm_ring α] {g : α → nnreal} (hg : is_mul_norm g) 
  {β : Type*} [ring β] [algebra α β] (f : β → nnreal) extends (is_norm f) : Prop :=
(smul : ∀ (a : α) (x : β) , f ((algebra_map α β a) * x) = g a * f x)

def function_extends {α : Type*} [comm_ring α] (g : α → nnreal) {β : Type*} [ring β] [algebra α β]
  (f : β → nnreal) : Prop :=
∀ x : α, f (algebra_map α β x) = g x 

def is_nonarchimedean {α : Type*} [add_group α] (f : α → nnreal) : Prop := 
∀ a b, f (a - b) ≤ max (f a) (f b)

lemma is_nonarchimedean.neg {α : Type*} [add_group α] {f : α → nnreal} (hu : is_nonarchimedean f) 
  (h0 : f 0 = 0) (x : α) : f (-x) = f x := 
begin
  apply le_antisymm,
  { rw [neg_eq_zero_sub, ← max_eq_right (zero_le (f x)), ← h0], exact hu _ _, },
  { nth_rewrite 0 [← neg_neg x],
    rw [neg_eq_zero_sub, ← max_eq_right (zero_le (f (-x))), ← h0], exact hu _ _, },
end

lemma is_nonarchimedean.add_le {α : Type*} [add_group α] {f : α → nnreal} (h0 : f 0 = 0)
  (hu : is_nonarchimedean f) (a b : α) : f (a + b) ≤ max (f a) (f b) := 
begin
  rw [← neg_neg b, ← sub_eq_add_neg, neg_neg, ← hu.neg h0 b], exact hu _ _,
end

/- def is_nonarchimedean {α : Type*} [add_monoid α] (f : α → nnreal) : Prop := 
∀ a b, f (a + b) ≤ max (f a) (f b) -/

lemma is_nonarchimedean_nmul {α : Type*} [ring α] {f : α → nnreal} (hsn : is_seminorm f)
  (hna : is_nonarchimedean f) (n : ℕ) (a : α) : f (n * a) ≤ (f a) := 
begin
  induction n with n hn,
  { rw [nat.cast_zero, zero_mul, hsn.zero], exact zero_le _ },
  { rw [nat.cast_succ, add_mul, one_mul],
    exact le_trans (is_nonarchimedean.add_le hsn.zero hna _ _) (max_le_iff.mpr ⟨hn, le_refl _⟩) }
end

lemma is_nonarchimedean_add_eq_max_of_ne {α : Type*} [ring α] {f : α → nnreal} (hsn : is_seminorm f)
  (hu : is_nonarchimedean f) {x y : α} (hne : f y ≠ f x) :
  f (x + y) = max (f x) (f y) :=
begin
  wlog hle := le_total (f y) (f x) using [x y],
  have hlt : f y < f x, from lt_of_le_of_ne hle hne,
  have : f x ≤ max (f (x + y)) (f y), from calc
    f x = f (x + y - y) : by congr; rw [add_sub_cancel]
               ... ≤ max (f (x + y)) (f (y)) : hu _ _,
  have hnge : f y ≤ f (x + y),
  { apply le_of_not_gt,
    intro hgt,
    rw max_eq_right_of_lt hgt at this,
    apply not_lt_of_ge this,
    assumption },
  have : f x ≤ f (x + y), by rwa [max_eq_left hnge] at this,
  apply _root_.le_antisymm,
  { exact hu.add_le hsn.zero _ _ },
  { rw max_eq_left_of_lt hlt,
    assumption }
end

open_locale classical

lemma is_nonarchimedean_finset_add {α : Type*} [ring α] {f : α → nnreal} (hf0 : f 0 = 0)
  (hna : is_nonarchimedean f) (s : finset α) :
  ∃ (a : α) (ha : if s.nonempty then a ∈ s else a = 0), f (s.sum id) ≤ f a := 
begin
  apply finset.induction_on s,
  { rw [finset.sum_empty], use 0, simp only [finset.not_nonempty_empty, if_false],
    exact ⟨eq.refl _, le_refl _⟩, },
  { rintros a s has ⟨M, hMs, hM⟩,
    rw [finset.sum_insert has, id.def],
    by_cases hMa : f M ≤ f a,
    { refine ⟨a, by simp only [finset.insert_nonempty, finset.mem_insert, if_true, eq_self_iff_true,
        true_or], le_trans (is_nonarchimedean.add_le hf0 hna _ _)
        ( max_le_iff.mpr (⟨le_refl _,le_trans hM hMa⟩))⟩ },
    { rw not_le at hMa,
      by_cases hs : s.nonempty,
      { rw if_pos hs at hMs,
        refine ⟨M, _, le_trans (is_nonarchimedean.add_le hf0 hna _ _)
          (max_le_iff.mpr ⟨le_of_lt hMa, hM⟩)⟩,
        simp only [finset.insert_nonempty, finset.mem_insert, if_true],
        exact or.intro_right _ hMs, },
      { rw if_neg hs at hMs,
        exfalso,
        simp only [hMs, hf0, not_lt_zero'] at hMa,
        exact hMa, }}}      
end

/- f ((finset.range n).sum (λ (i : ℕ), g i) -/


lemma is_nonarchimedean_finset_image_add {α : Type*} [ring α] {f : α → nnreal} (hf0 : f 0 = 0)
  (hna : is_nonarchimedean f) {β : Type*} [hβ : nonempty β] (g : β → α) (s : finset β) :
  ∃ (b : β) (hb : s.nonempty → b ∈ s), f (s.sum g) ≤ f (g b) := 
begin
  apply finset.induction_on s,
  { rw [finset.sum_empty],
    refine ⟨hβ.some, by simp only [finset.nonempty_coe_sort, finset.not_nonempty_empty,
      forall_false_left], _⟩,
    rw hf0, exact zero_le _, },
  { rintros a s has ⟨M, hMs, hM⟩,
    rw [finset.sum_insert has],
    by_cases hMa : f (g M) ≤ f (g a),
    { refine ⟨a, _, le_trans (is_nonarchimedean.add_le hf0 hna _ _)
        (max_le_iff.mpr (⟨le_refl _,le_trans hM hMa⟩))⟩,
      simp only [finset.nonempty_coe_sort, finset.insert_nonempty, finset.mem_insert,
        eq_self_iff_true, true_or, forall_true_left], },
    { rw not_le at hMa,
      by_cases hs : s.nonempty,
      { refine ⟨M, _, le_trans (is_nonarchimedean.add_le hf0 hna _ _)
          (max_le_iff.mpr ⟨le_of_lt hMa, hM⟩)⟩,
        simp only [finset.nonempty_coe_sort, finset.insert_nonempty, finset.mem_insert,
          forall_true_left],
          exact or.intro_right _ (hMs hs) },
      { use a,
        split,
        { simp only [finset.insert_nonempty, finset.mem_insert, eq_self_iff_true, true_or,
            forall_true_left] },
          have h0 : f (s.sum g) = 0,
          { rw [finset.not_nonempty_iff_eq_empty.mp hs, finset.sum_empty, hf0],},
          apply le_trans (is_nonarchimedean.add_le hf0 hna _ _),
          rw h0,
          exact max_le_iff.mpr ⟨le_refl _, zero_le _⟩, }}} 
end

lemma is_nonarchimedean_finset_range_add_le {α : Type*} [ring α] {f : α → nnreal} (hf0 : f 0 = 0)
  (hna : is_nonarchimedean f) (n : ℕ) (g : ℕ → α) : ∃ (m : ℕ) (hm : 0 < n → m < n),
  f ((finset.range n).sum g) ≤ f (g m) :=
begin
  obtain ⟨m, hm, h⟩ := is_nonarchimedean_finset_image_add hf0 hna g (finset.range n),
  rw [finset.nonempty_range_iff, ← zero_lt_iff, finset.mem_range] at hm,
  exact ⟨m, hm, h⟩,
end

lemma is_nonarchimedean_add_pow {α : Type*} [comm_ring α] {f : α → nnreal} (hsn : is_seminorm f)
  (hna : is_nonarchimedean f) (n : ℕ) (a b : α) : ∃ (m : ℕ) (hm : m ∈ list.range(n + 1)),
  f ((a + b) ^ n) ≤ (f (a ^ m)) * (f (b ^ (n - m))) :=
begin
  obtain ⟨m, hm_lt, hM⟩ := is_nonarchimedean_finset_image_add hsn.zero hna 
    (λ (m : ℕ), a ^ m * b ^ (n - m) * ↑(n.choose m)) (finset.range (n + 1)),
  simp only [finset.nonempty_range_iff, ne.def, nat.succ_ne_zero, not_false_iff, finset.mem_range,
    if_true, forall_true_left] at hm_lt,
  refine ⟨m, list.mem_range.mpr hm_lt, _⟩,
  simp only [← add_pow] at hM,
  rw mul_comm at hM,
  exact le_trans hM (le_trans (is_nonarchimedean_nmul hsn hna _ _) (hsn.mul _ _)),
end

lemma add_le_of_is_nonarchimedean {α : Type*} [ring α] {f : α → nnreal} (hf0 : f 0 = 0)
  (hna : is_nonarchimedean f) (a b : α) : f (a + b) ≤ f a + f b :=
begin
  apply le_trans (is_nonarchimedean.add_le hf0 hna _ _),
  simp only [max_le_iff, le_add_iff_nonneg_right, zero_le', le_add_iff_nonneg_left, and_self],
end

lemma field.is_norm_of_is_seminorm {α : Type*} [field α] {f : α → nnreal} (hf : is_seminorm f)
  (hnt : ∃ x : α, 0 ≠ f x) : is_norm f := 
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
  
lemma seminormed_ring.to_is_seminorm (R : Type*) [semi_normed_ring R] :
  is_seminorm (λ r : R, ∥r∥₊) :=
{ zero := nnnorm_zero,
  add  := nnnorm_add_le,
  mul  := nnnorm_mul_le }

lemma normed_ring.to_is_norm (R : Type*) [normed_ring R] :
  is_norm (λ r : R, ∥r∥₊) :=
{ zero    := nnnorm_zero,
  add     := nnnorm_add_le,
  mul     := nnnorm_mul_le,
  ne_zero := λ x hx, by { rw [pos_iff_ne_zero, ne.def, nnnorm_eq_zero], exact hx }}

def ring_hom.is_bounded {α : Type*} [semi_normed_ring α] {β : Type*} [semi_normed_ring β] 
  (f : α →+* β) : Prop := ∃ C : nnreal, 0 < C ∧ ∀ x : α, norm (f x) ≤ C * norm x

def ring_hom.is_bounded_wrt {α : Type*} [ring α] {β : Type*} [ring β] (nα : α → nnreal)
  (nβ : β → nnreal) (f : α →+* β) : Prop :=
∃ C : nnreal, 0 < C ∧ ∀ x : α, nβ (f x) ≤ C * nα x

example {C : ℝ} (hC : 0 < C) : filter.tendsto (λ n : ℕ, C ^ (1 / (n : ℝ))) filter.at_top (𝓝 1) :=
begin
  apply filter.tendsto.comp _ (tendsto_const_div_at_top_nhds_0_nat 1),
  rw ← real.rpow_zero C,
  apply continuous_at.tendsto (real.continuous_at_const_rpow (ne_of_gt hC)),
end 

lemma contraction_of_is_pm_wrt {α : Type*} [ring α] {β : Type*} [ring β] {nα : α → nnreal}
  (hnα : is_seminorm nα) (nβ : β → nnreal) (hβ : is_pow_mult nβ)
  {f : α →+* β} (hf : f.is_bounded_wrt nα nβ) (x : α) : nβ (f x) ≤ nα x :=
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

lemma contraction_of_is_pm {α : Type*} [semi_normed_ring α] {β : Type*} [semi_normed_ring β] 
  (hβ : is_pow_mult (λ x : β, (⟨∥x∥, norm_nonneg _⟩ : nnreal))) {f : α →+* β} (hf : f.is_bounded)
  (x : α) : norm (f x) ≤ norm x :=
contraction_of_is_pm_wrt (seminormed_ring.to_is_seminorm α) (λ x : β, (∥x∥₊))
  hβ hf x

lemma eq_seminorms  {α : Type*} [ring α] {f : α → nnreal} (hf : is_seminorm f) (hfpm : is_pow_mult f)
  {g : α → nnreal} (hg : is_seminorm g) (hgpm : is_pow_mult g)
  (hfg : ∃ (r : nnreal) (hr : 0 < r), ∀ (a : α), f a ≤ r * g a)
  (hgf : ∃ (r : nnreal) (hr : 0 < r), ∀ (a : α), g a ≤ r * f a) : f = g :=
begin
  obtain ⟨r, hr0, hr⟩ := hfg,
  obtain ⟨s, hs0, hs⟩ := hgf,
  have hle : ring_hom.is_bounded_wrt f g (ring_hom.id _) := ⟨s, hs0, hs⟩,
  have hge : ring_hom.is_bounded_wrt g f (ring_hom.id _) := ⟨r, hr0, hr⟩,
  ext x,
  exact le_antisymm (contraction_of_is_pm_wrt hg f hfpm hge x)
    (contraction_of_is_pm_wrt hf g hgpm hle x),
end


-- Def. 1.5.1/2
def is_degenerate {α : Type*} [ring α] {f : α → nnreal} (hf : is_mul_norm f) : Prop :=
(∀ (x : α), f x = 0 ∨ 1 ≤ f x) ∨ (∀ (x : α), f x ≤ 1)

-- I might not need the following two defs:

--TODO: check if I can use any mathlib def
def is_bdd_above {α : Type*} [ring α] {f : α → nnreal} (hf : is_mul_norm f) : Prop :=
∃ B : ℝ≥0, ∀ x : α, f x ≤ B

def is_trivial {α : Type*} [ring α] {f : α → nnreal} (hf : is_mul_norm f) : Prop :=
∀ (x : α) (hx : x ≠ 0), f x = 1