import ring_seminorm
import analysis.special_functions.pow
import ring_theory.adjoin.basic

open_locale topological_space


def ring_hom.is_bounded {α : Type*} [semi_normed_ring α] {β : Type*} [semi_normed_ring β] 
  (f : α →+* β) : Prop := ∃ C : ℝ, 0 < C ∧ ∀ x : α, norm (f x) ≤ C * norm x

def ring_hom.is_bounded_wrt {α : Type*} [ring α] {β : Type*} [ring β] (nα : α → ℝ) (nβ : β → ℝ)
  (f : α →+* β) : Prop :=
∃ C : ℝ, 0 < C ∧ ∀ x : α, nβ (f x) ≤ C * nα x

lemma contraction_of_is_pm_wrt {α : Type*} [ring α] {β : Type*} [ring β] (nα : ring_seminorm α) 
  {nβ : β → ℝ} (hβ : is_pow_mul nβ) {f : α →+* β} (hf : f.is_bounded_wrt nα nβ) (x : α) : 
  nβ (f x) ≤ nα x :=
begin
  obtain ⟨C, hC0, hC⟩ := hf,
  have hlim : filter.tendsto (λ n : ℕ, C ^ (1 / (n : ℝ)) * nα x) filter.at_top (𝓝 (nα x)),
  { have : (𝓝 (nα x)) = (𝓝 (1 * (nα x))) := by rw one_mul,
    rw this,
    apply filter.tendsto.mul,
    { apply filter.tendsto.comp _ (tendsto_const_div_at_top_nhds_0_nat 1),
      rw ← real.rpow_zero C,
      apply continuous_at.tendsto (real.continuous_at_const_rpow (ne_of_gt hC0)), },
    exact tendsto_const_nhds, },
  apply ge_of_tendsto hlim,
  simp only [filter.eventually_at_top, ge_iff_le],
  use 1,
  intros n hn,
  have h : (C^(1/n : ℝ))^n  = C,
  { have hn0 : (n : ℝ) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_gt hn),
      rw [← real.rpow_nat_cast, ← real.rpow_mul (le_of_lt hC0), one_div, inv_mul_cancel hn0,
        real.rpow_one], },
  apply le_of_pow_le_pow n _ hn,
  { rw [mul_pow, h, ← hβ _ hn, ← ring_hom.map_pow], 
    apply le_trans (hC (x^n)),
    rw mul_le_mul_left hC0,
    exact map_pow_le_pow _ _ (nat.one_le_iff_ne_zero.mp hn), },
  { refine mul_nonneg (real.rpow_nonneg_of_nonneg (le_of_lt hC0) _) (map_nonneg _ _), }, 
end

lemma contraction_of_is_pm_wrt' {F : Type*} {α : out_param(Type*)} [ring α] 
  [ring_seminorm_class F α] {β : Type*} [ring β] (nα : F) {nβ : β → ℝ} (hβ : is_pow_mul nβ)
  {f : α →+* β} (hf : f.is_bounded_wrt nα nβ) (x : α) : 
  nβ (f x) ≤ nα x :=
begin
  obtain ⟨C, hC0, hC⟩ := hf,
  have hlim : filter.tendsto (λ n : ℕ, C ^ (1 / (n : ℝ)) * nα x) filter.at_top (𝓝 (nα x)),
  { have : (𝓝 (nα x)) = (𝓝 (1 * (nα x))) := by rw one_mul,
    rw this,
    apply filter.tendsto.mul,
    { apply filter.tendsto.comp _ (tendsto_const_div_at_top_nhds_0_nat 1),
      rw ← real.rpow_zero C,
      apply continuous_at.tendsto (real.continuous_at_const_rpow (ne_of_gt hC0)), },
    exact tendsto_const_nhds, },
  apply ge_of_tendsto hlim,
  simp only [filter.eventually_at_top, ge_iff_le],
  use 1,
  intros n hn,
  have h : (C^(1/n : ℝ))^n  = C,
  { have hn0 : (n : ℝ) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_gt hn),
      rw [← real.rpow_nat_cast, ← real.rpow_mul (le_of_lt hC0), one_div, inv_mul_cancel hn0,
        real.rpow_one], },
  apply le_of_pow_le_pow n _ hn,
  { rw [mul_pow, h, ← hβ _ hn, ← ring_hom.map_pow], 
    apply le_trans (hC (x^n)),
    rw mul_le_mul_left hC0,
    exact map_pow_le_pow _ _ (nat.one_le_iff_ne_zero.mp hn), },
  { refine mul_nonneg (real.rpow_nonneg_of_nonneg (le_of_lt hC0) _) (map_nonneg _ _), }, 
end

lemma contraction_of_is_pm {α : Type*} [semi_normed_ring α] {β : Type*} [semi_normed_ring β] 
  (hβ : is_pow_mul (norm : β → ℝ)) {f : α →+* β} (hf : f.is_bounded) (x : α) : 
  norm (f x) ≤ norm x := 
contraction_of_is_pm_wrt (seminormed_ring.to_ring_seminorm α) hβ hf x


lemma eq_seminorms  {α : Type*} [ring α] (f : ring_seminorm α) (hfpm : is_pow_mul f)
  (g : ring_seminorm α) (hgpm : is_pow_mul g)
  (hfg : ∃ (r : ℝ) (hr : 0 < r), ∀ (a : α), f a ≤ r * g a)
  (hgf : ∃ (r : ℝ) (hr : 0 < r), ∀ (a : α), g a ≤ r * f a) : f = g :=
begin
  obtain ⟨r, hr0, hr⟩ := hfg,
  obtain ⟨s, hs0, hs⟩ := hgf,
  have hle : ring_hom.is_bounded_wrt f g (ring_hom.id _) := ⟨s, hs0, hs⟩,
  have hge : ring_hom.is_bounded_wrt g f (ring_hom.id _) := ⟨r, hr0, hr⟩,
  ext x,
  exact le_antisymm (contraction_of_is_pm_wrt g hfpm hge x)
    (contraction_of_is_pm_wrt f hgpm hle x), 
end

lemma eq_seminorms' {F : Type*}  {α : out_param(Type*)} [ring α] [ring_seminorm_class F α]
  (f g : F) (hfpm : is_pow_mul f) (hgpm : is_pow_mul g)
  (hfg : ∃ (r : ℝ) (hr : 0 < r), ∀ (a : α), f a ≤ r * g a)
  (hgf : ∃ (r : ℝ) (hr : 0 < r), ∀ (a : α), g a ≤ r * f a) : f = g :=
begin
  obtain ⟨r, hr0, hr⟩ := hfg,
  obtain ⟨s, hs0, hs⟩ := hgf,
  have hle : ring_hom.is_bounded_wrt f g (ring_hom.id _) := ⟨s, hs0, hs⟩,
  have hge : ring_hom.is_bounded_wrt g f (ring_hom.id _) := ⟨r, hr0, hr⟩,
  rw ← function.injective.eq_iff (ring_seminorm_class.coe_injective'),
  ext x,
  exact le_antisymm (contraction_of_is_pm_wrt' g hfpm hge x)
    (contraction_of_is_pm_wrt' f hgpm hle x), 
end

variables {R S : Type*} [normed_comm_ring R] [comm_ring S] [algebra R S]

lemma is_pow_mul.restriction (A : subalgebra R S) {f : S → ℝ} (hf_pm : is_pow_mul f) :
  is_pow_mul (λ x : A, (f x.val)) :=
λ x n hn, by simpa [subtype.val_eq_coe,subsemiring_class.coe_pow] using (hf_pm ↑x hn)

def algebra_norm.restriction (A : subalgebra R S) 
 (f : algebra_norm R S) : algebra_norm R A := 
{ to_fun    := λ x : A, f x.val,
  map_zero' := map_zero f,
  add_le'   := λ x y, map_add_le_add _ _ _,
  neg'      := λ x, map_neg_eq_map _ _,
  mul_le'   := λ x y, map_mul_le_mul _ _ _,
  eq_zero_of_map_eq_zero' := 
  λ x hx, by {rw ← zero_mem_class.coe_eq_zero; exact eq_zero_of_map_eq_zero f hx},
  smul'      := λ r x, map_smul_eq_mul _ _ _ }

-- Proposition 3.1.5/1
lemma eq_of_pow_mult_faithful (f₁ : algebra_norm R S) (hf₁_pm : is_pow_mul f₁)
  (f₂ : algebra_norm R S) (hf₂_pm : is_pow_mul f₂)
  (h_eq : ∀ (y : S), ∃ (C₁ C₂ : ℝ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂), ∀ (x : (algebra.adjoin R {y})), 
    f₁ x.val ≤ C₁ * (f₂ x.val) ∧ f₂ x.val ≤ C₂ * (f₁ x.val) ) : 
  f₁ = f₂ := 
begin
  ext x,
  set g₁ : algebra_norm R (algebra.adjoin R ({x} : set S)) := algebra_norm.restriction _ f₁,
  set g₂ : algebra_norm R (algebra.adjoin R ({x} : set S)) := algebra_norm.restriction _ f₂,
  have hg₁_pm : is_pow_mul g₁ := is_pow_mul.restriction _ hf₁_pm,
  have hg₂_pm : is_pow_mul g₂ := is_pow_mul.restriction _ hf₂_pm,
  let y : algebra.adjoin R ({x} : set S) := ⟨x, algebra.self_mem_adjoin_singleton R x⟩,
  have hy : x = y.val := rfl,
  have h1 : f₁ y.val = g₁ y := rfl,
  have h2 : f₂ y.val = g₂ y := rfl,
  obtain ⟨C₁, C₂, hC₁_pos, hC₂_pos, hC⟩ := h_eq x,
  obtain ⟨hC₁, hC₂⟩ := forall_and_distrib.mp hC,
  rw [hy, h1, h2, eq_seminorms' g₁ g₂ hg₁_pm  hg₂_pm ⟨C₁, hC₁_pos, hC₁⟩ ⟨C₂, hC₂_pos, hC₂⟩],
end