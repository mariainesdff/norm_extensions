import seminormed_rings
import ring_theory.adjoin.basic
--import field_theory.normal

open_locale nnreal

variables {R S : Type*} [comm_ring R] [comm_ring S] [algebra R S]

lemma is_pow_mult.restriction (A : subalgebra R S) {f : S → ℝ≥0} (hf_pm : is_pow_mult f) :
  is_pow_mult (λ x : A, (f x.val)) :=
λ x n hn, by simpa [subtype.val_eq_coe,subsemiring_class.coe_pow] using (hf_pm ↑x hn)

lemma is_algebra_norm.restriction (A : subalgebra R S) {g : R → ℝ≥0} (hg : is_norm g)
  {f : S → ℝ≥0} (hf_an : is_algebra_norm hg f) : is_algebra_norm hg (λ x : A, (f x.val)) :=
⟨⟨⟨hf_an.to_is_norm.to_is_seminorm.zero, λ x y, hf_an.to_is_norm.to_is_seminorm.add _ _,
    λ x y, hf_an.to_is_norm.to_is_seminorm.mul _ _⟩, λ x hx, (by {rw [ne.def, 
      ← add_submonoid_class.coe_eq_zero] at hx, exact hf_an.to_is_norm.ne_zero _ hx})⟩,
     λ r x, hf_an.smul _ _⟩

-- Proposition 3.1.5/1
lemma eq_of_pow_mult_faithful {g : R → ℝ≥0} (hg : is_mul_norm g) {f₁ : S → ℝ≥0}
  (hf₁_pm : is_pow_mult f₁) (hf₁_an : is_algebra_norm (hg.to_is_norm) f₁) {f₂ : S → ℝ≥0}
  (hf₂_pm : is_pow_mult f₂) (hf₂_an : is_algebra_norm (hg.to_is_norm) f₂)
  (h_eq : ∀ (y : S), ∃ (C₁ C₂ : ℝ≥0) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂), ∀ (x : (algebra.adjoin R {y})), 
    f₁ x.val ≤ C₁ * (f₂ x.val) ∧ f₂ x.val ≤ C₂ * (f₁ x.val) ) : 
  f₁ = f₂ := 
begin
  ext x,
  rw nnreal.coe_eq,
  set g₁ : algebra.adjoin R ({x} : set S) → ℝ≥0 := λ y, f₁ y.val with hg₁,
  set g₂ : algebra.adjoin R ({x} : set S) → ℝ≥0 := λ y, f₂ y.val with hg₂,
  have hg₁_s : is_seminorm g₁ :=
  (is_algebra_norm.restriction _ hg.to_is_norm hf₁_an).to_is_norm.to_is_seminorm,
  have hg₁_pm : is_pow_mult g₁ := is_pow_mult.restriction _ hf₁_pm,
  have hg₂_s : is_seminorm g₂ :=
  (is_algebra_norm.restriction _ hg.to_is_norm hf₂_an).to_is_norm.to_is_seminorm,
  have hg₂_pm : is_pow_mult g₂ := is_pow_mult.restriction _ hf₂_pm,
  let y : algebra.adjoin R ({x} : set S) := ⟨x, algebra.self_mem_adjoin_singleton R x⟩,
  have hy : x = y.val := rfl,
  have h1 : f₁ y.val = g₁ y := rfl,
  have h2 : f₂ y.val = g₂ y := rfl,
  obtain ⟨C₁, C₂, hC₁_pos, hC₂_pos, hC⟩ := h_eq x,
  obtain ⟨hC₁, hC₂⟩ := forall_and_distrib.mp hC,
  rw [hy, h1, h2, eq_seminorms hg₁_s hg₁_pm hg₂_s hg₂_pm ⟨C₁, hC₁_pos, hC₁⟩ ⟨C₂, hC₂_pos, hC₂⟩],
end