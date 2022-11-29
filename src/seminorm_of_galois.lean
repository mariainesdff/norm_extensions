import normed_space
import data.fintype.order
import field_theory.fixed
import field_theory.normal


noncomputable theory

section supr

lemma lt_csupr_of_lt {α : Type*} {ι : Sort*} [conditionally_complete_lattice α] {a : α} {f : ι → α}
  (H : bdd_above (set.range f)) (c : ι) (h : a < f c) : a < supr f :=
lt_of_lt_of_le h (le_csupr H c)

lemma csupr_univ {α β : Type*} [fintype β] [conditionally_complete_lattice α] {f : β → α} :
  (⨆ (x : β) (H : x ∈ (finset.univ : finset β)), f x) = ⨆ (x : β), f x := 
by simp

theorem finset.sup_eq_csupr {α : Type*} [nonempty α] (s : finset α) [nonempty s]
  (f : α → nnreal) : s.sup f = ⨆ (a : α) (H : a ∈ s), f a :=
begin
  apply le_antisymm,
  { apply finset.sup_le,
    intros a ha, apply le_csupr_of_le _ a,
    { exact le_csupr_of_le (set.finite.bdd_above (set.finite_range (λ (ha : a ∈ s), f a)))
        ha (le_refl _) },
    { apply set.finite.bdd_above,
      have hrange: set.range (λ (a : α), ⨆ (H : a ∈ s), f a) ⊆
        set.range (λ (a : s), f a) ∪ {⊥},
      { rintros y ⟨x, hxy⟩, 
        simp only [set.mem_range, bot_eq_zero', set.union_singleton, set.mem_insert_iff] at y ⊢,
        by_cases hx : x ∈ s,
        { right, simp only [hx, csupr_pos] at hxy, exact ⟨⟨x, hx⟩, hxy⟩, },
        { left, simp only [hx, csupr_false, bot_eq_zero'] at hxy, exact hxy.symm }},
      exact set.finite.subset (set.range (λ (a : ↥s), f ↑a) ∪ {⊥}).to_finite hrange, }},
  { apply csupr_le,
    intro x,
    by_cases hx : x ∈ s,
    { haveI : nonempty (x ∈ s) := ⟨hx⟩,
      apply csupr_le, intro hx', exact finset.le_sup hx, },
    { simp only [(iff_false _).mpr hx, csupr_false, bot_eq_zero', zero_le'], }}
end

lemma nnreal.supr_pow {ι : Type*} [nonempty ι] [fintype ι] (f : ι → nnreal) (n : ℕ) :
  (⨆ (i : ι), f i)^n = ⨆ (i : ι), (f i)^n :=
begin
  induction n with n hn,
  { simp only [pow_zero, csupr_const], },
  { rw [pow_succ, hn],
    apply le_antisymm,
    { apply nnreal.supr_mul_supr_le,
      intros i j,
      by_cases hij : f i < f j,
      { have hj : f i * f j ^ n ≤ f j ^ n.succ,
        { rw pow_succ, apply mul_le_mul' (le_of_lt hij) (le_refl _) },
        exact le_trans hj (le_csupr_of_le (set.finite.bdd_above (set.finite_range _)) j 
          (le_refl _)), },
      { have hi : f i * f j ^ n ≤ f i ^ n.succ,
        { rw pow_succ, exact mul_le_mul' (le_refl _) (pow_le_pow_of_le_left' (not_lt.mp hij) n) },
        exact le_trans hi (le_csupr_of_le (set.finite.bdd_above (set.finite_range _)) i
          (le_refl _)), }},
    { haveI : nonempty (finset.univ : finset ι),
     { exact finset.nonempty_coe_sort.mpr finset.univ_nonempty },
       simp only [← csupr_univ, ← finset.sup_eq_csupr, pow_succ],
      apply finset.sup_mul_le_mul_sup_of_nonneg;
      rintros i -; exact zero_le _ }},
end

lemma real.supr_nonneg {ι : Type*} [nonempty ι] {f : ι → ℝ} (hf_nn : ∀ i, 0 ≤ f i) :
  0 ≤ supr f :=
begin
  by_cases hf : bdd_above (set.range f),
  { set i : ι := nonempty.some (by apply_instance),
    exact le_csupr_of_le hf i (hf_nn i), },
  { simp only [supr, Sup],
    rw dif_neg,
    exact not_and_of_not_right _ hf }
end

lemma real.supr_mul_supr_le {ι : Type*} [nonempty ι] {a : ℝ} {g h : ι → ℝ} (hg_nn : ∀ i, 0 ≤ g i)
  (hh_nn : ∀ i, 0 ≤ h i) (H : ∀ i j, g i * h j ≤ a) : supr g * supr h ≤ a :=
begin
  rw real.supr_mul_of_nonneg (real.supr_nonneg hh_nn),
  apply csupr_le,
  intro i,
  rw real.mul_supr_of_nonneg (hg_nn _),
  exact csupr_le (λ j, H i j), 
end

lemma real.supr_mul_le_mul_supr_of_nonneg {ι : Type*} [nonempty ι] [fintype ι] {f g : ι → ℝ} 
  (hf_nn : ∀ i, 0 ≤ f i) (hg_nn : ∀ i, 0 ≤ g i) : (⨆ (i : ι), f i * g i) ≤ supr f * supr g := 
begin
  have hf : bdd_above (set.range f) := fintype.bdd_above_range f,
  have hg : bdd_above (set.range g) := fintype.bdd_above_range g,
  exact csupr_le (λ x, mul_le_mul (le_csupr hf x) (le_csupr hg x) (hg_nn x) 
      (real.supr_nonneg hf_nn)),
end

lemma real.supr_pow {ι : Type*} [nonempty ι] [fintype ι] {f : ι → ℝ} (hf_nn : ∀ i, 0 ≤ f i)
  (n : ℕ) : (⨆ (i : ι), f i)^n = ⨆ (i : ι), (f i)^n :=
begin
  induction n with n hn,
  { simp only [pow_zero, csupr_const], },
  { rw [pow_succ, hn],
    apply le_antisymm,
    { refine real.supr_mul_supr_le hf_nn (λ x, pow_nonneg (hf_nn x) n) _,
      intros i j,
      by_cases hij : f i < f j,
      { have hj : f i * f j ^ n ≤ f j ^ n.succ,
        { rw pow_succ,
          exact mul_le_mul (le_of_lt hij) (le_refl _) (pow_nonneg (hf_nn _) _) (hf_nn _) },
        exact le_trans hj (le_csupr_of_le (set.finite.bdd_above (set.finite_range _)) j 
          (le_refl _)), },
      { have hi : f i * f j ^ n ≤ f i ^ n.succ,
        { rw pow_succ, 
          exact mul_le_mul (le_refl _) (pow_le_pow_of_le_left (hf_nn _) (not_lt.mp hij) _)
            (pow_nonneg (hf_nn _) _) (hf_nn _) },
        exact le_trans hi (le_csupr_of_le (set.finite.bdd_above (set.finite_range _)) i
          (le_refl _)), }},
    { simp_rw [pow_succ],
      exact real.supr_mul_le_mul_supr_of_nonneg hf_nn (λ x, pow_nonneg (hf_nn x) n) }},
end

end supr

variables {K : Type*} [normed_field K] {L : Type*} [field L] [algebra K L]
  (h_alg : algebra.is_algebraic K L) (h_fin : finite_dimensional K L)

section alg_norm_of_auto

def alg_norm_of_auto (σ : L ≃ₐ[K] L) (hna : is_nonarchimedean (norm : K → ℝ)) :
  algebra_norm K L := 
{ to_fun    := λ x, classical.some (finite_extension_pow_mul_seminorm h_fin hna) (σ x),
  map_zero' := by simp only [map_zero],
  add_le'   := λ x y, by simp only [map_add σ, map_add_le_add],
  neg'      := λ x, by simp only [map_neg σ, map_neg_eq_map],
  mul_le'   := λ x y, by simp only [map_mul σ, map_mul_le_mul],
  smul'     := λ x y, by simp only [map_smul σ, map_smul_eq_mul],
  eq_zero_of_map_eq_zero' := λ x hx, 
    (add_equiv_class.map_eq_zero_iff _).mp (eq_zero_of_map_eq_zero _ hx), }

lemma alg_norm_of_auto_apply (σ : L ≃ₐ[K] L) (hna : is_nonarchimedean (norm : K → ℝ)) (x : L) :
  alg_norm_of_auto h_fin σ hna x = 
  classical.some (finite_extension_pow_mul_seminorm h_fin hna) (σ x) := rfl

lemma alg_norm_of_auto_is_pow_mul (σ : L ≃ₐ[K] L) (hna : is_nonarchimedean (norm : K → ℝ)) :
  is_pow_mul (alg_norm_of_auto h_fin σ hna) :=
begin
  intros x n hn,
  simp only [alg_norm_of_auto_apply, map_pow σ x n],
  exact (classical.some_spec (finite_extension_pow_mul_seminorm h_fin hna)).1 _ hn,
end

lemma alg_norm_of_auto_is_nonarchimedean (σ : L ≃ₐ[K] L)
  (hna : is_nonarchimedean (norm : K → ℝ)) :
  is_nonarchimedean (alg_norm_of_auto h_fin σ hna):=
begin
  intros x y,
  simp only [alg_norm_of_auto_apply, map_add σ],
  exact (classical.some_spec (finite_extension_pow_mul_seminorm h_fin hna)).2.2 _ _,
end

lemma alg_norm_of_auto_extends (σ : L ≃ₐ[K] L) (hna : is_nonarchimedean (norm : K → ℝ)) :
  function_extends (norm : K → ℝ) (alg_norm_of_auto h_fin σ hna) :=
begin
  intro r, simp only [alg_norm_of_auto_apply, alg_equiv.commutes], 
  exact (classical.some_spec (finite_extension_pow_mul_seminorm h_fin hna)).2.1 _,
end

end alg_norm_of_auto

section alg_norm_of_galois

def alg_norm_of_galois (hna : is_nonarchimedean (norm : K → ℝ)) :
  algebra_norm K L := 
{ to_fun    := λ x, (supr (λ (σ : L ≃ₐ[K] L), alg_norm_of_auto h_fin σ hna x)),
  map_zero' := by simp only [map_zero,  csupr_const],
  add_le'   := λ x y, csupr_le (λ σ, le_trans (map_add_le_add (alg_norm_of_auto h_fin σ hna) x y)
    (add_le_add (le_csupr_of_le (set.finite.bdd_above (set.finite_range _)) σ (le_refl _)) 
      (le_csupr_of_le (set.finite.bdd_above (set.finite_range _)) σ (le_refl _)))), 
  neg' := λ x, by simp only [map_neg_eq_map],
  mul_le'     := λ x y, csupr_le $ λ σ, le_trans (map_mul_le_mul (alg_norm_of_auto h_fin σ hna) x y)
     (mul_le_mul (le_csupr_of_le (set.finite.bdd_above (set.finite_range _)) σ (le_refl _))
        (le_csupr_of_le (set.finite.bdd_above (set.finite_range _)) σ (le_refl _)) (map_nonneg _ _)
        (le_csupr_of_le (set.finite.bdd_above (set.finite_range _)) σ (map_nonneg _ _))),
  eq_zero_of_map_eq_zero' := λ x, 
  begin
    contrapose!, 
    exact λ hx, ne_of_gt (lt_csupr_of_lt  (set.finite.bdd_above (set.range (λ (σ : L ≃ₐ[K] L),
      alg_norm_of_auto h_fin σ hna x)).to_finite) (alg_equiv.refl) (map_pos_of_ne_zero _ hx)),
  end,
  smul'    := λ r x, by simp only [algebra_norm_class.map_smul_eq_mul, 
    normed_ring.to_ring_norm_apply, real.mul_supr_of_nonneg (norm_nonneg _)] }

@[simp] lemma alg_norm_of_galois_apply (hna : is_nonarchimedean (norm : K → ℝ)) (x : L) :
  alg_norm_of_galois h_fin hna x = (supr (λ (σ : L ≃ₐ[K] L), alg_norm_of_auto h_fin σ hna x)) := 
rfl

lemma alg_norm_of_galois_is_pow_mul (hna : is_nonarchimedean (norm : K → ℝ)) :
  is_pow_mul (alg_norm_of_galois h_fin hna) :=
begin
  intros x n hn,
  simp only [alg_norm_of_galois_apply],
  rw real.supr_pow, 
  exact supr_congr (λ σ, alg_norm_of_auto_is_pow_mul h_fin σ hna _ hn),
  { exact λ σ, map_nonneg (alg_norm_of_auto h_fin σ hna) x }
end

lemma alg_norm_of_galois_is_nonarchimedean (hna : is_nonarchimedean (norm : K → ℝ)) :
  is_nonarchimedean (alg_norm_of_galois h_fin hna)  := 
λ x y, csupr_le (λ σ, le_trans ((alg_norm_of_auto_is_nonarchimedean h_fin σ hna) x y)
  (max_le_max (le_csupr_of_le (set.finite.bdd_above (set.finite_range _)) σ (le_refl _))
    (le_csupr_of_le (set.finite.bdd_above (set.finite_range _)) σ (le_refl _))))

lemma alg_norm_of_galois_extends (hna : is_nonarchimedean (norm : K → ℝ)) :
  function_extends (norm : K → ℝ) (alg_norm_of_galois h_fin hna) := 
λ r, begin
  rw [alg_norm_of_galois, ← algebra_norm.to_fun_eq_coe], 
  simp only [algebra_norm.to_fun_eq_coe, alg_norm_of_auto_extends h_fin _ hna r, csupr_const],
end

end alg_norm_of_galois