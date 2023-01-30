/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import data.list.min_max
import analysis.special_functions.pow
import ring_theory.mv_polynomial.symmetric
import ring_theory.polynomial.vieta
import minpoly
import normal_closure
import alg_norm_of_galois

noncomputable theory

open polynomial

open_locale polynomial

section list

lemma list.max_repeat {α : Type*} {n : ℕ} (a : α) [linear_order α] :
  list.foldr max a (list.repeat a n) = a :=
begin
  induction n with n hn,
  { simp only [list.repeat, list.foldr_nil] },
  { simp only [list.foldr, list.repeat, list.repeat_succ, list.foldr_cons, max_eq_left_iff],
    exact le_of_eq hn, }
end

lemma list.le_max_of_exists_le {α : Type*} [linear_order α] {l : list α} {a x : α} (b : α)
  (hx : x ∈ l) (h : a ≤ x) : a ≤ l.foldr max b :=
begin
  induction l with y l IH,
  { exact absurd hx (list.not_mem_nil _), },
  { obtain rfl | hl := hx,
    simp only [list.foldr, list.foldr_cons],
    { exact le_max_of_le_left h, },
    { exact le_max_of_le_right (IH hl) }}
end

end list

variables {R : Type*}

section seminormed

variables [semi_normed_ring R]

--def polynomial.coeffs (p : R[X])  : list R := list.map p.coeff (list.range p.nat_degree)


def spectral_value_terms {p : R[X]} (hp : p.monic) : ℕ → ℝ := 
λ (n : ℕ), if n < p.nat_degree then ‖ p.coeff n ‖^(1/(p.nat_degree - n : ℝ)) else 0 

lemma spectral_value_terms_of_lt_nat_degree {p : R[X]} (hp : p.monic) {n : ℕ} 
  (hn : n < p.nat_degree ) : spectral_value_terms hp n = ‖ p.coeff n ‖^(1/(p.nat_degree - n : ℝ)) := 
by simp only [spectral_value_terms, if_pos hn]

lemma spectral_value_terms_of_nat_degree_le {p : R[X]} (hp : p.monic) {n : ℕ}
  (hn : p.nat_degree ≤ n) : spectral_value_terms hp n = 0 := 
by simp only [spectral_value_terms, if_neg (not_lt.mpr hn)] 

def spectral_value {p : R[X]} (hp : p.monic) : ℝ := supr (spectral_value_terms hp)

lemma spectral_value_terms_bdd_above {p : R[X]} (hp : p.monic) :
  bdd_above (set.range (spectral_value_terms hp)) := 
begin
  use list.foldr max 0
  (list.map (λ n, ‖ p.coeff n ‖^(1/(p.nat_degree - n : ℝ))) (list.range p.nat_degree)),
  { rw mem_upper_bounds,
    intros r hr,
    obtain ⟨n, hn⟩ := set.mem_range.mpr hr,
    simp only [spectral_value_terms] at hn,
    split_ifs at hn with hd hd,
    { have h : ‖ p.coeff n ‖ ^ (1 / (p.nat_degree - n : ℝ)) ∈ list.map 
        (λ (n : ℕ), ‖ p.coeff n ‖ ^ (1 / (p.nat_degree - n : ℝ))) (list.range p.nat_degree),
      { simp only [list.mem_map, list.mem_range],
        exact ⟨n, hd, rfl⟩, },
    exact list.le_max_of_exists_le 0 h (ge_of_eq hn), },
    { rw ← hn,
      by_cases hd0 : p.nat_degree = 0,
      { rw [hd0, list.range_zero, list.map_nil, list.foldr_nil], },
      { have h : ‖ p.coeff 0 ‖ ^ (1 / (p.nat_degree - 0 : ℝ)) ∈ list.map 
          (λ (n : ℕ), ‖ p.coeff n ‖ ^ (1 / (p.nat_degree - n : ℝ))) (list.range p.nat_degree),
        { simp only [list.mem_map, list.mem_range],
          exact ⟨0, nat.pos_of_ne_zero hd0, by rw nat.cast_zero⟩,},
      refine list.le_max_of_exists_le 0 h _,
      exact real.rpow_nonneg_of_nonneg (norm_nonneg _) _}}},
end

lemma spectral_value_terms_finite_range {p : R[X]} (hp : p.monic) :
  (set.range (spectral_value_terms hp)).finite :=
begin
  have h_ss : set.range (spectral_value_terms hp) ⊆ set.range (λ (n : fin p.nat_degree), 
    ‖ p.coeff n ‖^(1/(p.nat_degree - n : ℝ))) ∪ {(0 : ℝ)},
  { intros x hx,
    obtain ⟨m, hm⟩ := set.mem_range.mpr hx,
    by_cases hm_lt : m < p.nat_degree,
    { simp only [spectral_value_terms_of_lt_nat_degree hp hm_lt] at hm,
      rw ← hm,
      exact set.mem_union_left _ ⟨⟨m, hm_lt⟩, rfl⟩, },
    { simp only [spectral_value_terms_of_nat_degree_le hp (le_of_not_lt hm_lt)] at hm,
      rw hm,
      exact set.mem_union_right _ (set.mem_singleton _), }},
  exact set.finite.subset (set.finite.union (set.finite_range _) (set.finite_singleton _)) h_ss,
end

lemma spectral_value_terms_nonneg {p : R[X]} (hp : p.monic) (n : ℕ) :
  0 ≤ spectral_value_terms hp n :=
begin
  simp only [spectral_value_terms],
  split_ifs with h,
  { exact real.rpow_nonneg_of_nonneg (norm_nonneg _) _ },
  { exact le_refl _ },
end

lemma spectral_value_nonneg {p : R[X]} (hp : p.monic) :
  0 ≤ spectral_value hp :=
real.supr_nonneg (spectral_value_terms_nonneg hp)

variable [nontrivial R]

lemma spectral_value_X_sub_C (r : R) :
  spectral_value (@polynomial.monic_X_sub_C _ _ r) = ‖ r ‖ := 
begin
  rw spectral_value, rw spectral_value_terms,
  simp only [polynomial.nat_degree_X_sub_C, nat.lt_one_iff, polynomial.coeff_sub,
    nat.cast_one, one_div],
  suffices : (⨆ (n : ℕ), ite (n = 0) ‖ r ‖  0) = ‖ r ‖,
  { rw ← this,
    apply congr_arg,
    ext n,
    by_cases hn : n = 0,
    { rw [if_pos hn, if_pos hn, hn, nat.cast_zero, sub_zero, polynomial.coeff_X_zero,
        polynomial.coeff_C_zero, zero_sub, norm_neg, inv_one, real.rpow_one] },
    { rw [if_neg hn, if_neg hn], }},
  { apply csupr_eq_of_forall_le_of_forall_lt_exists_gt,
    { intro n,
      split_ifs,
      exact le_refl _, 
      exact norm_nonneg _ },
    { intros x hx, use 0,
      simp only [eq_self_iff_true, if_true, hx], }}
end

lemma spectral_value_X_pow (n : ℕ) :
  spectral_value (@polynomial.monic_X_pow R _ n) = 0 := 
begin
  rw spectral_value, rw spectral_value_terms,
  simp_rw [polynomial.coeff_X_pow n, polynomial.nat_degree_X_pow],
  convert csupr_const,
  ext m,
  by_cases hmn : m < n,
  { rw [if_pos hmn, real.rpow_eq_zero_iff_of_nonneg (norm_nonneg _), if_neg (ne_of_lt hmn),
      norm_zero, one_div, ne.def, inv_eq_zero, ← nat.cast_sub (le_of_lt hmn), nat.cast_eq_zero,
      nat.sub_eq_zero_iff_le],
    exact ⟨eq.refl _, not_le_of_lt hmn⟩ },
  { rw if_neg hmn },
  apply_instance, 
end

end seminormed

section normed

variables [normed_ring R] 

lemma spectral_value_eq_zero_iff [nontrivial R] {p : R[X]} (hp : p.monic) :
  spectral_value hp = 0 ↔ p = polynomial.X^p.nat_degree := 
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rw spectral_value at h,
    ext,
    rw polynomial.coeff_X_pow,
    by_cases hn : n = p.nat_degree,
    { rw [if_pos hn, hn, polynomial.coeff_nat_degree], exact hp, },
    { rw if_neg hn,
      { by_cases hn' : n < p.nat_degree,
        { have h_le : supr (spectral_value_terms hp) ≤ 0 := le_of_eq h,
          have h_exp : 0 < 1 / ((p.nat_degree : ℝ) - n),
          { rw [one_div_pos, ← nat.cast_sub (le_of_lt hn'), nat.cast_pos],
            exact nat.sub_pos_of_lt hn', },
          have h0 : (0 : ℝ) = 0^(1 / ((p.nat_degree : ℝ) - n)),
          { rw real.zero_rpow (ne_of_gt h_exp), },
          rw [supr, cSup_le_iff (spectral_value_terms_bdd_above hp)
            (set.range_nonempty _)] at h_le,
          specialize h_le (spectral_value_terms hp n) ⟨n, rfl⟩,
          simp only [spectral_value_terms, if_pos hn'] at h_le,
          rw [h0, real.rpow_le_rpow_iff (norm_nonneg _) (le_refl _) h_exp] at h_le,
          exact norm_eq_zero.mp (le_antisymm h_le (norm_nonneg _)) },
        { exact polynomial.coeff_eq_zero_of_nat_degree_lt 
            (lt_of_le_of_ne (le_of_not_lt hn') (ne_comm.mpr hn)) }}}},
  { convert spectral_value_X_pow p.nat_degree,
    apply_instance }
end

end normed

lemma polynomial.nat_degree_pos_of_monic_of_root  {K : Type*} [normed_field K] {L : Type*} [field L]
  [algebra K L] {p : K[X]} (hp : p.monic) {x : L} (hx : polynomial.aeval x p = 0) : 
  0 < p.nat_degree := 
polynomial.nat_degree_pos_of_aeval_root (polynomial.ne_zero_of_ne_zero_of_monic one_ne_zero hp) hx
  ((injective_iff_map_eq_zero (algebra_map K L)).mp (algebra_map K L).injective)


/- In this section we prove Proposition 3.1.2/1 from BGR. -/
section bdd_by_spectral_value
variables {K : Type*} [normed_field K] {L : Type*} [field L] [algebra K L]


-- Part (1): the norm of any root of p is bounded by the spectral value of p.
lemma root_norm_le_spectral_value {f : algebra_norm K L}
  (hf_pm : is_pow_mul f) (hf_na : is_nonarchimedean f) (hf1 : f 1 ≤ 1)
  {p : K[X]} (hp : p.monic) {x : L} (hx : polynomial.aeval x p = 0) : f x ≤ spectral_value hp := 
begin
  by_cases hx0 : f x = 0,
  { rw hx0, exact spectral_value_nonneg hp, },
  { by_contra' h_ge,
    have hn_lt : ∀ (n : ℕ) (hn : n < p.nat_degree), ‖ p.coeff n ‖ < (f x)^ (p.nat_degree - n),
    { intros n hn,
      have hexp : (‖p.coeff n ‖^(1/(p.nat_degree - n : ℝ)))^(p.nat_degree - n) = ‖ p.coeff n ‖,
      { rw [← real.rpow_nat_cast, ← real.rpow_mul (norm_nonneg _), mul_comm, 
          real.rpow_mul (norm_nonneg _), real.rpow_nat_cast, ← nat.cast_sub (le_of_lt hn), one_div,
          real.pow_nat_rpow_nat_inv (norm_nonneg _) (ne_of_gt (tsub_pos_of_lt hn))], },
      have h_base : ‖ p.coeff n ‖^(1/(p.nat_degree - n : ℝ)) < f x,
      { rw [spectral_value, supr, set.finite.cSup_lt_iff (spectral_value_terms_finite_range hp)
          (set.range_nonempty (spectral_value_terms hp))] at h_ge,
        have h_rg : ‖ p.coeff n ‖^ (1 / (p.nat_degree - n : ℝ)) ∈
          set.range (spectral_value_terms hp),
        { use n, simp only [spectral_value_terms, if_pos hn] },
        exact h_ge (‖ p.coeff n ‖₊ ^ (1 / (↑(p.nat_degree) - ↑n))) h_rg },
      rw [← hexp, ← real.rpow_nat_cast, ← real.rpow_nat_cast],
      exact real.rpow_lt_rpow (real.rpow_nonneg_of_nonneg (norm_nonneg _) _) h_base 
        (nat.cast_pos.mpr (tsub_pos_of_lt hn)) },
    have h_deg : 0 < p.nat_degree := polynomial.nat_degree_pos_of_monic_of_root hp hx,
    have : ‖ (1 : K) ‖ = 1 := norm_one,
    have h_lt : f ((finset.range (p.nat_degree)).sum (λ (i : ℕ), p.coeff i • x ^ i)) < 
      f (x^(p.nat_degree)),
    { have hn' : ∀ (n : ℕ) (hn : n < p.nat_degree), f (p.coeff n • x ^ n) < f (x^(p.nat_degree)),
      { intros n hn,
        by_cases hn0 : n = 0,
        { rw [hn0, pow_zero, map_smul_eq_mul, hf_pm _ (nat.succ_le_iff.mpr h_deg),
            ← nat.sub_zero p.nat_degree, ← hn0],
          exact mul_lt_of_lt_of_le_one_of_nonneg (hn_lt n hn) hf1 (norm_nonneg _) },
        { have : p.nat_degree = (p.nat_degree - n) + n,
          { rw nat.sub_add_cancel (le_of_lt hn), },
          rw [map_smul_eq_mul, hf_pm _ (nat.succ_le_iff.mp (pos_iff_ne_zero.mpr hn0)), 
            hf_pm _ (nat.succ_le_iff.mpr h_deg), this, pow_add],
          exact (mul_lt_mul_right (pow_pos (lt_of_le_of_ne (map_nonneg _ _) (ne.symm hx0)) _)).mpr
            (hn_lt n hn), }},
      obtain ⟨m, hm_in, hm⟩ := is_nonarchimedean_finset_range_add_le hf_na p.nat_degree 
        (λ (i : ℕ), p.coeff i • x ^ i),
      exact lt_of_le_of_lt hm (hn' m (hm_in h_deg))  },
    have h0 : f 0 ≠ 0,
    { have h_eq : f 0 = f (x^(p.nat_degree)),
      { rw [← hx, polynomial.aeval_eq_sum_range, finset.sum_range_succ, add_comm, hp.coeff_nat_degree,
        one_smul, ← max_eq_left_of_lt h_lt], 
        exact is_nonarchimedean_add_eq_max_of_ne hf_na (ne_of_lt h_lt) },
      rw h_eq,
      exact ne_of_gt (lt_of_le_of_lt (map_nonneg _ _) h_lt) },
    exact h0 (map_zero _), } 
end

lemma polynomial.monic_of_prod (p : K[X]) {n : ℕ} (b : fin n → L) (hp : polynomial.map_alg K L p =
  finprod (λ (k : fin n), polynomial.X - (polynomial.C (b k)))) : p.monic :=
begin
  have hprod : (finprod (λ (k : fin n), polynomial.X - polynomial.C (b k))).monic,
  { rw finprod_eq_prod_of_fintype,
    exact polynomial.monic_prod_of_monic _ _ (λ m hm, polynomial.monic_X_sub_C (b m)) },
  rw [← hp, polynomial.map_alg_eq_map] at hprod,
  exact polynomial.monic_of_injective (algebra_map K L).injective hprod,
end

lemma polynomial.monic_of_prod' (p : K[X]) (s : multiset L) (hp : polynomial.map_alg K L p =
  (multiset.map (λ (a : L), polynomial.X - polynomial.C a) s).prod) : p.monic :=
begin
  have hprod : ((multiset.map (λ (a : L), polynomial.X - polynomial.C a) s).prod).monic,
  { exact polynomial.monic_multiset_prod_of_monic _ _ (λ m hm, polynomial.monic_X_sub_C m) },
  rw [← hp, polynomial.map_alg_eq_map] at hprod,
  exact polynomial.monic_of_injective (algebra_map K L).injective hprod,
end

lemma polynomial.C_finset_add {α : Type*} (s : finset α) (b : α → K) :
  s.sum (λ (x : α), polynomial.C (b x)) = polynomial.C (s.sum b) := 
begin
  classical,
  apply s.induction_on,
  { simp only [finset.sum_empty, map_zero] },
  { intros a s ha hs,
    rw [finset.sum_insert ha, finset.sum_insert ha, hs, polynomial.C_add], }
end

lemma polynomial.C_finset_prod {α : Type*} (s : finset α) (b : α → K) :
  s.prod (λ (x : α), polynomial.C (b x)) = polynomial.C (s.prod  b) := 
begin
  classical,
  apply s.induction_on,
  { simp only [finset.prod_empty, map_one] },
  { intros a s ha hs,
    rw [finset.prod_insert ha, finset.prod_insert ha, hs, polynomial.C_mul], }
end

lemma prod_X_add_C_nat_degree {n : ℕ} (b : fin n → L) :
  (finset.univ.prod (λ (i : fin n), polynomial.X - polynomial.C (b i))).nat_degree = n :=
begin
  rw polynomial.nat_degree_prod _ _ (λ m hm, polynomial.X_sub_C_ne_zero (b m)),
  simp only [polynomial.nat_degree_X_sub_C, finset.sum_const, finset.card_fin,
    algebra.id.smul_eq_mul, mul_one],
end

lemma finset.powerset_len_nonempty' {α : Type*} {n : ℕ} {s : finset α} (h : n ≤ s.card) :
  (finset.powerset_len n s).nonempty :=
begin
  classical,
  induction s using finset.induction_on with x s hx IH generalizing n,
  { rw [finset.card_empty, le_zero_iff] at h,
    rw [h, finset.powerset_len_zero],
    exact finset.singleton_nonempty _, },
  { cases n,
    { simp },
    { rw [finset.card_insert_of_not_mem hx, nat.succ_le_succ_iff] at h,
      rw finset.powerset_len_succ_insert hx,
      refine finset.nonempty.mono _ ((IH h).image (insert x)),
      convert (finset.subset_union_right _ _) }}
end

lemma is_nonarchimedean_finset_powerset_image_add {f : algebra_norm K L} (hf_pm : is_pow_mul f)
  (hf_na : is_nonarchimedean f) {n : ℕ} (hn : 0 < n) (b : fin n → L) {m : ℕ} (hm : m < n) :
  ∃ (s : (finset.powerset_len (fintype.card (fin n) - m) (@finset.univ (fin n) _))),
    f ((finset.powerset_len (fintype.card (fin n) - m) finset.univ).sum 
      (λ (t : finset (fin n)), t.prod (λ (i : fin n), -b i))) ≤
    f (s.val.prod (λ (i : fin n), -b i)) := 
begin
  set g := (λ (t : finset (fin n)), t.prod (λ (i : fin n), -b i)) with hg,
  obtain ⟨b, hb_in, hb⟩ := is_nonarchimedean_finset_image_add hf_na g 
    (finset.powerset_len (fintype.card (fin n) - m) finset.univ),
  have hb_ne : (finset.powerset_len (fintype.card (fin n) - m)
    (finset.univ : finset(fin n))).nonempty,
  { rw [fintype.card_fin],
    have hmn : n - m ≤ (finset.univ : finset (fin n)).card,
    { rw [finset.card_fin], 
      exact nat.sub_le n m },
    exact finset.powerset_len_nonempty' hmn, },
  use [⟨b, hb_in hb_ne⟩, hb],
end

lemma is_nonarchimedean_multiset_powerset_image_add {f : algebra_norm K L} (hf_pm : is_pow_mul f)
  (hf_na : is_nonarchimedean f) (s : multiset L) {m : ℕ} (hm : m < s.card) :
  ∃ t : multiset L, t.card = s.card - m ∧ (∀ x : L, x ∈ t → x ∈ s) ∧ 
    f (multiset.map multiset.prod (multiset.powerset_len (s.card - m) s)).sum ≤ f (t.prod) := 
begin
  set g := (λ (t : multiset L), t.prod) with hg,
  obtain ⟨b, hb_in, hb_le⟩ := is_nonarchimedean_multiset_image_add hf_na g
    (multiset.powerset_len (s.card - m) s),
  have hb : b ≤ s ∧ b.card = s.card - m,
  { rw [← multiset.mem_powerset_len],
    apply hb_in,
    rw [multiset.card_powerset_len],
    exact nat.choose_pos ((s.card).sub_le m), },
  refine ⟨b, hb.2, (λ x hx, multiset.mem_of_le hb.left hx), hb_le⟩,
end

/- lemma finset.esymm_map_val {σ R} [comm_semiring R] (f : σ → R) (s : finset σ) (n : ℕ) :
  (s.val.map f).esymm n = (s.powerset_len n).sum (λ t, t.prod f) :=
begin
  rw [multiset.esymm, multiset.powerset_len_map, ← finset.map_val_val_powerset_len],
  simpa only [multiset.map_map],
end
 -/
-- (multiset.map (λ (a : L), X - ⇑C a) s).prod
open_locale classical


open multiset
@[to_additive le_sum_of_subadditive_on_pred]
lemma multiset.le_prod_of_submultiplicative_on_pred'  {α β : Type*}  [comm_monoid α] 
  [ordered_comm_ring β]
  (f : α → β) (p : α → Prop) (h_nonneg : ∀ a, 0 ≤ f a) (h_one : f 1 = 1) (hp_one : p 1)
  (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b)
  (hp_mul : ∀ a b, p a → p b → p (a * b)) (s : multiset α) (hps : ∀ a, a ∈ s → p a) :
  f s.prod ≤ (s.map f).prod :=
begin
  revert s,
  refine multiset.induction _ _,
  { simp [le_of_eq h_one] },
  intros a s hs hpsa,
  have hps : ∀ x, x ∈ s → p x, from λ x hx, hpsa x (multiset.mem_cons_of_mem hx),
  have hp_prod : p s.prod, from multiset.prod_induction p s hp_mul hp_one hps,
  rw [prod_cons, map_cons, prod_cons],
  refine (h_mul a s.prod (hpsa a (mem_cons_self a s)) hp_prod).trans _,
  exact mul_le_mul_of_nonneg_left (hs hps) (h_nonneg _),
end

@[to_additive le_sum_of_subadditive]
lemma multiset.le_prod_of_submultiplicative' {α β : Type*} [comm_monoid α] [ordered_comm_ring β]
  (f : α → β) (h_nonneg : ∀ a, 0 ≤ f a) (h_one : f 1 = 1) (h_mul : ∀ a b, f (a * b) ≤ f a * f b) 
  (s : multiset α) : f s.prod ≤ (s.map f).prod :=
multiset.le_prod_of_submultiplicative_on_pred' f (λ i, true) h_nonneg h_one trivial
  (λ x y _ _ , h_mul x y) (by simp) s (by simp)

theorem finset.le_prod_of_submultiplicative' {ι M N : Type*} [comm_monoid M] 
  [ordered_comm_ring N] (f : M → N) (h_nonneg : ∀ a, 0 ≤ f a) (h_one : f 1 = 1) 
  (h_mul : ∀ (x y : M), f (x * y) ≤ f x * f y) (s : finset ι) (g : ι → M) :
f (s.prod (λ (i : ι), g i)) ≤ s.prod (λ (i : ι), f (g i)) := 
begin
  refine le_trans (multiset.le_prod_of_submultiplicative' f h_nonneg h_one h_mul _) _,
  rw multiset.map_map,
  refl,
end

/-- Part (2): if p splits into linear factors over B, then its spectral value equals the maximum
  of the norms of its roots. -/
lemma max_root_norm_eq_spectral_value  {f : algebra_norm K L} (hf_pm : is_pow_mul f)
  (hf_na : is_nonarchimedean f) (hf1 : f 1 = 1) (p : K[X]) {n : ℕ} (hn : 0 < n) (b : fin n → L)
  (hp : polynomial.map_alg K L p = finprod (λ (k : fin n), polynomial.X - (polynomial.C (b k))))
  (h_isom : ∀ x y : K, f ((algebra_map K L y) - algebra_map K L x) = nndist x y) :
  supr (f ∘ b) = spectral_value (p.monic_of_prod b hp) := 
begin
  apply le_antisymm,
  { haveI : nonempty (fin n) := fin.pos_iff_nonempty.mp hn,
    apply csupr_le,
    rintros m,
    have hm : polynomial.aeval (b m) p = 0,
    { have hm' : polynomial.aeval (b m) ((polynomial.map_alg K L) p) = 0,
      { have hd1 : (polynomial.aeval (b m)) (polynomial.X - polynomial.C (b m)) = 0,
        { rw [polynomial.coe_aeval_eq_eval, polynomial.eval_sub, polynomial.eval_X,
            polynomial.eval_C, sub_self] },
        rw [hp, finprod_eq_prod_of_fintype, polynomial.aeval_def, polynomial.eval₂_finset_prod],
        exact finset.prod_eq_zero (finset.mem_univ m) hd1, },
      rw [polynomial.map_alg_eq_map, polynomial.aeval_map_algebra_map] at hm',
      exact hm', },
    rw function.comp_apply,
    exact root_norm_le_spectral_value hf_pm hf_na (le_of_eq hf1) _ hm, },
  { haveI : nonempty (fin n) := fin.pos_iff_nonempty.mp hn,
    have h_supr : 0 ≤ supr (f ∘ b) := (real.supr_nonneg (λ x, map_nonneg f (b x))),
    apply csupr_le,
    intros m,
    by_cases hm : m < p.nat_degree,
    { rw spectral_value_terms_of_lt_nat_degree _ hm,
      have h : 0 < (p.nat_degree - m : ℝ),
      { rw [sub_pos, nat.cast_lt], exact hm },
      rw [← real.rpow_le_rpow_iff (real.rpow_nonneg_of_nonneg (norm_nonneg _) _) h_supr h, 
        ← real.rpow_mul (norm_nonneg _), one_div_mul_cancel (ne_of_gt h), real.rpow_one,
        ← nat.cast_sub (le_of_lt hm), real.rpow_nat_cast],
      have hpn : n = p.nat_degree,
      { rw [← polynomial.nat_degree_map (algebra_map K L), ← polynomial.map_alg_eq_map, hp,
          finprod_eq_prod_of_fintype, prod_X_add_C_nat_degree] },
      have hc : ‖ p.coeff m ‖ = f (((polynomial.map_alg K L) p).coeff m),
      { rw [← algebra_norm.extends_norm hf1, polynomial.map_alg_eq_map, polynomial.coeff_map] },
        rw [hc, hp, finprod_eq_prod_of_fintype],
        simp_rw [sub_eq_add_neg, ← polynomial.C_neg, finset.prod_eq_multiset_prod, ← pi.neg_apply,
          ← multiset.map_map (λ x : L, X + C x) (-b)],
        have hm_le' : m ≤ multiset.card (multiset.map (-b) finset.univ.val),
        { have : multiset.card finset.univ.val = finset.card finset.univ := rfl,
          rw [multiset.card_map, this, finset.card_fin n, hpn],
          exact (le_of_lt hm) },
        rw multiset.prod_X_add_C_coeff _ hm_le',
      have : m < n,
      { rw hpn, exact hm },
      obtain ⟨s, hs⟩ := is_nonarchimedean_finset_powerset_image_add hf_pm hf_na hn b this,
      rw finset.esymm_map_val,
      have h_card : multiset.card (multiset.map (-b) finset.univ.val) = fintype.card (fin n),
      { rw [multiset.card_map], refl, },
      rw h_card,
      apply le_trans hs,
      have  h_pr: f (s.val.prod (λ (i : fin n), -b i)) ≤ s.val.prod (λ (i : fin n), f(-b i)),
      { exact finset.le_prod_of_submultiplicative' f (map_nonneg _) hf1 (map_mul_le_mul _) _ _ },
      apply le_trans h_pr,
      have : s.val.prod (λ (i : fin n), f (-b i)) ≤ s.val.prod (λ (i : fin n), supr (f ∘ b)),
      { apply finset.prod_le_prod,
        { intros i hi, exact map_nonneg _ _, },
        { intros i hi, 
          rw map_neg_eq_map,
          exact le_csupr (set.finite.bdd_above (set.range (f ∘ b)).to_finite) _, }},
      apply le_trans this,
      apply le_of_eq,
      simp only [subtype.val_eq_coe, finset.prod_const],
      suffices h_card : (s : finset (fin n)).card = p.nat_degree - m,
      { rw h_card },
      have hs' := s.property,
      simp only [subtype.val_eq_coe, fintype.card_fin, finset.mem_powerset_len] at hs',
      rw [hs'.right, hpn],  },
    rw spectral_value_terms_of_nat_degree_le _ (le_of_not_lt hm),
    exact h_supr, }, 
end

lemma multiset.max (f : L → ℝ) {s : multiset L} (hs : s.to_finset.nonempty) :
  ∃ y : L, y ∈ s ∧ ∀ z : L, z ∈ s → f z ≤ f y := 
begin
  have hsf : (multiset.map f s).to_finset.nonempty,
  { obtain ⟨x, hx⟩ := hs.bex,
    exact ⟨f x, multiset.mem_to_finset.mpr (multiset.mem_map.mpr
      ⟨x, (multiset.mem_to_finset.mp hx), rfl⟩)⟩ },
  have h := (s.map f).to_finset.max'_mem hsf,
  rw [multiset.mem_to_finset, multiset.mem_map] at h,
  obtain ⟨y, hys, hymax⟩ := h,
  use [y, hys],
  intros z hz,
  rw hymax,
  exact finset.le_max' _ _ (multiset.mem_to_finset.mpr (multiset.mem_map.mpr ⟨z, hz, rfl⟩)),
end

lemma multiset.card_to_finset_pos {α : Type u_1} {m : multiset α} (hm : 0 < m.card) :
  0 < m.to_finset.card :=
begin
  obtain ⟨x, hx⟩ := multiset.card_pos_iff_exists_mem.mp hm,
  exact finset.card_pos.mpr ⟨x, multiset.mem_to_finset.mpr hx⟩,
end

lemma polynomial.aeval_root (s : multiset L) {x : L} (hx : x ∈ s) {p : K[X]}
  (hp : polynomial.map_alg K L p =
    (multiset.map (λ (a : L), polynomial.X - polynomial.C a) s).prod) : polynomial.aeval x p = 0 :=
begin
  have : polynomial.aeval x (polynomial.map_alg K L p) = polynomial.aeval x p,
  { rw [map_alg_eq_map, aeval_map_algebra_map] },
  rw [← this, hp, coe_aeval_eq_eval],
  have hy : (X - C x) ∣ (multiset.map (λ (a : L), X - C a) s).prod,
  { apply multiset.dvd_prod,
    simp only [multiset.mem_map, sub_right_inj, C_inj, exists_eq_right],
    exact hx },
  rw eval_eq_zero_of_dvd_of_eval_eq_zero hy,
  simp only [eval_sub, eval_X, eval_C, sub_self],
end

lemma real.multiset_prod_le_pow_card {t : multiset L} {f : algebra_norm K L} {y : L}
  (hf : ∀ (x : ℝ), x ∈ multiset.map f t → x ≤ f y) : 
  (map f t).prod ≤ f y ^ card (map f t) := 
begin
  set g : L → nnreal := λ x : L, ⟨f x, map_nonneg _ _⟩,
  have hg_le : (map g t).prod ≤ g y ^ card (map g t),
  { apply multiset.prod_le_pow_card,
    intros x hx,
    obtain ⟨a, hat, hag⟩ := mem_map.mp hx,
    rw [subtype.ext_iff, subtype.coe_mk] at hag,
    rw [← nnreal.coe_le_coe, subtype.coe_mk],
    exact hf (x : ℝ) (mem_map.mpr ⟨a, hat, hag⟩), },
  rw ← nnreal.coe_le_coe at hg_le,
  convert hg_le,
  { simp only [nnreal.coe_multiset_prod, multiset.map_map, function.comp_app, subtype.coe_mk] },
  { simp only [card_map] }
end

lemma real.multiset_le_prod_of_submultiplicative {α : Type*} [comm_monoid α] {f : α → ℝ}
  (h_nonneg : ∀ a, 0 ≤ f a) (h_one : f 1 = 1) (h_mul : ∀ a b, f (a * b) ≤ f a * f b)
  (s : multiset α) : f s.prod ≤ (s.map f).prod := 
begin
  set g : α → nnreal := λ x : α, ⟨f x, h_nonneg _ ⟩,
  have hg_le : g s.prod ≤ (s.map g).prod,
  { apply multiset.le_prod_of_submultiplicative,
    { ext, rw [subtype.coe_mk, nonneg.coe_one, h_one], },
    { intros a b, 
      simp only [← nnreal.coe_le_coe, subtype.coe_mk, nonneg.mk_mul_mk],
      exact h_mul _ _, }},
  rw ← nnreal.coe_le_coe at hg_le,
  convert hg_le,
  simp only [nnreal.coe_multiset_prod, multiset.map_map, function.comp_app, subtype.coe_mk],
end

lemma max_root_norm_eq_spectral_value' {f : algebra_norm K L} (hf_pm : is_pow_mul f)
  (hf_na : is_nonarchimedean f) (hf1 : f 1 = 1) (p : K[X]) (s : multiset L) 
  (hp : polynomial.map_alg K L p = (multiset.map (λ (a : L), polynomial.X - polynomial.C a) s).prod)
  (h_isom : ∀ x y : K, f ((algebra_map K L y) - algebra_map K L x) = nndist x y) :
  supr (λ x : L, if x ∈ s then f x else 0 ) = spectral_value (p.monic_of_prod' s hp) :=
begin
  have h_le : 0 ≤ ⨆ (x : L), ite (x ∈ s) (f x) 0,
  { apply real.supr_nonneg,
    intro x,
    split_ifs,
    exacts [map_nonneg _ _, le_refl _] },
   apply le_antisymm,
  { apply csupr_le,
    rintros x,
    by_cases hx : x ∈ s,
    { have hx0 : polynomial.aeval x p = 0 := polynomial.aeval_root s hx hp,
      rw if_pos hx,
      exact root_norm_le_spectral_value hf_pm hf_na (le_of_eq hf1) _ hx0, },
    { rw if_neg hx,
      exact spectral_value_nonneg _, }},
  { apply csupr_le,
    intros m,
    by_cases hm : m < p.nat_degree,
    { rw spectral_value_terms_of_lt_nat_degree _ hm,
      have h : 0 < (p.nat_degree - m : ℝ),
      { rw [sub_pos, nat.cast_lt], exact hm },
      rw [← real.rpow_le_rpow_iff (real.rpow_nonneg_of_nonneg (norm_nonneg _) _) h_le h,
        ← real.rpow_mul (norm_nonneg _), one_div_mul_cancel (ne_of_gt h),
        real.rpow_one, ← nat.cast_sub (le_of_lt hm), real.rpow_nat_cast],
      have hps : s.card = p.nat_degree,
      { rw [← polynomial.nat_degree_map (algebra_map K L), ← polynomial.map_alg_eq_map, hp, 
          nat_degree_multiset_prod_X_sub_C_eq_card], },
      have hc : ‖ p.coeff m ‖ = f (((polynomial.map_alg K L) p).coeff m),
      { rw [← algebra_norm.extends_norm hf1, polynomial.map_alg_eq_map, polynomial.coeff_map] },
      rw [hc, hp],
      have hm_le' : m ≤ s.card,
      { rw hps, exact le_of_lt hm, },
      rw multiset.prod_X_sub_C_coeff s hm_le',
      have h : f ((-1) ^ (s.card - m) * s.esymm (s.card - m)) = f (s.esymm (s.card - m)),
      { cases (neg_one_pow_eq_or L (s.card - m)) with h1 hn1,
        { rw [h1, one_mul] },
        { rw [hn1, neg_mul, one_mul, map_neg_eq_map], }},
      rw [h, multiset.esymm],
      have ht : ∃ t : multiset L, t.card = s.card - m ∧ (∀ x : L, x ∈ t → x ∈ s) ∧ 
      f (multiset.map multiset.prod (multiset.powerset_len (s.card - m) s)).sum ≤ f (t.prod),
      { have hm' : m < multiset.card s,
        { rw hps, exact hm, },
        exact is_nonarchimedean_multiset_powerset_image_add hf_pm hf_na s hm',  },

      obtain ⟨t, ht_card, hts, ht_ge⟩ := ht,
      apply le_trans ht_ge,

      have  h_pr: f (t.prod) ≤ (t.map f).prod,
      { exact real.multiset_le_prod_of_submultiplicative (map_nonneg _) hf1 (map_mul_le_mul _) _ },
      apply le_trans h_pr,
      have hs_ne : s.to_finset.nonempty,
      { rw [← finset.card_pos],
        apply multiset.card_to_finset_pos,
        rw hps,
        exact lt_of_le_of_lt (zero_le _) hm, },
      have hy : ∃ y : L, y ∈ s ∧ ∀ z : L, z ∈ s → f z ≤ f y := multiset.max f hs_ne,
      obtain ⟨y, hyx, hy_max⟩ := hy,
      have : (multiset.map f t).prod ≤ (f y) ^ (p.nat_degree - m),
      { have h_card : (p.nat_degree - m) = (t.map f).card,
        { rw [multiset.card_map, ht_card, ← hps] },
        have hx_le : ∀ (x : ℝ), x ∈ multiset.map f t → x ≤ f y,
        { intros r hr,
          obtain ⟨z, hzt, hzr⟩ := multiset.mem_map.mp hr,
          rw ← hzr,
          exact hy_max _ (hts _ hzt) },
        rw h_card,
        exact real.multiset_prod_le_pow_card hx_le, },

      have h_bdd : bdd_above (set.range (λ (x : L), ite (x ∈ s) (f x) 0)),
      { use f y,
        rw mem_upper_bounds,
        intros r hr,
        obtain ⟨z, hz⟩ := set.mem_range.mpr hr,
        simp only at hz,
        rw ← hz,
        split_ifs with h,
        { exact hy_max _ h },
        { exact map_nonneg _ _ }},
      apply le_trans this,
      apply pow_le_pow_of_le_left (map_nonneg _ _),
      apply le_trans _ (le_csupr h_bdd y),
      rw if_pos hyx },
    { simp only [spectral_value_terms],
      rw if_neg hm,
      exact h_le }},
end

end bdd_by_spectral_value

section alg_equiv

variables {S A B C: Type*} [comm_semiring S] [semiring A] [semiring B] [semiring C] [algebra S A]
  [algebra S B] [algebra S C]

def alg_equiv.comp (f : A ≃ₐ[S] B) (g : B ≃ₐ[S] C) : A ≃ₐ[S] C :=
{ to_fun    := g.to_fun ∘ f.to_fun,
  inv_fun   := f.inv_fun ∘ g.inv_fun,
  left_inv  :=  λ x, by simp only [alg_equiv.inv_fun_eq_symm, alg_equiv.to_fun_eq_coe,
    function.comp_app, alg_equiv.symm_apply_apply],
  right_inv := λ x, by simp only [alg_equiv.to_fun_eq_coe, alg_equiv.inv_fun_eq_symm,
    function.comp_app, alg_equiv.apply_symm_apply],
  map_mul'  := λ x y, by simp only [alg_equiv.to_fun_eq_coe, function.comp_app, map_mul],
  map_add'  := λ x y, by simp only [alg_equiv.to_fun_eq_coe, function.comp_app, map_add],
  commutes' := λ x, by simp only [alg_equiv.to_fun_eq_coe, function.comp_app, alg_equiv.commutes] }

lemma alg_equiv.comp_apply (f : A ≃ₐ[S] B) (g : B ≃ₐ[S] C) (x : A) : f.comp g x = g (f x) := rfl

end alg_equiv

/- In this section we prove Theorem 3.2.1/2 from BGR. -/

section spectral_norm

variables {K : Type*} [normed_field K] {L : Type*} [field L] [algebra K L]
(h_alg : algebra.is_algebraic K L)

-- The spectral norm |y|_sp is the spectral value of the minimal polynomial of y over K.
def spectral_norm (y : L) : ℝ :=
spectral_value (minpoly.monic (is_algebraic_iff_is_integral.mp (h_alg y)))

lemma spectral_value.eq_of_tower {E : Type*} [field E] [algebra K E] [algebra E L]
  [is_scalar_tower K E L] (h_alg_E : algebra.is_algebraic K E) (h_alg_L : algebra.is_algebraic K L)
  (x : E) : spectral_norm h_alg_E x = spectral_norm h_alg_L (algebra_map E L x) :=
begin
  have hx : minpoly K x = minpoly K  (algebra_map E L x),
  { exact minpoly.eq_of_algebra_map_eq (algebra_map E L).injective 
      (is_algebraic_iff_is_integral.mp (h_alg_E x)) rfl, },
  simp only [spectral_norm, hx],
end

lemma intermediate_field.is_algebraic (h_alg_L : algebra.is_algebraic K L)
  (E : intermediate_field K L) :
  algebra.is_algebraic K E := λ y,
begin
  obtain ⟨p, hp0, hp⟩ := h_alg_L ↑y,
  rw [subalgebra.aeval_coe, subalgebra.coe_eq_zero] at hp,
  exact ⟨p, hp0, hp⟩,
end

variable (E : intermediate_field K L)

/- Auxiliary instances to avoid timeouts. -/
instance aux : is_scalar_tower K E E := infer_instance

instance aux' : is_scalar_tower K E (algebraic_closure E) := 
@algebraic_closure.is_scalar_tower E _ K E _ _ _ _ _ (aux E)

instance : is_scalar_tower K E (normal_closure K ↥E (algebraic_closure ↥E)) := infer_instance

instance : normal K (algebraic_closure K) := 
normal_iff.mpr (λ x, ⟨is_algebraic_iff_is_integral.mp (algebraic_closure.is_algebraic K x), 
  is_alg_closed.splits_codomain (minpoly K x)⟩)

lemma intermediate_field.adjoin_simple.alg_closure_normal (h_alg : algebra.is_algebraic K L)
  (x : L) : normal K (algebraic_closure K⟮x⟯) := 
normal_iff.mpr (λ y, ⟨is_algebraic_iff_is_integral.mp (algebra.is_algebraic_trans 
  (intermediate_field.is_algebraic h_alg K⟮x⟯) (algebraic_closure.is_algebraic K⟮x⟯) y),
  is_alg_closed.splits_codomain (minpoly K y)⟩)

lemma intermediate_field.adjoin_double.alg_closure_normal (h_alg : algebra.is_algebraic K L)
  (x y : L) : normal K (algebraic_closure K⟮x, y⟯) := 
normal_iff.mpr (λ z, ⟨is_algebraic_iff_is_integral.mp (algebra.is_algebraic_trans 
  (intermediate_field.is_algebraic h_alg K⟮x, y⟯) (algebraic_closure.is_algebraic K⟮x, y⟯) z),
  is_alg_closed.splits_codomain (minpoly K z)⟩)

lemma spectral_value.eq_normal (h_alg_L : algebra.is_algebraic K L) 
  (E : intermediate_field K L) (x : E) :
  spectral_norm (normal_closure.is_algebraic K E (intermediate_field.is_algebraic h_alg_L E))
    (algebra_map E (normal_closure K E (algebraic_closure E)) x) = 
      spectral_norm h_alg_L (algebra_map E L x) :=
begin
  simp only [spectral_norm, spectral_value],
  have h_min : minpoly K (algebra_map ↥E ↥(normal_closure K ↥E (algebraic_closure ↥E)) x) = 
    minpoly K (algebra_map ↥E L x),
  { have hx : is_integral K x := 
    is_algebraic_iff_is_integral.mp (intermediate_field.is_algebraic_iff.mpr (h_alg_L ↑x)),
    rw [← minpoly.eq_of_algebra_map_eq 
      ((algebra_map ↥E ↥(normal_closure K E (algebraic_closure E))).injective) hx rfl,
      minpoly.eq_of_algebra_map_eq (algebra_map ↥E L).injective hx rfl] },
  simp_rw h_min,
end

variable (y : L)

lemma spectral_norm_zero : spectral_norm h_alg (0 : L) = 0 := 
begin
  have h_lr: list.range 1 = [0] := rfl,
  rw [spectral_norm, spectral_value, spectral_value_terms, minpoly.zero, polynomial.nat_degree_X],
  convert csupr_const,
  ext m,
  by_cases hm : m < 1,
  { rw [if_pos hm, nat.lt_one_iff.mp hm, nat.cast_one, nat.cast_zero, sub_zero,
      div_one, real.rpow_one, polynomial.coeff_X_zero, norm_zero] },
  { rw if_neg hm },
  apply_instance,
end

lemma spectral_norm_nonneg (y : L) : 0 ≤  spectral_norm h_alg y := 
le_csupr_of_le (spectral_value_terms_bdd_above (minpoly.monic
  (is_algebraic_iff_is_integral.mp (h_alg y)))) 0 (spectral_value_terms_nonneg _ 0)

lemma spectral_norm_zero_lt {y : L} (hy : y ≠ 0) : 0 < spectral_norm h_alg y := 
begin
  rw lt_iff_le_and_ne,
  refine ⟨spectral_norm_nonneg _ _, _⟩,
  rw [spectral_norm, ne.def, eq_comm, spectral_value_eq_zero_iff],
  have h0 : polynomial.coeff (minpoly K y) 0 ≠ 0  :=
  minpoly.coeff_zero_ne_zero (is_algebraic_iff_is_integral.mp (h_alg y)) hy,
  intro h,
  have h0' : (minpoly K y).coeff 0 = 0,
  { rw [h, polynomial.coeff_X_pow,
      if_neg (ne_of_lt ( minpoly.nat_degree_pos (is_algebraic_iff_is_integral.mp (h_alg y))))] },
  exact h0 h0', 
end

lemma spectral_norm_ne_zero_of_map_ne_zero {x : L} (hx : spectral_norm h_alg x = 0) : x = 0 :=
begin
  by_contra h0,
  exact (ne_of_gt (spectral_norm_zero_lt h_alg h0)) hx,
end

lemma spectral_norm.ge_norm {f : algebra_norm K L} (hf_pm : is_pow_mul f)
  (hf_na : is_nonarchimedean f) (hf1 : f 1 ≤ 1) (x : L) : f x ≤ spectral_norm h_alg x :=
begin
  apply root_norm_le_spectral_value hf_pm hf_na hf1,
  rw [minpoly.aeval],
end

lemma spectral_norm.aut_isom (σ : L ≃ₐ[K] L) (x : L) : 
  spectral_norm h_alg x = spectral_norm h_alg (σ x) :=
by simp only [spectral_norm, minpoly.eq_of_conj h_alg]

-- We first assume that the extension is finite and normal
section finite

variable (h_fin : finite_dimensional K L)

section normal

lemma extends_is_norm_le_one_class {f : L → ℝ}
  (hf_ext : function_extends (norm : K → ℝ) f) : f 1 ≤ 1:= 
by rw [← (algebra_map K L).map_one, hf_ext, norm_one]

lemma extends_is_norm_one_class {f : L → ℝ}
  (hf_ext : function_extends (norm : K → ℝ) f) : f 1 = 1 := 
by rw [← (algebra_map K L).map_one, hf_ext, norm_one]

lemma spectral_norm.max_of_fd_normal (h_fin : finite_dimensional K L) (hn : normal K L) 
  (hna : is_nonarchimedean (norm : K → ℝ)) {f : algebra_norm K L} (hf_pm : is_pow_mul f)
  (hf_na : is_nonarchimedean f) (hf_ext : function_extends (λ x : K, ‖ x ‖₊) f) (x : L) :
  spectral_norm h_alg x = supr (λ (σ : L ≃ₐ[K] L), f (σ x)) :=
begin
  refine le_antisymm _ (csupr_le (λ σ, root_norm_le_spectral_value hf_pm hf_na
      (extends_is_norm_le_one_class hf_ext) _ (minpoly.aeval_conj h_alg _ _))),
{ set p := minpoly K x with hp_def,
  have hp_sp : polynomial.splits (algebra_map K L) (minpoly K x) := hn.splits x,
  obtain ⟨s, hs⟩ := (polynomial.splits_iff_exists_multiset _).mp hp_sp,
  have : polynomial.map_alg K L p = map (algebra_map K L) p := rfl,
  have h_lc : (algebra_map K L) (minpoly K x).leading_coeff = 1,
  { have h1 : (minpoly K x).leading_coeff = 1,
    { rw ← monic, exact minpoly.monic (normal.is_integral hn x),},
    rw [h1, map_one] },
  rw [h_lc, map_one, one_mul] at hs,
  simp only [spectral_norm],
  rw ← max_root_norm_eq_spectral_value' hf_pm hf_na (extends_is_norm_one_class hf_ext) 
    _ _ hs (λ x y, by rw [← map_sub, hf_ext, nndist_comm, nndist_eq_nnnorm]),
  apply csupr_le,
  intros y,
  split_ifs,
  { have hy : ∃ σ : L ≃ₐ[K] L, σ x = y,
    { exact minpoly.conj_of_root' h_alg hn (polynomial.aeval_root s h hs), },
    obtain ⟨σ, hσ⟩ := hy,
    rw ← hσ,
    exact le_csupr (fintype.bdd_above_range _) σ, },
  { exact real.supr_nonneg (λ σ, map_nonneg _ _) }},
end

lemma spectral_norm.eq_seminorm_of_galois (h_fin : finite_dimensional K L) (hn : normal K L) 
  (hna : is_nonarchimedean (norm : K → ℝ)) :
  spectral_norm h_alg = alg_norm_of_galois h_fin hna := 
begin
  ext x,
  set f := classical.some (finite_extension_pow_mul_seminorm h_fin hna) with hf,
  have hf_pow : is_pow_mul f :=
  (classical.some_spec (finite_extension_pow_mul_seminorm h_fin hna)).1,
  have hf_ext : function_extends _ f :=
  (classical.some_spec (finite_extension_pow_mul_seminorm h_fin hna)).2.1,
  have hf_na : is_nonarchimedean f :=
  (classical.some_spec (finite_extension_pow_mul_seminorm h_fin hna)).2.2,
  rw spectral_norm.max_of_fd_normal h_alg h_fin hn hna hf_pow hf_na hf_ext,
  refl,
end

lemma spectral_norm.is_pow_mul_of_fd_normal (h_fin : finite_dimensional K L) (hn : normal K L) 
  (hna : is_nonarchimedean (norm : K → ℝ)) : is_pow_mul (spectral_norm h_alg) :=
begin
  rw spectral_norm.eq_seminorm_of_galois _ h_fin hn hna,
  exact alg_norm_of_galois_is_pow_mul h_fin hna,
end

def spectral_alg_norm_of_fd_normal (h_fin : finite_dimensional K L) (hn : normal K L) 
  (hna : is_nonarchimedean (norm : K → ℝ)) :
  algebra_norm K L :=
{ to_fun    := spectral_norm h_alg,
  map_zero' := by {rw spectral_norm.eq_seminorm_of_galois _ h_fin hn hna, exact map_zero _ },
  add_le'   := by {rw spectral_norm.eq_seminorm_of_galois _ h_fin hn hna, exact map_add_le_add _ },
  neg'      := by {rw spectral_norm.eq_seminorm_of_galois _ h_fin hn hna, exact map_neg_eq_map _ },
  mul_le'   := by {rw spectral_norm.eq_seminorm_of_galois _ h_fin hn hna, exact map_mul_le_mul _ },
  eq_zero_of_map_eq_zero' := λ x,
  by {rw spectral_norm.eq_seminorm_of_galois _ h_fin hn hna, exact eq_zero_of_map_eq_zero _ },
  smul'     := 
  by { rw spectral_norm.eq_seminorm_of_galois _ h_fin hn hna, 
       exact algebra_norm_class.map_smul_eq_mul _  }}

lemma spectral_alg_norm_of_fd_normal_def (h_fin : finite_dimensional K L) (hn : normal K L) 
  (hna : is_nonarchimedean (norm : K → ℝ)) (x : L) : 
  spectral_alg_norm_of_fd_normal h_alg h_fin hn hna x = spectral_norm h_alg x := 
rfl

lemma spectral_norm.is_nonarchimedean_of_fd_normal (h_fin : finite_dimensional K L) (hn : normal K L) 
  (hna : is_nonarchimedean (norm : K → ℝ))  :
  is_nonarchimedean (spectral_norm h_alg) :=
begin
  rw spectral_norm.eq_seminorm_of_galois _ h_fin hn hna,
  exact alg_norm_of_galois_is_nonarchimedean h_fin hna,
end

lemma spectral_norm.extends_norm_of_fd (h_fin : finite_dimensional K L) (hn : normal K L) 
  (hna : is_nonarchimedean (norm : K → ℝ)) :
  function_extends (norm : K → ℝ) (spectral_norm h_alg) :=
begin
  rw spectral_norm.eq_seminorm_of_galois _ h_fin hn hna,
  exact alg_norm_of_galois_extends h_fin hna,
end

/- lemma max_root_norm_eq_spectral_value (hf_pm : is_pow_mult f) (hf_na : is_nonarchimedean f)
  (hf_alg_norm : is_algebra_norm (normed_ring.to_is_norm K) f) (hf1 : is_norm_one_class f)
  (p : K[X]) {n : ℕ} (hn : 0 < n) (b : fin n → L)
  (hp : polynomial.map_alg K L p = finprod (λ (k : fin n), polynomial.X - (polynomial.C (b k))))
  (h_isom : ∀ x y : K, f ((algebra_map K L y) - algebra_map K L x) = nndist x y) :
  supr (f ∘ b) = spectral_value (p.monic_of_prod b hp) := -/

lemma spectral_norm.unique_of_fd_normal (h_fin : finite_dimensional K L) (hn : normal K L)
  (hna : is_nonarchimedean (norm : K → ℝ)) {f : algebra_norm K L} 
  (hf_pm : is_pow_mul f) (hf_na : is_nonarchimedean f) 
  (hf_ext : function_extends (λ x : K, ‖ x ‖₊) f)
  (hf_iso : ∀ (σ : L ≃ₐ[K] L) (x : L), f x = f (σ x))
  (x : L) : f x = spectral_norm h_alg x :=
begin
  have h_sup : supr (λ (σ : L ≃ₐ[K] L), f (σ x)) = f x,
  { rw ← @csupr_const _ (L ≃ₐ[K] L) _ _ (f x),
    exact supr_congr (λ σ, by rw hf_iso σ x), },
  rw [spectral_norm.max_of_fd_normal h_alg h_fin hn hna hf_pm  hf_na hf_ext, h_sup]
end

end normal

end finite

-- Now we let L/K be any algebraic extension

-- The spectral norm is a power-multiplicative K-algebra norm on L extending the norm on K.

lemma spectral_value.eq_normal' (h_alg_L : algebra.is_algebraic K L) 
  {E : intermediate_field K L} {x : L} (g : E) (h_map : algebra_map E L g = x) :
  spectral_norm (normal_closure.is_algebraic K E (intermediate_field.is_algebraic h_alg_L E))
    (algebra_map E (normal_closure K E (algebraic_closure E)) g) = spectral_norm h_alg_L x :=
begin
  rw ← h_map,
  exact spectral_value.eq_normal h_alg_L E g,
end

lemma spectral_norm_is_pow_mul (hna : is_nonarchimedean (norm : K → ℝ)) :
  is_pow_mul (spectral_norm h_alg) :=
begin
  intros x n hn,
  set E := K⟮x⟯ with hE,
  haveI h_fd_E : finite_dimensional K E := 
  intermediate_field.adjoin.finite_dimensional (is_algebraic_iff_is_integral.mp (h_alg x)),
  have h_alg_E : algebra.is_algebraic K E := intermediate_field.is_algebraic h_alg E,
  set g := intermediate_field.adjoin_simple.gen K x with hg,
  have h_map : algebra_map E L g^n = x^n := rfl,
  haveI h_normal : normal K (algebraic_closure ↥K⟮x⟯) := 
  intermediate_field.adjoin_simple.alg_closure_normal h_alg x,
  rw [← spectral_value.eq_normal' h_alg  _ (intermediate_field.adjoin_simple.algebra_map_gen K x),
    ← spectral_value.eq_normal' h_alg (g^n) h_map, map_pow],
  exact spectral_norm.is_pow_mul_of_fd_normal (normal_closure.is_algebraic K E h_alg_E)
    (normal_closure.is_finite_dimensional K E _) (normal_closure.normal K E _) hna _ hn,
end

lemma spectral_norm_smul (hna : is_nonarchimedean (norm : K → ℝ)) (k : K) (y : L) :
  spectral_norm h_alg (k • y) = ‖ k ‖₊ * spectral_norm h_alg y :=
begin
  set E := K⟮y⟯ with hE,
  haveI : normal K (algebraic_closure ↥E) := 
  intermediate_field.adjoin_simple.alg_closure_normal h_alg y,
  haveI h_fd_E : finite_dimensional K E := 
  intermediate_field.adjoin.finite_dimensional (is_algebraic_iff_is_integral.mp (h_alg y)),
  have h_alg_E : algebra.is_algebraic K E := intermediate_field.is_algebraic h_alg E,
  set g := intermediate_field.adjoin_simple.gen K y with hg,
  have hgy : k • y = (algebra_map ↥K⟮y⟯ L) (k • g) := rfl,
  have h : algebra_map K⟮y⟯ (normal_closure K K⟮y⟯ (algebraic_closure K⟮y⟯)) (k • g) = 
    k • algebra_map K⟮y⟯ (normal_closure K K⟮y⟯ (algebraic_closure K⟮y⟯)) g,
  { rw [algebra.algebra_map_eq_smul_one, algebra.algebra_map_eq_smul_one, smul_assoc] },
    rw [← spectral_value.eq_normal' h_alg g (intermediate_field.adjoin_simple.algebra_map_gen K y),
      hgy, ← spectral_value.eq_normal' h_alg (k • g) rfl, h],
    have h_alg' := normal_closure.is_algebraic K E h_alg_E,
    rw ← spectral_alg_norm_of_fd_normal_def h_alg' 
      (normal_closure.is_finite_dimensional K E (algebraic_closure E)) 
      (normal_closure.normal K E _) hna,
    exact map_smul_eq_mul _ _ _,    
end

lemma intermediate_field.adjoin_adjoin.finite_dimensional {x y : L} (hx : is_integral K x)
  (hy : is_integral K y) : finite_dimensional K K⟮x, y⟯ := 
begin
  haveI hx_fd : finite_dimensional K K⟮x⟯ := intermediate_field.adjoin.finite_dimensional hx,
  have hy' : is_integral K⟮x⟯ y := is_integral_of_is_scalar_tower hy,
  haveI hy_fd : finite_dimensional K⟮x⟯ K⟮x⟯⟮y⟯ := intermediate_field.adjoin.finite_dimensional hy',
  rw ← intermediate_field.adjoin_simple_adjoin_simple,
  apply finite_dimensional.trans K K⟮x⟯ K⟮x⟯⟮y⟯,
end

lemma intermediate_field.mem_adjoin_adjoin_left (F : Type u_1) [field F] {E : Type u_2} [field E]
  [algebra F E] (x y : E) : x ∈ F⟮x, y⟯ := 
begin
  rw [← intermediate_field.adjoin_simple_adjoin_simple, intermediate_field.adjoin_simple_comm],
  exact intermediate_field.subset_adjoin F⟮y⟯ {x} (set.mem_singleton x),
end

lemma intermediate_field.mem_adjoin_adjoin_right (F : Type u_1) [field F] {E : Type u_2} [field E]
  [algebra F E] (x y : E) : y ∈ F⟮x, y⟯ :=
begin
  rw ← intermediate_field.adjoin_simple_adjoin_simple,
  exact intermediate_field.subset_adjoin F⟮x⟯ {y} (set.mem_singleton y),
end

def intermediate_field.adjoin_adjoin.gen_1 (F : Type u_1) [field F] {E : Type u_2} [field E]
  [algebra F E] (x y : E) : F⟮x, y⟯ := 
⟨x, intermediate_field.mem_adjoin_adjoin_left F x y⟩

def intermediate_field.adjoin_adjoin.gen_2 (F : Type u_1) [field F] {E : Type u_2} [field E]
  [algebra F E] (x y : E) : F⟮x, y⟯ :=
⟨y, intermediate_field.mem_adjoin_adjoin_right F x y⟩

@[simp]
theorem intermediate_field.adjoin_adjoin.algebra_map_gen_1 (F : Type u_1) [field F] {E : Type u_2}
  [field E] [algebra F E] (x y : E) : 
  (algebra_map ↥F⟮x, y⟯ E) (intermediate_field.adjoin_adjoin.gen_1 F x y) = x := rfl

@[simp]
theorem intermediate_field.adjoin_adjoin.algebra_map_gen_2 (F : Type u_1) [field F] {E : Type u_2}
  [field E] [algebra F E] (x y : E) : 
  (algebra_map ↥F⟮x, y⟯ E) (intermediate_field.adjoin_adjoin.gen_2 F x y) = y := rfl

lemma spectral_norm_is_nonarchimedean (h : is_nonarchimedean (norm : K → ℝ)) :
  is_nonarchimedean (spectral_norm h_alg) :=
begin
  intros x y,
  set E := K⟮x, y⟯ with hE,
  haveI : normal K (algebraic_closure ↥E) := 
  intermediate_field.adjoin_double.alg_closure_normal h_alg x y,
  haveI h_fd_E : finite_dimensional K E :=
  intermediate_field.adjoin_adjoin.finite_dimensional (is_algebraic_iff_is_integral.mp (h_alg x))
    (is_algebraic_iff_is_integral.mp (h_alg y)),
  have h_alg_E : algebra.is_algebraic K E := intermediate_field.is_algebraic h_alg E,
  set gx := intermediate_field.adjoin_adjoin.gen_1 K x y with hgx,
  set gy := intermediate_field.adjoin_adjoin.gen_2 K x y with hgy,
  have hxy : x + y = (algebra_map K⟮x, y⟯ L) (gx + gy) := rfl,
  rw [hxy, ← spectral_value.eq_normal' h_alg (gx + gy) hxy,
    ← spectral_value.eq_normal' h_alg gx (intermediate_field.adjoin_adjoin.algebra_map_gen_1
    K x y), ← spectral_value.eq_normal' h_alg gy (intermediate_field.adjoin_adjoin.algebra_map_gen_2
    K x y), map_add],
  exact spectral_norm.is_nonarchimedean_of_fd_normal (normal_closure.is_algebraic K E h_alg_E)
    (normal_closure.is_finite_dimensional K E _)  (normal_closure.normal K E _) h _ _, 
end

lemma spectral_norm_mul (hna : is_nonarchimedean (norm : K → ℝ)) (x y : L)  :
  spectral_norm h_alg (x * y) ≤ spectral_norm h_alg x * spectral_norm h_alg y :=
begin
  set E := K⟮x, y⟯ with hE,
  haveI : normal K (algebraic_closure ↥E) := 
  intermediate_field.adjoin_double.alg_closure_normal h_alg x y,
  haveI h_fd_E : finite_dimensional K E :=
  intermediate_field.adjoin_adjoin.finite_dimensional (is_algebraic_iff_is_integral.mp (h_alg x))
    (is_algebraic_iff_is_integral.mp (h_alg y)),
  have h_alg_E : algebra.is_algebraic K E := intermediate_field.is_algebraic h_alg E,
  set gx := intermediate_field.adjoin_adjoin.gen_1 K x y with hgx,
  set gy := intermediate_field.adjoin_adjoin.gen_2 K x y with hgy,
  have hxy : x * y = (algebra_map K⟮x, y⟯ L) (gx * gy) := rfl,
  rw [hxy, ← spectral_value.eq_normal' h_alg (gx*gy) hxy,
    ← spectral_value.eq_normal' h_alg gx (intermediate_field.adjoin_adjoin.algebra_map_gen_1
    K x y), ← spectral_value.eq_normal' h_alg gy (intermediate_field.adjoin_adjoin.algebra_map_gen_2
    K x y), map_mul, ← spectral_alg_norm_of_fd_normal_def (normal_closure.is_algebraic K E h_alg_E)
    (normal_closure.is_finite_dimensional K E (algebraic_closure E)) 
    (normal_closure.normal K E _) hna],
  exact map_mul_le_mul _ _ _
end

lemma spectral_norm.extends (k : K) : spectral_norm h_alg (algebra_map K L k) = ‖ k ‖ :=
begin
  simp_rw [spectral_norm, minpoly.eq_X_sub_C_of_algebra_map_inj _ (algebra_map K L).injective],
  exact spectral_value_X_sub_C k,
end

lemma spectral_norm_neg (hna : is_nonarchimedean (norm : K → ℝ)) (y : L)  :
  spectral_norm h_alg (-y) = spectral_norm h_alg y :=
begin
  set E := K⟮y⟯ with hE,
  haveI : normal K (algebraic_closure ↥E) := 
  intermediate_field.adjoin_simple.alg_closure_normal h_alg y,
  haveI h_fd_E : finite_dimensional K E := 
  intermediate_field.adjoin.finite_dimensional (is_algebraic_iff_is_integral.mp (h_alg y)),
  have h_alg_E : algebra.is_algebraic K E := intermediate_field.is_algebraic h_alg E,
  set g := intermediate_field.adjoin_simple.gen K y with hg,
  have hy : - y = (algebra_map K⟮y⟯ L) (- g) := rfl,
  rw [← spectral_value.eq_normal' h_alg g (intermediate_field.adjoin_simple.algebra_map_gen K y), 
    hy, ← spectral_value.eq_normal' h_alg (-g) hy, map_neg, ← spectral_alg_norm_of_fd_normal_def 
      (normal_closure.is_algebraic K E h_alg_E)(normal_closure.is_finite_dimensional K E 
      (algebraic_closure E)) (normal_closure.normal K E _) hna],
    exact map_neg_eq_map _ _
end

def spectral_alg_norm (hna : is_nonarchimedean (norm : K → ℝ)) :
  algebra_norm K L:=
{ to_fun    := spectral_norm h_alg,
  map_zero' := spectral_norm_zero h_alg,
  add_le'   := add_le_of_is_nonarchimedean (spectral_norm_nonneg h_alg)
    (spectral_norm_is_nonarchimedean h_alg hna),
  mul_le'   := spectral_norm_mul h_alg hna,
  smul'     := spectral_norm_smul h_alg hna,
  neg'      := spectral_norm_neg h_alg hna,
  eq_zero_of_map_eq_zero' := λ x hx, spectral_norm_ne_zero_of_map_ne_zero h_alg hx }

lemma spectral_alg_norm_def (hna : is_nonarchimedean (norm : K → ℝ)) (x : L) : 
  spectral_alg_norm h_alg hna x = spectral_norm h_alg x := 
rfl

lemma spectral_norm_extends (k : K) : spectral_norm h_alg (algebra_map K L k) = ‖ k ‖ :=
begin
  simp_rw [spectral_norm, minpoly.eq_X_sub_C_of_algebra_map_inj _ (algebra_map K L).injective],
  exact spectral_value_X_sub_C k,
end

lemma spectral_alg_norm_extends (k : K) (hna : is_nonarchimedean (norm : K → ℝ)) :
  spectral_alg_norm h_alg hna (algebra_map K L k) = ‖ k ‖ :=
spectral_norm_extends h_alg k

lemma spectral_norm_is_norm_le_one_class : spectral_norm h_alg 1 ≤ 1 :=
begin
  have h1 : (1 : L) = (algebra_map K L 1) := by rw map_one,
  rw [h1, spectral_norm.extends, norm_one],
end

lemma spectral_alg_norm_is_norm_le_one_class (hna : is_nonarchimedean (norm : K → ℝ)) :
  spectral_alg_norm h_alg hna 1 ≤ 1 :=
spectral_norm_is_norm_le_one_class h_alg

lemma spectral_norm_is_norm_one_class : spectral_norm h_alg 1 = 1 :=
begin
  have h1 : (1 : L) = (algebra_map K L 1) := by rw map_one,
  rw [h1, spectral_norm.extends, norm_one],
end

lemma spectral_alg_norm_is_norm_one_class (hna : is_nonarchimedean (norm : K → ℝ)) :
  spectral_alg_norm h_alg hna 1 = 1 :=
spectral_norm_is_norm_one_class h_alg

lemma spectral_alg_norm_is_pow_mul (hna : is_nonarchimedean (norm : K → ℝ)) :
  is_pow_mul (spectral_alg_norm h_alg hna) := 
spectral_norm_is_pow_mul h_alg hna

def adjoin.algebra_norm (f : algebra_norm K L) (x : L) : 
  algebra_norm K K⟮x⟯ := 
{ to_fun    := (f ∘ (algebra_map ↥K⟮x⟯ L)),
  map_zero' := by simp only [function.comp_app, map_zero],
  add_le'   := λ a b, by { simp only [function.comp_app, map_add, map_add_le_add] },
  mul_le'   := λ a b, by { simp only [function.comp_app, map_mul, map_mul_le_mul] },
  smul'     := λ r a, 
  begin
    simp only [function.comp_app, algebra.smul_def],
    rw [map_mul, ← ring_hom.comp_apply, ← is_scalar_tower.algebra_map_eq, ← algebra.smul_def, 
      map_smul_eq_mul _ _],
  end,
  neg'      := λ a, by { simp only [function.comp_app, map_neg, map_neg_eq_map] },
  eq_zero_of_map_eq_zero' := λ a ha, 
  begin 
    simp only [function.comp_app, map_eq_zero_iff_eq_zero, _root_.map_eq_zero] at ha,
    exact ha,
  end  }

end spectral_norm

section spectral_valuation

variables {K : Type*} [normed_field K] [complete_space K] {L : Type*} [hL : field L] [algebra K L]
(h_alg : algebra.is_algebraic K L)

include hL

-- Theorem 3.2.4/2

section

omit hL

def norm_to_normed_ring {A : Type*} [ring A] (f : ring_norm A):
  normed_ring A := 
{ norm          := λ x, f x,
  dist          := λ x y, f (x - y),
  dist_self     := λ x, by simp only [sub_self, map_zero],
  dist_comm     := λ x y, by simp only [← neg_sub x y, map_neg_eq_map],
  dist_triangle := λ x y z, begin
    have hxyz : x - z = x - y + (y - z) := by abel,
    simp only [hxyz, map_add_le_add],
  end,
  eq_of_dist_eq_zero := λ x y hxy, eq_of_sub_eq_zero (ring_norm.eq_zero_of_map_eq_zero' _ _ hxy),
  dist_eq := λ x y, rfl,
  norm_mul := λ x y, by simp only [map_mul_le_mul], }

end

def mul_norm_to_normed_field (f : mul_ring_norm L) :
  normed_field L := 
{ norm          := λ x, f x,
  dist          := λ x y, f (x - y),
  dist_self     := λ x, by simp only [sub_self, map_zero],
  dist_comm     := λ x y, by simp only [← neg_sub x y, map_neg_eq_map],
  dist_triangle := λ x y z, begin
    have hxyz : x - z = x - y + (y - z) := by ring, 
    simp only [hxyz, map_add_le_add],
  end,
  eq_of_dist_eq_zero :=
   λ x y hxy, eq_of_sub_eq_zero (mul_ring_norm.eq_zero_of_map_eq_zero' _ _ hxy),
  dist_eq := λ x y, rfl,
  norm_mul' := λ x y, by simp only [map_mul],} 

lemma mul_norm_to_normed_field.norm (f : mul_ring_norm L) /- (hf_neg : ∀ x, f (-x) = f x) -/:
  (mul_norm_to_normed_field f).norm = λ x, (f x : ℝ) := rfl



end spectral_valuation