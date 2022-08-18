import rank_one_valuation
import normed_space
import power_mult_seminorm
import data.list.min_max
import field_theory.fixed
import field_theory.normal
import topology.algebra.valuation
import ring_theory.polynomial.vieta
import normal_closure
import pow_mult_faithful

noncomputable theory

open_locale polynomial nnreal

variables {R : Type*} [normed_ring R]

def polynomial.coeffs (p : R[X])  : list R := list.map p.coeff (list.range p.nat_degree)

lemma list.le_max_of_exists_le {α : Type*} [linear_order α] [order_bot α] {l : list α} {a x : α}
  (hx : x ∈ l) (h : a ≤ x) : a ≤ l.foldr max ⊥ :=
begin
  induction l with y l IH,
  { exact absurd hx (list.not_mem_nil _), },
  { obtain rfl | hl := hx,
    simp only [list.foldr, list.foldr_cons],
    { exact le_max_of_le_left h, },
    { exact le_max_of_le_right (IH hl) }}
end

def spectral_value_terms {p : R[X]} (hp : p.monic) : ℕ → ℝ≥0 := 
λ (n : ℕ), if n < p.nat_degree then ∥ p.coeff n ∥₊^(1/(p.nat_degree - n : ℝ)) else 0

lemma spectral_value_terms_of_lt_nat_degree {p : R[X]} (hp : p.monic) {n : ℕ}
  (hn : n < p.nat_degree) : spectral_value_terms hp n = ∥ p.coeff n ∥₊^(1/(p.nat_degree - n : ℝ)) := 
by simp only [spectral_value_terms, if_pos hn]

lemma spectral_value_terms_of_nat_degree_le {p : R[X]} (hp : p.monic) {n : ℕ}
  (hn : p.nat_degree ≤ n) : spectral_value_terms hp n = 0 := 
by simp only [spectral_value_terms, if_neg (not_lt.mpr hn)]

def spectral_value {p : R[X]} (hp : p.monic) : nnreal := supr (spectral_value_terms hp)

lemma spectral_value_terms_bdd_above {p : R[X]} (hp : p.monic) :
  bdd_above (set.range (spectral_value_terms hp)) := 
begin
  use list.foldr max 0
  (list.map (λ n, ∥ p.coeff n ∥₊^(1/(p.nat_degree - n : ℝ))) (list.range p.nat_degree)),
  { rw mem_upper_bounds,
    intros r hr,
    obtain ⟨n, hn⟩ := set.mem_range.mpr hr,
    simp only [spectral_value_terms] at hn,
    rw ← nnreal.bot_eq_zero,
    split_ifs at hn with hd hd,
    { have h : ∥p.coeff n∥₊ ^ (1 / (p.nat_degree - n : ℝ)) ∈ list.map 
        (λ (n : ℕ), ∥p.coeff n∥₊ ^ (1 / (p.nat_degree - n : ℝ))) (list.range p.nat_degree),
      { simp only [list.mem_map, list.mem_range],
        exact ⟨n, hd, rfl⟩, },  
    exact list.le_max_of_exists_le h (ge_of_eq hn), },
    { rw ← hn, exact zero_le _, }},
end

lemma spectral_value_terms_finite_range {p : R[X]} (hp : p.monic) :
  (set.range (spectral_value_terms hp)).finite :=
begin
  have h_ss : set.range (spectral_value_terms hp) ⊆ set.range (λ (n : fin p.nat_degree), 
    ∥ p.coeff n ∥₊^(1/(p.nat_degree - n : ℝ))) ∪ {(0 : ℝ≥0)},
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

variable [nontrivial R]

lemma list.max_repeat {α : Type*} {n : ℕ} (a : α) [linear_order α] :
  list.foldr max a (list.repeat a n) = a :=
begin
  induction n with n hn,
  { simp only [list.repeat, list.foldr_nil] },
  { simp only [list.foldr, list.repeat, list.repeat_succ, list.foldr_cons, max_eq_left_iff],
    exact le_of_eq hn, }
end

lemma spectral_value_X_pow (n : ℕ) :
  spectral_value (@polynomial.monic_X_pow R _ n) = 0 := 
begin
  rw spectral_value, rw spectral_value_terms,
  simp_rw [polynomial.coeff_X_pow n, polynomial.nat_degree_X_pow],
  convert csupr_const,
  ext m,
  by_cases hmn : m < n,
  { rw [if_pos hmn, nnreal.coe_eq, nnreal.rpow_eq_zero_iff, if_neg (ne_of_lt hmn), nnnorm_zero,
      one_div, ne.def, inv_eq_zero, ← nat.cast_sub (le_of_lt hmn), nat.cast_eq_zero,
      nat.sub_eq_zero_iff_le],
    exact ⟨eq.refl _, not_le_of_lt hmn⟩, },
  { rw if_neg hmn },
  apply_instance,
end

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
          have h0 : (0 : nnreal) = 0^(1 / ((p.nat_degree : ℝ) - n)),
          { rw nnreal.zero_rpow (ne_of_gt h_exp), },
          rw [supr, cSup_le_iff (spectral_value_terms_bdd_above hp)
            (set.range_nonempty _)] at h_le,
          specialize h_le (spectral_value_terms hp n) ⟨n, rfl⟩,
          simp only [spectral_value_terms, if_pos hn'] at h_le,
          rw [h0, nnreal.rpow_le_rpow_iff h_exp] at h_le,
          exact norm_eq_zero.mp (le_antisymm h_le (norm_nonneg _)), },
        { exact polynomial.coeff_eq_zero_of_nat_degree_lt 
            (lt_of_le_of_ne (le_of_not_lt hn') (ne_comm.mpr hn)) }}}},
  { convert spectral_value_X_pow p.nat_degree,
    apply_instance }
end

lemma spectral_value_X_sub_C (r : R) :
  spectral_value (@polynomial.monic_X_sub_C _ _ r) = ∥r∥₊ := 
begin
  rw spectral_value, rw spectral_value_terms,
  simp only [polynomial.nat_degree_X_sub_C, nat.lt_one_iff, polynomial.coeff_sub,
    nat.cast_one, one_div],
  suffices : (⨆ (n : ℕ), ite (n = 0) ∥r∥₊ 0) = ∥r∥₊,
  { rw ← this,
    apply congr_arg,
    ext n,
    by_cases hn : n = 0,
    { rw [if_pos hn, if_pos hn, hn, nat.cast_zero, sub_zero, polynomial.coeff_X_zero,
        polynomial.coeff_C_zero, zero_sub, nnnorm_neg, inv_one, nnreal.rpow_one] },
    { rw [if_neg hn, if_neg hn],}},
  { apply csupr_eq_of_forall_le_of_forall_lt_exists_gt,
    { intro n,
      split_ifs,
      exact le_refl _, 
      exact zero_le _ },
    { intros x hx, use 0,
      simp only [eq_self_iff_true, if_true, hx], }}
end

/- In this section we prove Proposition 3.1.2/1 from BGR. -/
section bdd_by_spectral_value
variables {K : Type*} [normed_field K] {L : Type*} [field L] [algebra K L] {f : L → ℝ≥0}

lemma polynomial.nat_degree_pos_of_monic_of_root {p : K[X]} (hp : p.monic) {x : L}
  (hx : polynomial.aeval x p = 0) : 0 < p.nat_degree := 
polynomial.nat_degree_pos_of_aeval_root (polynomial.ne_zero_of_ne_zero_of_monic one_ne_zero hp) hx
  ((injective_iff_map_eq_zero (algebra_map K L)).mp (algebra_map K L).injective)

-- Part (1): the norm of any root of p is bounded by the spectral value of p.
lemma root_norm_le_spectral_value (hf_pm : is_pow_mult f) (hf_na : is_nonarchimedean f)
  (hf_alg_norm : is_algebra_norm (normed_ring.to_is_norm K) f) (hf1 : is_norm_le_one_class f)
  {p : K[X]} (hp : p.monic) {x : L} (hx : polynomial.aeval x p = 0) : f x ≤ spectral_value hp := 
begin
  by_cases hx0 : f x = 0,
  { rw hx0, exact zero_le _ },
  { by_contra' h_ge,
    have hn_lt : ∀ (n : ℕ) (hn : n < p.nat_degree), ∥ p.coeff n ∥₊ < (f x)^ (p.nat_degree - n),
    { intros n hn,
      have hexp : (∥p.coeff n∥₊^(1/(p.nat_degree - n : ℝ)))^(p.nat_degree - n) = ∥p.coeff n∥₊,
      { rw [← nnreal.rpow_nat_cast, ← nnreal.rpow_mul, mul_comm, nnreal.rpow_mul, 
          nnreal.rpow_nat_cast, ← nat.cast_sub (le_of_lt hn), one_div,
          nnreal.pow_nat_rpow_nat_inv _ (ne_of_gt (tsub_pos_of_lt hn))] },
      have h_base : ∥p.coeff n∥₊^(1/(p.nat_degree - n : ℝ)) < f x,
      { rw [spectral_value, supr, set.finite.cSup_lt_iff (spectral_value_terms_finite_range hp)
          (set.range_nonempty (spectral_value_terms hp))] at h_ge,
        have h_rg: ∥p.coeff n∥₊ ^ (1 / (p.nat_degree - n : ℝ)) ∈ set.range (spectral_value_terms hp),
        { use n, simp only [spectral_value_terms, if_pos hn] },
        exact h_ge (∥p.coeff n∥₊ ^ (1 / (↑(p.nat_degree) - ↑n))) h_rg },
      rw [← hexp, ← nnreal.rpow_nat_cast, ← nnreal.rpow_nat_cast],
      exact nnreal.rpow_lt_rpow h_base (nat.cast_pos.mpr (tsub_pos_of_lt hn)), },
    have h_deg : 0 < p.nat_degree := polynomial.nat_degree_pos_of_monic_of_root hp hx,
    have : ∥(1 : K)∥ = 1 := norm_one,
    have h_lt : f ((finset.range (p.nat_degree)).sum (λ (i : ℕ), p.coeff i • x ^ i)) < 
      f (x^(p.nat_degree)),
    { have hn' : ∀ (n : ℕ) (hn : n < p.nat_degree), f (p.coeff n • x ^ n) < f (x^(p.nat_degree)),
      { intros n hn,
        by_cases hn0 : n = 0,
        { rw [hn0, pow_zero, hf_alg_norm.smul, hf_pm _ (nat.succ_le_iff.mpr h_deg), 
            ← nat.sub_zero p.nat_degree, ← hn0],
          exact mul_lt_of_lt_of_le_one (hn_lt n hn) hf1 },
        { have : p.nat_degree = (p.nat_degree - n) + n,
          { rw nat.sub_add_cancel (le_of_lt hn), },
          rw [hf_alg_norm.smul, hf_pm _ (nat.succ_le_iff.mp (pos_iff_ne_zero.mpr hn0)), 
            hf_pm _ (nat.succ_le_iff.mpr h_deg), this, pow_add],
          rw mul_lt_mul_right (pow_pos (pos_iff_ne_zero.mpr hx0) _),
          exact hn_lt n hn }},
      have hf0 : f 0 = 0 := hf_alg_norm.to_is_norm.to_is_seminorm.zero,
      obtain ⟨m, hm_in, hm⟩ := is_nonarchimedean_finset_range_add_le hf0 hf_na p.nat_degree 
        (λ (i : ℕ), p.coeff i • x ^ i),
      exact lt_of_le_of_lt hm (hn' m (hm_in h_deg)) },
    have h0 : f 0 ≠ 0,
    { have h_eq : f 0 = f (x^(p.nat_degree)),
      { rw [← hx, polynomial.aeval_eq_sum_range, finset.sum_range_succ, add_comm, hp.coeff_nat_degree,
        one_smul, ← max_eq_left_of_lt h_lt],
        exact is_nonarchimedean_add_eq_max_of_ne hf_alg_norm.to_is_norm.to_is_seminorm 
        hf_na (ne_of_lt h_lt), },
      rw h_eq,
      exact ne_of_gt (lt_of_le_of_lt (zero_le _) h_lt) },
    exact h0 hf_alg_norm.to_is_norm.to_is_seminorm.zero, }
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

/- universe u
theorem mv_polynomial.prod_X_add_C_eval {R : Type u} [comm_semiring R] (σ : Type u)
 [fintype σ] (r : σ → R) :
finset.univ.prod (λ (i : σ), ⇑polynomial.C (r i) + polynomial.X) =
 (finset.range (fintype.card σ + 1)).sum (λ (i : ℕ), (finset.powerset_len i finset.univ).sum (λ (t : finset σ), t.prod (λ (i : σ), ⇑polynomial.C (r i))) * polynomial.X ^ (fintype.card σ - i))
 -/

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

lemma polynomial.prod_X_sub_C_coeff {n : ℕ} (hn : 0 < n) (b : fin n → K)
  {m : ℕ} (hm : m ≤ n) : (finprod (λ (k : fin n), polynomial.X - (polynomial.C (b k)))).coeff m =
  (finset.powerset_len (n - m) finset.univ).sum
    (λ (t : finset (fin n)), t.prod (λ (i : (fin n)), - b i)) := 
begin
  simp_rw [sub_eq_add_neg, ← polynomial.C_neg, ← pi.neg_apply],
  rw [finprod_eq_prod_of_fintype],
  --rw mv_polynomial.prod_X_add_C_coeff,
  sorry
  /- rw [finprod_eq_prod_of_fintype, mv_polynomial.prod_X_add_C_eval],
  simp_rw [fintype.card_fin, pi.neg_apply, map_neg, polynomial.finset_sum_coeff],
  have h_coeff : ∀ (k : ℕ), ((finset.powerset_len k finset.univ).sum (λ (x : finset (fin n)), 
    x.prod (λ (x : fin n), - polynomial.C (b x))) * polynomial.X ^ (n - k)).coeff m = 
    if k = n - m then (finset.powerset_len (n - m) finset.univ).sum
    (λ (t : finset (fin n)), t.prod (λ (i : (fin n)), - b i)) else 0,
  { intro k,
    simp_rw [← polynomial.C_neg, polynomial.C_finset_prod, polynomial.C_finset_add],
    rw polynomial.coeff_C_mul_X_pow,
    split_ifs with h1 h2 h3,
    { rw h2 },
    { by_cases hk : k ≤ n,
      { rw [h1, tsub_tsub_cancel_of_le hk, ne_self_iff_false] at h2, contradiction },
      { rw not_le at hk,
        have hempt : finset.powerset_len k (finset.univ : finset (fin n)) = ∅,
        { apply finset.powerset_len_empty,
          rw [finset.card_fin],
          exact hk, },
        rw [hempt, finset.sum_empty], }},
    { rw [h3, tsub_tsub_cancel_of_le hm, ne_self_iff_false] at h1, contradiction },
    { refl }},
  simp_rw h_coeff,
  rw [finset.sum_ite_eq', if_pos],
  rw finset.mem_range,
  linarith, -/
end

lemma prod_X_add_C_nat_degree {n : ℕ} (b : fin n → L) :
  (finset.univ.prod (λ (i : fin n), polynomial.X - polynomial.C (b i))).nat_degree = n :=
begin
  rw polynomial.nat_degree_prod _ _ (λ m hm, polynomial.X_sub_C_ne_zero (b m)),
  simp only [polynomial.nat_degree_X_sub_C, finset.sum_const, finset.card_fin,
    algebra.id.smul_eq_mul, mul_one],
end

lemma foo (hf_pm : is_pow_mult f) (hf_na : is_nonarchimedean f)
  (hf_alg_norm : is_algebra_norm (normed_ring.to_is_norm K) f) {n : ℕ} (hn : 0 < n) (b : fin n → L)
  {m : ℕ} (hm : m < n) :
∃ (s : (finset.powerset_len (fintype.card (fin n) - m) (@finset.univ (fin n) _))),
 f ((finset.powerset_len (fintype.card (fin n) - m) finset.univ).sum 
  (λ (t : finset (fin n)), t.prod (λ (i : fin n), -b i))) ≤  f (s.val.prod (λ (i : fin n), -b i)) := 
begin
  sorry
end

/-- Part (2): if p splits into linear factors over B, then its spectral value equals the maximum
  of the norms of its roots. -/
lemma max_root_norm_eq_spectral_value (hf_pm : is_pow_mult f) (hf_na : is_nonarchimedean f)
  (hf_alg_norm : is_algebra_norm (normed_ring.to_is_norm K) f) (hf1 : is_norm_one_class f)
  (p : K[X]) {n : ℕ} (hn : 0 < n) (b : fin n → L)
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
      rw [polynomial.map_alg_eq_map, polynomial.aeval_map] at hm',
      exact hm', },
    rw function.comp_apply,
    exact root_norm_le_spectral_value hf_pm hf_na hf_alg_norm (le_of_eq hf1) _ hm, },
  { apply csupr_le,
    intros m,
    by_cases hm : m < p.nat_degree,
    { rw spectral_value_terms_of_lt_nat_degree _ hm,
      have h : 0 < (p.nat_degree - m : ℝ),
      { rw [sub_pos, nat.cast_lt], exact hm },
      rw [← nnreal.rpow_le_rpow_iff h, ← nnreal.rpow_mul, one_div_mul_cancel (ne_of_gt h),
        nnreal.rpow_one, ← nat.cast_sub (le_of_lt hm), nnreal.rpow_nat_cast],
      have hpn : n = p.nat_degree,
      { rw [← polynomial.nat_degree_map (algebra_map K L), ← polynomial.map_alg_eq_map, hp,
          finprod_eq_prod_of_fintype, prod_X_add_C_nat_degree] },
      have hc : ∥p.coeff m∥₊ = f (((polynomial.map_alg K L) p).coeff m),
      { have : ∥p.coeff m∥₊ = (λ (r : K), ∥r∥₊) (p.coeff m) := rfl,
        rw [this, ← is_algebra_norm_extends (normed_ring.to_is_norm K) hf_alg_norm hf1,
          polynomial.map_alg_eq_map, polynomial.coeff_map] },
        have hm_le : m ≤ fintype.card (fin n),
        { rw [fintype.card_fin, hpn],
          exact le_of_lt hm, },
      rw [hc, hp, finprod_eq_prod_of_fintype],
      simp_rw sub_eq_add_neg,
      simp_rw ← polynomial.C_neg,
      sorry,},
      sorry },
      /- rw mv_polynomial.prod_X_add_C_coeff _ _ _ hm_le,
      have : m < n,
      { rw hpn, exact hm },
      obtain ⟨s, hs⟩ := foo hf_pm hf_na hf_alg_norm hn b this,
      apply le_trans hs,
      have  h_pr: f (s.val.prod (λ (i : fin n), -b i)) ≤ s.val.prod (λ (i : fin n), f(-b i)),
      { exact finset.le_prod_of_submultiplicative _ hf1 hf_alg_norm.mul _ _,},
      apply le_trans h_pr,
      have : s.val.prod (λ (i : fin n), f (-b i)) ≤ s.val.prod (λ (i : fin n), supr (f ∘ b)),
      { apply finset.prod_le_prod,
        { intros i hi, exact zero_le _, },
        { intros i hi, 
          rw hf_na.neg hf_alg_norm.zero _, 
          exact le_csupr (set.finite.bdd_above (set.range (f ∘ b)).to_finite) _, }},
      apply le_trans this,
      apply le_of_eq,
      simp only [subtype.val_eq_coe, finset.prod_const],
      suffices h_card : (s : finset (fin n)).card = p.nat_degree - m,
      { rw h_card },
      have hs' := s.property,
      simp only [subtype.val_eq_coe, fintype.card_fin, finset.mem_powerset_len] at hs',
      rw [hs'.right, hpn], },
    { rw spectral_value_terms_of_nat_degree_le _ (le_of_not_lt hm),
      exact zero_le _, }} -/
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

section minpoly

variables {K : Type*} [normed_field K] {L : Type*} [field L] [algebra K L]
(h_alg : algebra.is_algebraic K L)

def adjoin_root.id_alg_equiv {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) (h_eq : p = q) :
  adjoin_root p ≃ₐ[K] adjoin_root q :=
alg_equiv.of_alg_hom (adjoin_root.lift_hom p (adjoin_root.root q) (by 
  rw [h_eq, adjoin_root.aeval_eq, adjoin_root.mk_self])) 
  (adjoin_root.lift_hom q (adjoin_root.root p) (by
  rw [h_eq, adjoin_root.aeval_eq, adjoin_root.mk_self]))
  (power_basis.alg_hom_ext (adjoin_root.power_basis hq) (by
    rw [adjoin_root.power_basis_gen hq, alg_hom.coe_comp, function.comp_app, 
      adjoin_root.lift_hom_root, adjoin_root.lift_hom_root, alg_hom.coe_id, id.def]))
  (power_basis.alg_hom_ext (adjoin_root.power_basis hp) (by
    rw [adjoin_root.power_basis_gen hp, alg_hom.coe_comp, function.comp_app,
      adjoin_root.lift_hom_root, adjoin_root.lift_hom_root, alg_hom.coe_id, id.def]))

lemma adjoin_root.id_alg_equiv_apply_root {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) (h_eq : p = q) :
  adjoin_root.id_alg_equiv hp hq h_eq (adjoin_root.root p) = adjoin_root.root q :=
by rw [adjoin_root.id_alg_equiv, alg_equiv.of_alg_hom, alg_equiv.coe_mk, adjoin_root.lift_hom_root]

@[simp] lemma minpoly.aeval_conj (h_alg : algebra.is_algebraic K L) (σ : L ≃ₐ[K] L) (x : L) :
  (polynomial.aeval (σ x)) (minpoly K x) = 0 :=
by rw [polynomial.aeval_alg_equiv, alg_hom.coe_comp, function.comp_app, minpoly.aeval, map_zero]

@[simp] lemma minpoly.eq_of_conj (h_alg : algebra.is_algebraic K L) (σ : L ≃ₐ[K] L) (x : L) :
  minpoly K (σ x) = minpoly K x := 
begin
  have h_dvd : minpoly K x ∣ minpoly K (σ x),
  { apply minpoly.dvd,
    have hx : σ.symm (σ x) = x := σ.left_inv x,
    nth_rewrite 0 ← hx,
    rw [polynomial.aeval_alg_equiv, alg_hom.coe_comp, function.comp_app, minpoly.aeval, map_zero] },
  have h_deg : (minpoly K (σ x)).nat_degree ≤ (minpoly K x).nat_degree,
  { apply polynomial.nat_degree_le_nat_degree (minpoly.degree_le_of_ne_zero K _ (minpoly.ne_zero 
    (is_algebraic_iff_is_integral.mp (h_alg _))) (minpoly.aeval_conj h_alg σ x)) },
  exact polynomial.eq_of_monic_of_dvd_of_nat_degree_le
    (minpoly.monic (is_algebraic_iff_is_integral.mp (h_alg _)))
    (minpoly.monic (is_algebraic_iff_is_integral.mp (h_alg _))) h_dvd h_deg,
end

def minpoly.alg_equiv {x y : L} (h_mp : minpoly K x = minpoly K y) : K⟮x⟯ ≃ₐ[K] K⟮y⟯ := 
alg_equiv.comp ((intermediate_field.adjoin_root_equiv_adjoin K 
  (is_algebraic_iff_is_integral.mp (h_alg _))).symm)
  (alg_equiv.comp (adjoin_root.id_alg_equiv
    (minpoly.ne_zero (is_algebraic_iff_is_integral.mp (h_alg _))) 
    (minpoly.ne_zero (is_algebraic_iff_is_integral.mp (h_alg _))) h_mp)
    (intermediate_field.adjoin_root_equiv_adjoin K(is_algebraic_iff_is_integral.mp (h_alg _))))

lemma minpoly.alg_equiv_apply {x y : L} (h_mp : minpoly K x = minpoly K y) :
  minpoly.alg_equiv h_alg h_mp ((intermediate_field.adjoin_simple.gen K x)) =
    (intermediate_field.adjoin_simple.gen K y) := 
begin
  simp only [minpoly.alg_equiv],
  rw [alg_equiv.comp_apply, ← intermediate_field.adjoin_root_equiv_adjoin_apply_root K 
    (is_algebraic_iff_is_integral.mp (h_alg _)), alg_equiv.symm_apply_apply,
    alg_equiv.comp_apply, adjoin_root.id_alg_equiv_apply_root,
    intermediate_field.adjoin_root_equiv_adjoin_apply_root K 
    (is_algebraic_iff_is_integral.mp (h_alg _))],
end

lemma minpoly.eq_of_root (h_alg : algebra.is_algebraic K L) {x y : L}
 (h_ev : (polynomial.aeval y) (minpoly K x) = 0) : minpoly K y = minpoly K x  := 
polynomial.eq_of_monic_of_associated
   (minpoly.monic (is_algebraic_iff_is_integral.mp (h_alg _)))
   (minpoly.monic (is_algebraic_iff_is_integral.mp (h_alg _)))
   (irreducible.associated_of_dvd
    (minpoly.irreducible (is_algebraic_iff_is_integral.mp (h_alg _)))
    (minpoly.irreducible (is_algebraic_iff_is_integral.mp (h_alg _)))
    (minpoly.dvd K y h_ev))

lemma minpoly.conj_of_root (h_alg : algebra.is_algebraic K L) (hn : normal K L) {x y : L}
 (h_ev : (polynomial.aeval x) (minpoly K y) = 0) : ∃ (σ : L ≃ₐ[K] L), σ x = y  := 
begin
  set f : K⟮x⟯ ≃ₐ[K] K⟮y⟯ := minpoly.alg_equiv h_alg (minpoly.eq_of_root h_alg h_ev),
  set h : L ≃ₐ[K] L := alg_equiv.lift_normal f L,
  use alg_equiv.lift_normal f L,
  simp_rw ← intermediate_field.adjoin_simple.algebra_map_gen K x,
  rw [alg_equiv.lift_normal_commutes f L, minpoly.alg_equiv_apply,
    intermediate_field.adjoin_simple.algebra_map_gen K y],
end

end minpoly

/- In this section we prove Theorem 3.2.1/2 from BGR. -/

section spectral_norm

variables {K : Type*} [normed_field K] {L : Type*} [field L] [algebra K L]
(h_alg : algebra.is_algebraic K L)

-- The spectral norm |y|_sp is the spectral value of the minimal polynomial of y over K.
def spectral_norm (y : L) : nnreal :=
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
  rw [subalgebra.aeval_coe, add_submonoid_class.coe_eq_zero] at hp,
  exact ⟨p, hp0, hp⟩,
end

lemma spectral_value.eq_normal (h_alg_L : algebra.is_algebraic K L) 
  (E : intermediate_field K L) (x : E) :
  spectral_norm (normal_closure.is_algebraic K E (intermediate_field.is_algebraic h_alg_L E))
    (algebra_map E (normal_closure K E) x) = spectral_norm h_alg_L (algebra_map E L x) := sorry

variable (y : L)

lemma spectral_norm.zero : spectral_norm h_alg (0 : L) = 0 := 
begin
  have h_lr: list.range 1 = [0] := rfl,
  rw [spectral_norm, spectral_value, spectral_value_terms, minpoly.zero, polynomial.nat_degree_X],
  convert csupr_const,
  ext m,
  by_cases hm : m < 1,
  { rw [if_pos hm, nnreal.coe_eq, nat.lt_one_iff.mp hm, nat.cast_one, nat.cast_zero, sub_zero,
      div_one, nnreal.rpow_one, polynomial.coeff_X_zero, nnnorm_zero] },
  { rw if_neg hm },
  apply_instance,
end

lemma spectral_norm.zero_lt {y : L} (hy : y ≠ 0) : 0 < spectral_norm h_alg y := 
begin
  rw lt_iff_le_and_ne,
  refine ⟨zero_le _, _⟩,
  rw [spectral_norm, ne.def, eq_comm, spectral_value_eq_zero_iff],
  have h0 : polynomial.coeff (minpoly K y) 0 ≠ 0  :=
  minpoly.coeff_zero_ne_zero (is_algebraic_iff_is_integral.mp (h_alg y)) hy,
  intro h,
  have h0' : (minpoly K y).coeff 0 = 0,
  { rw [h, polynomial.coeff_X_pow,
      if_neg (ne_of_lt ( minpoly.nat_degree_pos (is_algebraic_iff_is_integral.mp (h_alg y))))] },
  exact h0 h0',
end

lemma spectral_norm.ge_norm {f : L → nnreal} (hf_pm : is_pow_mult f)
  (hf_na : is_nonarchimedean f) (hf_alg_norm : is_algebra_norm (normed_ring.to_is_norm K) f)
  (hf1 : is_norm_le_one_class f) (x : L) : f x ≤ spectral_norm h_alg x :=
begin
  apply root_norm_le_spectral_value hf_pm hf_na hf_alg_norm hf1,
  rw [minpoly.aeval],
end

lemma spectral_norm.aut_isom (σ : L ≃ₐ[K] L) (x : L) : 
  spectral_norm h_alg x = spectral_norm h_alg (σ x) :=
by simp only [spectral_norm, minpoly.eq_of_conj h_alg]

-- We first assume that the extension is finite and normal
section finite

variable (h_fin : finite_dimensional K L)

def seminorm_of_auto (σ : L ≃ₐ[K] L) (hna : is_nonarchimedean (nnnorm : K → ℝ≥0)) : L → ℝ≥0 :=
λ x, classical.some (finite_extension_pow_mul_seminorm h_fin hna) (σ x)

lemma seminorm_of_auto.is_pow_mult (σ : L ≃ₐ[K] L) (hna : is_nonarchimedean (nnnorm : K → ℝ≥0)) :
  is_pow_mult (seminorm_of_auto h_fin σ hna) :=
begin
  intros x n hn,
  simp only [seminorm_of_auto, map_pow σ x n],
  exact (classical.some_spec (finite_extension_pow_mul_seminorm h_fin hna)).2.1 _ hn,
end

lemma seminorm_of_auto.is_algebra_norm (σ : L ≃ₐ[K] L) (hna : is_nonarchimedean (nnnorm : K → ℝ≥0)) :
  is_algebra_norm (normed_ring.to_is_norm K) (seminorm_of_auto h_fin σ hna) :=
{ zero    := begin
    simp only [seminorm_of_auto, map_zero σ],
    exact (classical.some_spec (finite_extension_pow_mul_seminorm h_fin hna)).1.zero,
  end,
  add     := begin
    simp only [seminorm_of_auto, map_add σ],
    intros x y,
    exact (classical.some_spec (finite_extension_pow_mul_seminorm h_fin hna)).1.add _ _,
  end,
  mul     := begin
    simp only [seminorm_of_auto, map_mul σ],
    intros x y,
    exact (classical.some_spec (finite_extension_pow_mul_seminorm h_fin hna)).1.mul _ _,
  end,
  ne_zero := λ a ha, begin
    apply (classical.some_spec (finite_extension_pow_mul_seminorm h_fin hna)).1.ne_zero _
      ((add_equiv_class.map_ne_zero_iff σ).mpr ha),
  end,
  smul    := begin
    simp only [seminorm_of_auto, map_smul σ],
    intros r x,
    exact (classical.some_spec (finite_extension_pow_mul_seminorm h_fin hna)).1.smul _ _,
  end }

lemma seminorm_of_auto.extends (σ : L ≃ₐ[K] L) (hna : is_nonarchimedean (nnnorm : K → ℝ≥0)) :
  function_extends (λ x : K, ∥x∥₊) (seminorm_of_auto h_fin σ hna) :=
begin
  intro r, simp only [seminorm_of_auto,  alg_equiv.commutes],
  exact (classical.some_spec (finite_extension_pow_mul_seminorm h_fin hna)).2.2 _,
end

def seminorm_of_galois (hna : is_nonarchimedean (nnnorm : K → ℝ≥0)) : L → ℝ≥0 :=
λ x, (supr (λ (σ : L ≃ₐ[K] L), seminorm_of_auto h_fin σ hna x))

lemma csupr_univ {α : Type u_1} {β : Type u_2} [fintype β] [conditionally_complete_lattice α]
  {f : β → α} :
(⨆ (x : β) (H : x ∈ (finset.univ : finset β)), f x) = ⨆ (x : β), f x := by simp

theorem finset.sup_eq_csupr {α : Type u_1} [nonempty α] (s : finset α) [nonempty s]
  (f : α → ℝ≥0) : s.sup f = ⨆ (a : α) (H : a ∈ s), f a :=
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
    { apply nnreal.csupr_mul_csupr_le,
      intros i j,
      by_cases hij : f i < f j,
      { have hj : f i * f j ^ n ≤ f j ^ n.succ,
        { rw pow_succ, apply mul_le_mul' (le_of_lt hij) (le_refl _) },
        exact le_trans hj (le_csupr_of_le (set.finite.bdd_above (set.finite_range _)) j 
          (le_refl _)), },
      { have hi : f i * f j ^ n ≤ f i ^ n.succ,
        { rw pow_succ, exact mul_le_mul' (le_refl _) (pow_le_pow_of_le (not_lt.mp hij)) },
        exact le_trans hi (le_csupr_of_le (set.finite.bdd_above (set.finite_range _)) i
          (le_refl _)), }},
    { haveI : nonempty (finset.univ : finset ι),
     { exact finset.nonempty_coe_sort.mpr finset.univ_nonempty },
       simp only [← csupr_univ, ← finset.sup_eq_csupr, pow_succ],
      apply finset.sup_mul_le_mul_sup_of_nonneg;
      rintros i -; exact zero_le _ }},
end

lemma seminorm_of_galois.is_pow_mult (hna : is_nonarchimedean (nnnorm : K → ℝ≥0)) :
  is_pow_mult (seminorm_of_galois h_fin hna) :=
begin
  intros x n hn,
  simp only [seminorm_of_galois],
  rw nnreal.supr_pow,
  exact supr_congr (λ σ, seminorm_of_auto.is_pow_mult h_fin σ hna _ hn),
end

lemma lt_csupr_of_lt {α : Type*} {ι : Sort*} [conditionally_complete_lattice α] {a : α} {f : ι → α}
  (H : bdd_above (set.range f)) (c : ι) (h : a < f c) : a < supr f :=
lt_of_lt_of_le h (le_csupr H c)

lemma seminorm_of_galois.is_algebra_norm (hna : is_nonarchimedean (nnnorm : K → ℝ≥0)) :
  is_algebra_norm (normed_ring.to_is_norm K) (seminorm_of_galois h_fin hna) := 
{ zero    := by simp only [seminorm_of_galois, (seminorm_of_auto.is_algebra_norm h_fin _ hna).zero,
    csupr_const],
  add     := λ x y, csupr_le (λ σ, le_trans ((seminorm_of_auto.is_algebra_norm h_fin σ hna).add x y)
     (add_le_add (le_csupr_of_le (set.finite.bdd_above (set.finite_range _)) σ (le_refl _)) 
       (le_csupr_of_le (set.finite.bdd_above (set.finite_range _)) σ (le_refl _)))),
  mul     := λ x y, csupr_le (λ σ, le_trans ((seminorm_of_auto.is_algebra_norm h_fin σ hna).mul x y)
   ( mul_le_mul'  (le_csupr_of_le (set.finite.bdd_above (set.finite_range _)) σ (le_refl _))
  (le_csupr_of_le (set.finite.bdd_above (set.finite_range _)) σ (le_refl _)))),
  ne_zero := λ x hx, lt_csupr_of_lt (set.finite.bdd_above 
    (set.range (λ (σ : L ≃ₐ[K] L), seminorm_of_auto h_fin σ hna x)).to_finite) (alg_equiv.refl) 
    ((seminorm_of_auto.is_algebra_norm h_fin _ hna).ne_zero _ hx),
  smul    := λ r x, by simp only [seminorm_of_galois, 
    (seminorm_of_auto.is_algebra_norm h_fin _ hna).smul, nnreal.mul_csupr (set.finite.bdd_above 
      (set.finite_range (λ (i : L ≃ₐ[K] L), seminorm_of_auto h_fin i hna x)))] }

lemma seminorm_of_galois.extends (hna : is_nonarchimedean (nnnorm : K → ℝ≥0)) :
  function_extends (λ x : K, ∥x∥₊) (seminorm_of_galois h_fin hna) := 
λ r, by simp only [seminorm_of_galois, seminorm_of_auto.extends h_fin _ hna r, csupr_const]

section normal

lemma spectral_norm.is_pow_mult_of_fd_normal (h_fin : finite_dimensional K L) (hn : normal K L) 
  (hna : is_nonarchimedean (nnnorm : K → ℝ≥0)) : is_pow_mult (spectral_norm h_alg) :=
begin
  obtain ⟨f, hf_norm, hf_pm, hf_ext⟩ := finite_extension_pow_mul_seminorm h_fin hna,
  

  sorry
end

lemma spectral_norm.is_algebra_norm_of_fd :
  is_algebra_norm (normed_ring.to_is_norm K) (spectral_norm h_alg) :=
begin
  sorry
end

lemma spectral_norm.is_nonarchimedean_of_fd_normal
  (h : is_nonarchimedean (λ k : K, ⟨∥k∥, norm_nonneg _⟩)) (hn : normal K L) :
  is_nonarchimedean (spectral_norm h_alg) :=
begin
  sorry
end

lemma spectral_norm.extends_norm_of_fd : function_extends (λ x : K, ∥x∥₊) (spectral_norm h_alg) :=
begin
  sorry
end

lemma spectral_norm.max_of_fd_normal (hn: normal K L) {f : L → nnreal} (hf_pow : is_pow_mult f)
  (hf_alg_norm : is_algebra_norm (normed_ring.to_is_norm K) f) 
  (hf_ext : function_extends (λ x : K, ∥x∥₊) f) (x : L) :
  spectral_norm h_alg x = supr (λ (σ : L ≃ₐ[K] L), f (σ x)) :=
begin
  sorry
end

lemma spectral_norm.unique_of_fd_normal (hn : normal K L) {f : L → nnreal} (hf_pow : is_pow_mult f)
  (hf_alg_norm : is_algebra_norm (normed_ring.to_is_norm K) f) 
  (hf_ext : function_extends (λ x : K, ∥x∥₊) f)
  (hf_iso : ∀ (σ : L ≃ₐ[K] L) (x : L), f x = f (σ x))
  (x : L) : f x = spectral_norm h_alg x :=
begin
  have h_sup : supr (λ (σ : L ≃ₐ[K] L), f (σ x)) = f x,
  { rw ← @csupr_const _ (L ≃ₐ[K] L) _ _ (f x),
    exact supr_congr (λ σ, by rw hf_iso σ x), },
  rw [spectral_norm.max_of_fd_normal h_alg hn hf_pow hf_alg_norm hf_ext, h_sup]
end

end normal

end finite

-- Now we let L/K be any algebraic extension

-- The spectral norm is a power-multiplicative K-algebra norm on L extending the norm on K.

lemma spectral_value.eq_normal' (h_alg_L : algebra.is_algebraic K L) 
  {E : intermediate_field K L} {x : L} (g : E) (h_map : algebra_map E L g = x) :
  spectral_norm (normal_closure.is_algebraic K E (intermediate_field.is_algebraic h_alg_L E))
    (algebra_map E (normal_closure K E) g) = spectral_norm h_alg_L x :=
begin
  rw ← h_map,
  exact spectral_value.eq_normal h_alg_L E g,
end

lemma spectral_norm.is_pow_mult (hna : is_nonarchimedean (nnnorm : K → ℝ≥0)) :
  is_pow_mult (spectral_norm h_alg) :=
begin
  intros x n hn,
  set E := K⟮x⟯ with hE,
  haveI h_fd_E : finite_dimensional K E := 
  intermediate_field.adjoin.finite_dimensional (is_algebraic_iff_is_integral.mp (h_alg x)),
  have h_alg_E : algebra.is_algebraic K E := intermediate_field.is_algebraic h_alg E,
  set g := intermediate_field.adjoin_simple.gen K x with hg,
  have h_map : algebra_map E L g^n = x^n := rfl,
  rw [← spectral_value.eq_normal' h_alg  _ (intermediate_field.adjoin_simple.algebra_map_gen K x),
    ← spectral_value.eq_normal' h_alg (g^n) h_map, map_pow],
  exact spectral_norm.is_pow_mult_of_fd_normal (normal_closure.is_algebraic K E h_alg_E)
    (normal_closure.is_finite_dimensional K E) (normal_closure.is_normal K E h_alg_E) hna _ hn,
end

lemma spectral_norm.smul (k : K) (y : L) :
  spectral_norm h_alg (k • y) = ∥ k ∥₊ * spectral_norm h_alg y :=
begin
  set E := K⟮y⟯ with hE,
  haveI h_fd_E : finite_dimensional K E := 
  intermediate_field.adjoin.finite_dimensional (is_algebraic_iff_is_integral.mp (h_alg y)),
  have h_alg_E : algebra.is_algebraic K E := intermediate_field.is_algebraic h_alg E,
  set g := intermediate_field.adjoin_simple.gen K y with hg,
  have hgy : k • y = (algebra_map ↥K⟮y⟯ L) (k • g) := rfl,
  have h : algebra_map K⟮y⟯ (normal_closure K K⟮y⟯) (k • g) = 
    k • algebra_map K⟮y⟯ (normal_closure K K⟮y⟯) g,
  { rw [algebra.algebra_map_eq_smul_one, algebra.algebra_map_eq_smul_one, smul_assoc] },
    rw [← spectral_value.eq_normal' h_alg g (intermediate_field.adjoin_simple.algebra_map_gen K y),
      hgy, ← spectral_value.eq_normal' h_alg (k • g) rfl, h],
  exact (spectral_norm.is_algebra_norm_of_fd (normal_closure.is_algebraic K E h_alg_E)).smul _ _,
end

lemma intermediate_field.adjoin_adjoin.finite_dimensional {x y : L} (hx : is_integral K x)
  (hy : is_integral K y) : finite_dimensional K K⟮x, y⟯ := 
begin
  haveI hx_fd : finite_dimensional K K⟮x⟯ := intermediate_field.adjoin.finite_dimensional hx,
  have hy' : is_integral K⟮x⟯ y := is_integral_of_is_scalar_tower  y hy,
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


lemma spectral_norm.mul (x y : L) :
  spectral_norm h_alg (x * y) ≤ spectral_norm h_alg x * spectral_norm h_alg y :=
begin
  set E := K⟮x, y⟯ with hE,
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
    K x y), map_mul],
  exact (spectral_norm.is_algebra_norm_of_fd (normal_closure.is_algebraic K E h_alg_E)).mul _ _,
end

lemma spectral_norm.is_nonarchimedean (h : is_nonarchimedean (λ k : K, ∥k∥₊)) :
  is_nonarchimedean (spectral_norm h_alg) :=
begin
  intros x y,
  set E := K⟮x, y⟯ with hE,
  haveI h_fd_E : finite_dimensional K E :=
  intermediate_field.adjoin_adjoin.finite_dimensional (is_algebraic_iff_is_integral.mp (h_alg x))
    (is_algebraic_iff_is_integral.mp (h_alg y)),
  have h_alg_E : algebra.is_algebraic K E := intermediate_field.is_algebraic h_alg E,
  set gx := intermediate_field.adjoin_adjoin.gen_1 K x y with hgx,
  set gy := intermediate_field.adjoin_adjoin.gen_2 K x y with hgy,
  have hxy : x - y = (algebra_map K⟮x, y⟯ L) (gx - gy) := rfl,
  rw [hxy, ← spectral_value.eq_normal' h_alg (gx - gy) hxy,
    ← spectral_value.eq_normal' h_alg gx (intermediate_field.adjoin_adjoin.algebra_map_gen_1
    K x y), ← spectral_value.eq_normal' h_alg gy (intermediate_field.adjoin_adjoin.algebra_map_gen_2
    K x y), map_sub],
  exact spectral_norm.is_nonarchimedean_of_fd_normal (normal_closure.is_algebraic K E h_alg_E) h
    (normal_closure.is_normal K E h_alg_E) _ _,
end

lemma spectral_norm.is_algebra_norm (hna : is_nonarchimedean (λ k : K, ∥k∥₊)) :
  is_algebra_norm (normed_ring.to_is_norm K) (spectral_norm h_alg) :=
{ zero    := spectral_norm.zero h_alg,
  add     := add_le_of_is_nonarchimedean (spectral_norm.zero h_alg)
    (spectral_norm.is_nonarchimedean h_alg hna),
  mul     := spectral_norm.mul h_alg,
  ne_zero := λ x hx, spectral_norm.zero_lt h_alg hx,
  smul    := spectral_norm.smul h_alg }

lemma spectral_norm.neg (h : is_nonarchimedean (λ k : K, ∥k∥₊)) (y : L)  :
  spectral_norm h_alg (-y) = spectral_norm h_alg y :=
is_nonarchimedean.neg (spectral_norm.is_nonarchimedean h_alg h) (spectral_norm.zero h_alg) _

lemma spectral_norm.extends (k : K) : spectral_norm h_alg (algebra_map K L k) = ∥ k ∥₊ :=
begin
  simp_rw [spectral_norm, minpoly.eq_X_sub_C_of_algebra_map_inj _ (algebra_map K L).injective],
  exact spectral_value_X_sub_C k,
end

lemma spectral_norm.is_norm_le_one_class : is_norm_le_one_class (spectral_norm h_alg) :=
begin
  rw is_norm_le_one_class,
  have h1 : (1 : L) = (algebra_map K L 1) := by rw map_one,
  rw [h1, spectral_norm.extends, nnnorm_one],
end

lemma adjoin.algebra_norm {f : L → nnreal} (hf_alg_norm : is_algebra_norm
  (normed_ring.to_is_norm K) f) (x : L) : 
  is_algebra_norm (normed_ring.to_is_norm K) (f ∘ (algebra_map ↥K⟮x⟯ L)) := 
{ zero    := by rw [function.comp_app, map_zero, hf_alg_norm.zero],
  add     := λ a b, by {rw [function.comp_app, map_add], exact hf_alg_norm.add _ _ },
  mul     := λ a b, by {rw [function.comp_app, map_mul], exact hf_alg_norm.mul _ _ },
  ne_zero := λ a ha, by { rw [function.comp_app],
    exact hf_alg_norm.ne_zero _ ((ring_hom.map_ne_zero _).mpr ha) },
  smul    := λ r a, by { rw [function.comp_app, function.comp_app], exact hf_alg_norm.smul _ _ }}

end spectral_norm

section spectral_valuation

variables {K : Type*} [normed_field K] [complete_space K] {L : Type*} [hL : field L] [algebra K L]
(h_alg : algebra.is_algebraic K L)

include hL
/- variables {K : Type*} [hK : field K] {Γ₀ : Type*} [linear_ordered_comm_group_with_zero Γ₀]
[val : valued K Γ₀] [hv : is_rank_one val.v] [complete_space K] {L : Type*} [field L] [algebra K L]
(h_alg : algebra.is_algebraic K L) 

include hK


--@[priority 10]
instance valued_field.to_normed_field : normed_field K := 
{ norm               := sorry,
  dist               := sorry,
  dist_self          := sorry,
  dist_comm          := sorry,
  dist_triangle      := sorry,
  eq_of_dist_eq_zero := sorry,
  dist_eq            := sorry,
  norm_mul'          := sorry,
  ..hK }

instance spectral_valued : valued L (multiplicative (order_dual (with_top  ℝ))) := sorry -/

-- Theorem 3.2.4/2

--TODO : remove hna
def norm.to_normed_field {A : Type*} [hA : field A]  {f : A → nnreal} (hf : is_mul_norm f) 
  (hna : is_nonarchimedean f):
  normed_field A := 
{ norm         := λ x, (f x : ℝ),
  dist          := λ x y, f (x - y),
  dist_self     := λ x, by simp only [sub_self, hf.zero, nnreal.coe_zero],
  dist_comm     := λ x y, by simp only [nnreal.coe_eq, ← neg_sub x y, hna.neg hf.zero],
  dist_triangle := λ x y z, begin
    have hxyz : x - z = x - y + (y - z) := by ring, 
    rw [← nnreal.coe_add, nnreal.coe_le_coe, hxyz],
    exact hf.add _ _,
  end,
  eq_of_dist_eq_zero := λ x y hxy,
    eq_of_sub_eq_zero (hf.to_is_norm.zero_of_norm_zero ((nnreal.coe_eq_zero _).mp hxy)),
  dist_eq := λ x y, rfl,
  norm_mul' := λ x y, by simp only [norm, ← nnreal.coe_mul, nnreal.coe_eq, hf.mul_eq], 
  ..hA }

lemma spectral_norm.unique' {f : L → nnreal} (hf_pow : is_pow_mult f)
  (hf_alg_norm : is_algebra_norm (normed_ring.to_is_norm K) f) 
  (hna : is_nonarchimedean (λ k : K, ∥k∥₊)) :
  f = spectral_norm h_alg  := 
begin
  apply eq_of_pow_mult_faithful (normed_field.to_is_mul_norm K) hf_pow hf_alg_norm 
    (spectral_norm.is_pow_mult h_alg hna) (spectral_norm.is_algebra_norm h_alg hna),
  intro x,
  set E : Type* := id K⟮x⟯ with hEdef,
  letI hE : field E := (by rw [hEdef, id.def] ; apply_instance),
  letI : algebra K E := K⟮x⟯.algebra,

  let id1 : K⟮x⟯ →ₗ[K] E := 
  { to_fun := λ y, y,
    map_add' := sorry,
    map_smul' := sorry },

  let id2 : E →ₗ[K] K⟮x⟯ := 
  { to_fun := λ y, y,
    map_add' := sorry,
    map_smul' := sorry },

  letI n1 : normed_field K⟮x⟯ := 
  { norm             := λ y, (f((algebra_map K⟮x⟯ L) y) : ℝ),
    dist               := sorry,
    dist_self          := sorry,
    dist_comm          := sorry,
    dist_triangle      := sorry,
    eq_of_dist_eq_zero := sorry,
    dist_eq            := sorry,
    norm_mul'          := sorry,
    ..intermediate_field.to_field K⟮x⟯ },

  letI n2 : normed_field E := 
  { norm             := λ y, (spectral_norm h_alg (id2 y : L) : ℝ),
    dist               := sorry,
    dist_self          := sorry,
    dist_comm          := sorry,
    dist_triangle      := sorry,
    eq_of_dist_eq_zero := sorry,
    dist_eq            := sorry,
    norm_mul'          := sorry,
    ..hE }, 

  --need to import analysis.normed_space.operator_norm
  have hid1_cont : continuous id1 := sorry, --linear_map.continuous_of_finite_dimensional id1,
  have hid2_cont : continuous id2 := sorry,
  
  --have := (@normed_field.to_has_norm _ n1).norm,

  have hC1 : ∃ (C1 : ℝ), 0 < C1 ∧ ∀ (y : K⟮x⟯), ∥id1 y∥ ≤ C1 * ∥y∥ := sorry,
  have hC2 : ∃ (C2 : ℝ), 0 < C2 ∧ ∀ (y : E), ∥id2 y∥ ≤ C2 * ∥y∥ := sorry,

  obtain ⟨C1, hC1_pos, hC1⟩ := hC1,
  obtain ⟨C2, hC2_pos, hC2⟩ := hC2,
  use [⟨C2, le_of_lt hC2_pos⟩, ⟨C1, le_of_lt hC1_pos⟩, hC2_pos, hC1_pos],
  rw forall_and_distrib,
  simp only at hC1 hC2,
  split,
  { intro y, exact hC2 ⟨y, (intermediate_field.algebra_adjoin_le_adjoin K _) y.2⟩ },
  { intro y, exact hC1 ⟨y, (intermediate_field.algebra_adjoin_le_adjoin K _) y.2⟩ },

end

lemma spectral_norm.unique_field_norm_ext {f : L → nnreal} (hf_field_norm : is_mul_norm f)
  (hf_ext : function_extends (λ x : K, ∥x∥₊) f) (hna : is_nonarchimedean (λ k : K, ∥k∥₊)) (x : L) :
  f x = spectral_norm h_alg x := 
begin
  have hf_pow : is_pow_mult f := is_mul_norm.to_is_pow_mult hf_field_norm,
  have hf_alg_norm : is_algebra_norm (normed_ring.to_is_norm K) f := 
  { smul := λ k x, by rw [algebra.smul_def, hf_field_norm.mul_eq, hf_ext k],
    ..hf_field_norm},
  rw spectral_norm.unique' h_alg hf_pow hf_alg_norm hna,
end

lemma spectral_norm.is_mul_norm (hna : is_nonarchimedean (λ k : K, ∥k∥₊)) : 
  is_mul_norm (spectral_norm h_alg) :=
{ mul_eq := λ x y, begin
    by_cases hx : 0 = spectral_norm h_alg x,
    { rw [← hx, zero_mul],
      rw [eq_comm, (spectral_norm.is_algebra_norm h_alg hna).to_is_norm.zero_iff] at hx,
      rw [hx, zero_mul, (spectral_norm.is_algebra_norm h_alg hna).to_is_norm.zero] },
    { set f := c_seminorm (spectral_norm.is_norm_le_one_class h_alg) hx
        (spectral_norm.is_algebra_norm h_alg hna).to_is_norm.to_is_seminorm
        (spectral_norm.is_pow_mult h_alg hna) with hf,
      have hf_pow : is_pow_mult f := c_seminorm_is_pow_mult (spectral_norm.is_norm_le_one_class 
        h_alg) hx (spectral_norm.is_algebra_norm h_alg hna).to_is_norm.to_is_seminorm
        (spectral_norm.is_pow_mult h_alg hna),
      have hf_alg_norm : is_algebra_norm (normed_ring.to_is_norm K) f := 
      { smul := λ k y,
        begin
          rw [← spectral_norm.extends h_alg, algebra.smul_def, hf],
          have h_mul : ∀ (y : L), spectral_norm h_alg ((algebra_map K L k) * y) = 
            spectral_norm h_alg (algebra_map K L k) * spectral_norm h_alg y,
          { intro y, rw [spectral_norm.extends h_alg, ← algebra.smul_def],
            exact (spectral_norm.is_algebra_norm h_alg hna).smul _ _ },
          rw ← c_seminorm_apply_of_is_mult _ _ _ _ h_mul,
          exact c_seminorm_is_mult_of_is_mult _ _ _ _ h_mul _,
        end,
        ..(c_seminorm_is_norm _ _ _ _ _) },
      rw [← spectral_norm.unique' h_alg hf_pow hf_alg_norm hna],
      rw [hf, c_seminorm_c_is_mult (spectral_norm.is_norm_le_one_class h_alg) hx
        (spectral_norm.is_algebra_norm h_alg hna).to_is_norm.to_is_seminorm
        (spectral_norm.is_pow_mult h_alg hna)] }
  end
  ..spectral_norm.is_algebra_norm h_alg hna }

def spectral_norm.normed_field (h : is_nonarchimedean (λ k : K, ∥k∥₊)) : normed_field L := 
{ norm      := λ (x : L), (spectral_norm h_alg x : ℝ),
  dist      := λ (x y : L), (spectral_norm h_alg (x - y) : ℝ),
  dist_self := λ x, by simp only [sub_self, nnreal.coe_eq_zero, spectral_norm.zero],
  dist_comm := λ x y, by rw [nnreal.coe_eq, ← neg_sub, spectral_norm.neg h_alg h],
  dist_triangle := λ x y z, begin
    simp only [dist_eq_norm],
    rw ← sub_add_sub_cancel x y z,
    exact add_le_of_is_nonarchimedean (spectral_norm.zero h_alg)
      (spectral_norm.is_nonarchimedean h_alg h) _ _,
  end,
  eq_of_dist_eq_zero := λ x y hxy,
  begin
    simp only [nnreal.coe_eq_zero] at hxy,
    rw ← sub_eq_zero,
    rw is_norm.zero_iff (spectral_norm.is_mul_norm h_alg h).to_is_norm at hxy,
    exact hxy,
  end,
  dist_eq := λ x y, by refl,
  norm_mul' := λ x y,
  begin
    simp only [← nnreal.coe_mul, nnreal.coe_eq],
    exact (spectral_norm.is_mul_norm h_alg h).mul_eq x y,
  end,
  ..hL }

/- noncomputable! instance us : uniform_space L := infer_instance

instance spectral_norm.complete_space (h_fin : @finite_dimensional K L _ _ _) :
  complete_space L := sorry -/

end spectral_valuation

--#lint