import rank_one_valuation
import normed_space
import power_mult_seminorm
import data.list.min_max
import field_theory.normal
import topology.algebra.valuation
import ring_theory.polynomial.vieta

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

def spectral_value_terms {p : R[X]} (hp : p.monic) : ℕ → nnreal := 
λ (n : ℕ), if n < p.nat_degree then 
∥ p.coeff n ∥₊^(1/(p.nat_degree - n : ℝ)) else 0

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

/- In this section we prove Proposition 3.1.2/1 from BGR. -/
section bdd_by_spectral_value
variables {K : Type*} [normed_field K] {L : Type*} [field L] [algebra K L] {f : L → ℝ≥0}

lemma polynomial.nat_degree_pos_of_monic_of_root {p : K[X]} (hp : p.monic) {x : L}
  (hx : polynomial.aeval x p = 0) : 0 < p.nat_degree := 
polynomial.nat_degree_pos_of_aeval_root (polynomial.ne_zero_of_ne_zero_of_monic one_ne_zero hp) hx
  ((injective_iff_map_eq_zero (algebra_map K L)).mp (algebra_map K L).injective)

-- Part (1): the norm of any root of p is bounded by the spectral value of p.
lemma root_norm_le_spectral_value (hf_pm : is_pow_mult f) (hf_u : is_ultrametric f)
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
          nnreal.pow_nat_rpow_nat_inv _ (tsub_pos_of_lt hn)] },
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
      have hna : is_nonarchimedean f := hf_u.add_le hf0,
      obtain ⟨m, hm_in, hm⟩ := is_nonarchimedean_finset_range_add_le hf0 hna p.nat_degree 
        (λ (i : ℕ), p.coeff i • x ^ i),
      exact lt_of_le_of_lt hm (hn' m (hm_in h_deg)) },
    have h0 : f 0 ≠ 0,
    { have h_eq : f 0 = f (x^(p.nat_degree)),
      { rw [← hx, polynomial.aeval_eq_sum_range, finset.sum_range_succ, add_comm, hp.coeff_nat_degree,
        one_smul, ← max_eq_left_of_lt h_lt],
        exact is_nonarchimedean_add_eq_max_of_ne hf_alg_norm.to_is_norm.to_is_seminorm 
        hf_u (ne_of_lt h_lt), },
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

/-  theorem mv_polynomial.prod_X_add_C_eval {R : Type u} [comm_semiring R] (σ : Type u)
 [fintype σ] (r : σ → R) :
finset.univ.prod (λ (i : σ), ⇑polynomial.C (r i) + polynomial.X) =
 (finset.range (fintype.card σ + 1)).sum (λ (i : ℕ), (finset.powerset_len i finset.univ).sum (λ (t : finset σ), t.prod (λ (i : σ), ⇑polynomial.C (r i))) * polynomial.X ^ (fintype.card σ - i))
-/

universe u
lemma polynomial.prod_X_sub_C_coeff {n : ℕ} (hn : 0 < n) (b : fin n → K)
  {m : ℕ} (hm : m ≤ n) : (finprod (λ (k : fin n), polynomial.X - (polynomial.C (b k)))).coeff m =
  (finset.powerset_len (n - m) finset.univ).sum
    (λ (t : finset (fin n)), t.prod (λ (i : (fin n)), - b i)) := 
begin
  simp_rw [sub_eq_neg_add, ← polynomial.C_neg, ← pi.neg_apply],
  rw finprod_eq_prod_of_fintype,
  rw mv_polynomial.prod_X_add_C_eval,
  simp only [fintype.card_fin, pi.neg_apply, map_neg, polynomial.finset_sum_coeff],

  -- (λ (x : finset (fin n)), x.prod (λ (x : fin n), -⇑polynomial.C (b x))) * polynomial.X ^ (n - b_1)).coeff m
  sorry
end

/-- Part (2): if p splits into linear factors over B, then its spectral value equals the maximum
  of the norms of its roots. -/
lemma max_root_norm_eq_spectral_value (hf_pm : is_pow_mult f) (hf_u : is_ultrametric f)
  (hf_alg_norm : is_algebra_norm (normed_ring.to_is_norm K) f) (hf1 : is_norm_le_one_class f)
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
    exact root_norm_le_spectral_value hf_pm hf_u hf_alg_norm hf1 _ hm, },
  { apply csupr_le,
    intros m,
    by_cases hm : m < p.nat_degree,
    { rw spectral_value_terms_of_lt_nat_degree _ hm,
      have h : 0 < (p.nat_degree - m : ℝ) := sorry,
      rw [← nnreal.rpow_le_rpow_iff h, ← nnreal.rpow_mul, one_div_mul_cancel (ne_of_gt h),
        nnreal.rpow_one, ← nat.cast_sub (le_of_lt hm), nnreal.rpow_nat_cast],

      sorry },
    { rw spectral_value_terms_of_nat_degree_le _ (le_of_not_lt hm),
      exact zero_le _, }}
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
  set h : L ≃ₐ[K] L := alg_equiv.lift_normal' L f,
  use alg_equiv.lift_normal' L f,
  simp_rw ← intermediate_field.adjoin_simple.algebra_map_gen K x,
  rw [alg_equiv.lift_normal_commutes' L f, minpoly.alg_equiv_apply,
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
  (hf_u : is_ultrametric f) (hf_alg_norm : is_algebra_norm (normed_ring.to_is_norm K) f)
  (hf1 : is_norm_le_one_class f) (x : L) : f x ≤ spectral_norm h_alg x :=
begin
  apply root_norm_le_spectral_value hf_pm hf_u hf_alg_norm hf1,
  rw [minpoly.aeval],
end

lemma spectral_norm.aut_isom (σ : L ≃ₐ[K] L) (x : L) : 
  spectral_norm h_alg x = spectral_norm h_alg (σ x) :=
by simp only [spectral_norm, minpoly.eq_of_conj h_alg]

-- We first assume that the extension is finite and normal
section finite

variable (h_fin : finite_dimensional K L)

section normal

variable (hn : normal K L)

lemma spectral_norm.is_pow_mult_of_fd : is_pow_mult (spectral_norm h_alg) :=
begin
  sorry
end

lemma spectral_norm.is_algebra_norm_of_fd :
  is_algebra_norm (normed_ring.to_is_norm K) (spectral_norm h_alg) :=
begin
  sorry
end

lemma spectral_norm.is_nonarchimedean_of_fd (h : is_nonarchimedean (λ k : K, ⟨∥k∥, norm_nonneg _⟩)) :
  is_nonarchimedean (spectral_norm h_alg) :=
begin
  sorry
end

lemma spectral_norm.extends_norm_of_fd : function_extends (λ x : K, ∥x∥₊) (spectral_norm h_alg) :=
begin
  sorry
end

lemma spectral_norm.unique_of_fd_normal {f : L → nnreal} (hf_pow : is_pow_mult f)
  (hf_alg_norm : is_algebra_norm (normed_ring.to_is_norm K) f) 
  (hf_ext : function_extends (λ x : K, ∥x∥₊) f)
  (hf_iso : ∀ (σ : L ≃ₐ[K] L) (x y : L), f (y - x) = f (σ (y - x)))
  (x : L) : f x = spectral_norm h_alg x :=
begin
  sorry
end

lemma spectral_norm.max_of_fd_normal {f : L → nnreal} (hf_pow : is_pow_mult f)
  (hf_alg_norm : is_algebra_norm (normed_ring.to_is_norm K) f) 
  (hf_ext : function_extends (λ x : K, ∥x∥₊) f) (x : L) :
  spectral_norm h_alg x = supr (λ (σ : L ≃ₐ[K] L), f (σ x)) :=
begin
  sorry
end

end normal

end finite

-- Now we let L/K be any algebraic extension

-- The spectral norm is a power-multiplicative K-algebra norm on L extending the norm on K.

lemma spectral_norm.is_pow_mult : is_pow_mult (spectral_norm h_alg) :=
begin
  sorry
end

lemma spectral_norm.is_norm_le_one_class : is_norm_le_one_class (spectral_norm h_alg) :=
begin
  sorry
end


lemma spectral_norm.smul (k : K) (y : L) :
  spectral_norm h_alg (k • y) ≤ ∥ k ∥₊ * spectral_norm h_alg y :=
begin
  sorry
end

lemma spectral_norm.is_algebra_norm :
  is_algebra_norm (normed_ring.to_is_norm K) (spectral_norm h_alg) :=
begin
  sorry
end

lemma spectral_norm.is_nonarchimedean (h : is_nonarchimedean (λ k : K, ⟨∥k∥, norm_nonneg _⟩)) :
  is_nonarchimedean (spectral_norm h_alg) :=
begin
  sorry
end

lemma spectral_norm.extends_norm : function_extends (λ x : K, ∥x∥₊) (spectral_norm h_alg) :=
begin
  sorry
end

lemma spectral_norm.unique {f : L → nnreal} (hf_pow : is_pow_mult f)
  (hf_alg_norm : is_algebra_norm (normed_ring.to_is_norm K) f) 
  (hf_ext : function_extends (λ x : K, ∥x∥₊) f)
  (hf_iso : ∀ (σ : L ≃ₐ[K] L) (x y : L), f (y - x) = f (σ (y - x)))
  (x : L) : f x = spectral_norm h_alg x :=
begin
  sorry
end

lemma spectral_norm.extends (k : K) : ∥ k ∥ = spectral_norm h_alg (algebra_map K L k) :=
begin

  sorry
end 

end spectral_norm

section spectral_valuation

variables {K : Type*} [normed_field K] [complete_space K] {L : Type*} [field L] [algebra K L]
(h_alg : algebra.is_algebraic K L)

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
lemma spectral_norm.unique' {f : L → nnreal} (hf_pow : is_pow_mult f)
  (hf_alg_norm : is_algebra_norm (normed_ring.to_is_norm K) f) (x : L) :
  f x = spectral_norm h_alg x := sorry

lemma spectral_norm.unique_field_norm_ext {f : L → nnreal} (hf_field_norm : is_mul_norm f)
   (hf_ext : function_extends (λ x : K, ∥x∥₊) f) (x : L) : f x = spectral_norm h_alg x := sorry

lemma spectral_norm.is_mul_norm : is_mul_norm (spectral_norm h_alg) :=
{ mul_eq := λ x y, begin
    by_cases hx : 0 = spectral_norm h_alg x,
    { sorry },
    { set f := c_seminorm (spectral_norm.is_norm_le_one_class h_alg) hx
        (spectral_norm.is_algebra_norm h_alg).to_is_norm.to_is_seminorm
        (spectral_norm.is_pow_mult h_alg) with hf,
      have hf_pow : is_pow_mult f := c_seminorm_is_pow_mult (spectral_norm.is_norm_le_one_class 
        h_alg) hx (spectral_norm.is_algebra_norm h_alg).to_is_norm.to_is_seminorm
        (spectral_norm.is_pow_mult h_alg),
      have hf_alg_norm : is_algebra_norm (normed_ring.to_is_norm K) f := sorry,
      simp only [← spectral_norm.unique' h_alg hf_pow hf_alg_norm],
      rw [hf, c_seminorm_c_is_mult (spectral_norm.is_norm_le_one_class h_alg) hx
        (spectral_norm.is_algebra_norm h_alg).to_is_norm.to_is_seminorm
        (spectral_norm.is_pow_mult h_alg)] }
  end
  ..spectral_norm.is_algebra_norm h_alg }

--instance spectral_norm.complete_space (h_fin : finite_dimensional K L) : complete_space L := sorry

end spectral_valuation