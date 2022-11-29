import order.filter.ennreal
import order.liminf_limsup
import topology.instances.nnreal



section nnreal

open filter 
open_locale nnreal

--variables  {f : filter α} [countable_Inter_filter f]

lemma limsup_const_mul {α : Type*} {f : filter α } (hf : f.ne_bot) (u : α → ℝ≥0) (a : ℝ≥0)
  (hu_bdd : is_bounded_under has_le.le f u) : --(hu_cob : is_cobounded_under has_le.le f u) :
  f.limsup (λ (x : α), a * (u x)) = a * f.limsup u :=
begin
  by_cases ha_zero : a = 0,
  { simp_rw [ha_zero, zero_mul],
    exact limsup_const 0 },
  let g := λ x : ℝ≥0, a * x,
  have hg_bij : function.bijective g,
  from function.bijective_iff_has_inverse.mpr ⟨(λ x, a⁻¹ * x),
    ⟨λ x, by simp [←mul_assoc, inv_mul_cancel ha_zero],
    λ x, by simp [g, ←mul_assoc, mul_inv_cancel ha_zero]⟩⟩,
  have hg_mono : strict_mono g,
  { exact monotone.strict_mono_of_injective (λ x y hxy, mul_le_mul_left' hxy _) hg_bij.1 },
  let g_iso := strict_mono.order_iso_of_surjective g hg_mono hg_bij.2,
  refine (order_iso.limsup_apply g_iso _ _ _ _).symm,
  { exact hu_bdd },
  { use [0, λ a ha, zero_le'], },
  { obtain ⟨b, hb⟩ := hu_bdd,
    simp only [strict_mono.coe_order_iso_of_surjective, auto_param_eq],
    use g b,
    simp only [eventually_map, filter.eventually, mem_map, set.preimage_set_of_eq] at hb ⊢,
    simp_rw hg_mono.le_iff_le,
    exact hb, },
  { use [0, λ a ha, zero_le'], }
end

lemma limsup_mul_const {α : Type*} {f : filter α} (hf : f.ne_bot) (u : α → ℝ≥0) (a : ℝ≥0)
  (hu_bdd : is_bounded_under has_le.le f u) :
  f.limsup (λ (x : α), (u x) * a) = f.limsup u * a:=
begin
  rw mul_comm,
  simp_rw mul_comm,
  exact limsup_const_mul hf u a hu_bdd,
end


lemma foo {f : filter ℕ } (hf : f.ne_bot) (u : ℕ → ℝ≥0) 
  (hu_bdd : is_bounded_under has_le.le f u) :
  (((f.limsup u) : nnreal) : ennreal) = f.limsup (λ x : ℕ, (u x : ennreal)) :=
begin
 -- obtain ⟨b, hb⟩ := hu_bdd,
  --simp only [eventually_map, filter.eventually, mem_map, set.preimage_set_of_eq] at hb,
  
  ext x,
  simp only [option.mem_def, ennreal.some_eq_coe, ennreal.coe_eq_coe],
  simp only [filter.limsup_eq],
  simp only [subset_Inf_def],
  have hcInf : (0 : ℝ) ≤ Inf (coe '' {a : ℝ≥0 | ∀ᶠ (n : ℕ) in f, u n ≤ a}),
  { refine le_cInf _ _,
    { simp only [set.nonempty_image_iff],
      exact hu_bdd },
    intros b hb,
    simp only [set.mem_image, set_coe.exists, subtype.coe_mk, exists_and_distrib_right,
      exists_eq_right] at hb,
    obtain ⟨c, hc_in, hcb⟩ := hb,
    rw ← hcb,
    exact nnreal.coe_nonneg c },
  erw dif_pos hcInf,
  { split; intro h,
    { rw ← h,
      have : ((⟨Inf ((coe : nnreal → ℝ) '' {a : ℝ≥0 | ∀ᶠ (n : ℕ) in f, u n ≤ a}), 
        hcInf⟩ : nnreal): ℝ) =
        Inf ((coe : nnreal → ℝ) '' {a : ℝ≥0 | ∀ᶠ (n : ℕ) in f, u n ≤ a}) := rfl,
      sorry--rw this,
      },
    { sorry }},
  
end

section ennreal

--variables {α : Type*}

lemma eventually_le_limsup'  (u : ℕ → ennreal) :
  ∀ᶠ y in (filter.at_top : filter ℕ), u y ≤ (filter.at_top : filter ℕ).limsup u :=
begin
  set f := (filter.at_top : filter ℕ) with hf,
  by_cases hx_top : f.limsup u = ⊤,
  { simp_rw hx_top,
    exact eventually_of_forall (λ a, le_top), },
  have h_forall_le : ∀ᶠ y in f, ∀ n : ℕ, u y < f.limsup u + (1:ennreal)/n,
  { rw hf,
    simp only [eventually_at_top, ge_iff_le],
    sorry,/-  rw eventually_countable_forall,
    refine λ n, eventually_lt_of_limsup_lt _,
    nth_rewrite 0 ←add_zero (f.limsup u),
    exact (ennreal.add_lt_add_iff_left hx_top).mpr (by simp), -/ },
  refine h_forall_le.mono (λ y hy, ennreal.le_of_forall_pos_le_add (λ r hr_pos hx_top, _)),
  have hr_ne_zero : (r : ennreal) ≠ 0,
  { rw [ne.def, ennreal.coe_eq_zero],
    exact (ne_of_lt hr_pos).symm, },
  cases (ennreal.exists_inv_nat_lt hr_ne_zero) with i hi,
  rw inv_eq_one_div at hi,
  exact (hy i).le.trans (add_le_add_left hi.le (f.limsup u)),
end

end ennreal

#exit

lemma eventually_le_limsup {α : Type*} {f : filter α } [countable_Inter_filter f] (hf : f.ne_bot) (u : α → ℝ≥0) (a : ℝ≥0)
  (hu_bdd : is_bounded_under has_le.le f u) :
  ∀ᶠ y in f, u y ≤ f.limsup u :=
begin
  simp_rw ← ennreal.coe_le_coe,
  simp_rw foo hf u hu_bdd,
  exact ennreal.eventually_le_limsup _,
end

instance : countable_Inter_filter (filter.at_top : filter ℕ ) := infer_instance

#exit
lemma limsup_mul_le_of_bdd (u v : ℕ → nnreal) :
  filter.limsup filter.at_top (u * v) ≤ filter.at_top.limsup u * filter.at_top.limsup v :=
begin
  have : filter.at_top.limsup (u * v) ≤ filter.at_top.limsup (λ x, (filter.at_top.limsup u) * v x),
  { apply limsup_le_limsup,
    { filter_upwards [eventually_le_limsup _ u _] with x hx,
      exact mul_le_mul' hx le_rfl, },
    { obtain ⟨a, ha⟩ := eventually_at_top.mp (eventually_le_limsup v),
      use filter.at_top.limsup u * filter.at_top.limsup v,
      rw [eventually_map, eventually_at_top],
      use [a, λ b hb,mul_le_mul' (le_refl _) (ha b hb)], }},
  apply le_trans this,
  rw limsup_const_mul,
end

end nnreal