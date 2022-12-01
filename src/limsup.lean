import analysis.special_functions.pow --TODO: minimize
import order.filter.countable_Inter

noncomputable theory

lemma set.range.bdd_above.mul {f g : ℕ → ℝ} (hf : bdd_above (set.range f)) (hf0 : 0 ≤ f)
   (hg : bdd_above (set.range g)) (hg0 : 0 ≤ g) :  bdd_above (set.range (f * g)) :=
begin
  obtain ⟨bf, hbf⟩ := hf,
  obtain ⟨bg, hbg⟩ := hg,
  use bf*bg,
  simp only [mem_upper_bounds, set.mem_range, pi.mul_apply, forall_exists_index,
    forall_apply_eq_imp_iff'] at hbf hbg ⊢,
  intros n,
  exact mul_le_mul (hbf n) (hbg n) (hg0 n) (le_trans (hf0 n) (hbf n)),
end

namespace filter

lemma limsup_nonneg_of_nonneg {α β : Type*} [has_zero α]
  [conditionally_complete_linear_order α] {f : filter β} [hf_ne_bot : f.ne_bot] {u : β → α}
  (hf : is_bounded_under has_le.le f u) (h :  ∀ (n : β), 0 ≤ u n ) :
  0 ≤ limsup u f := 
le_limsup_of_frequently_le (frequently_of_forall h) hf


end filter


open filter
open_locale topological_space nnreal

/- lemma eventually_le_limsup [countable_Inter_filter f] (u : α → ℝ≥0∞) :
  ∀ᶠ y in f, u y ≤ f.limsup u :=
begin
  by_cases hx_top : f.limsup u = ⊤,
  { simp_rw hx_top,
    exact eventually_of_forall (λ a, le_top), },
  have h_forall_le : ∀ᶠ y in f, ∀ n : ℕ, u y < f.limsup u + (1:ℝ≥0∞)/n,
  { rw eventually_countable_forall,
    refine λ n, eventually_lt_of_limsup_lt _,
    nth_rewrite 0 ←add_zero (f.limsup u),
    exact (ennreal.add_lt_add_iff_left hx_top).mpr (by simp), },
  refine h_forall_le.mono (λ y hy, le_of_forall_pos_le_add (λ r hr_pos hx_top, _)),
  have hr_ne_zero : (r : ℝ≥0∞) ≠ 0,
  { rw [ne.def, coe_eq_zero],
    exact (ne_of_lt hr_pos).symm, },
  cases (exists_inv_nat_lt hr_ne_zero) with i hi,
  rw inv_eq_one_div at hi,
  exact (hy i).le.trans (add_le_add_left hi.le (f.limsup u)),
end-/

/- lemma real.exists_inv_nat_lt {a : ℝ} (h : a ≠ 0) :
  ∃n:ℕ, (n:ℝ)⁻¹ < a := sorry -/
/- inv_inv a ▸ by simp only [inv_lt_inv, ennreal.exists_nat_gt (inv_ne_top.2 h)]
 -/

-- This is false
/- instance : countable_Inter_filter (at_top : filter ℕ) :=
{ countable_sInter_mem' := λ S hS_count hS_at_top,
  begin
    simp only [mem_at_top_sets, ge_iff_le, set.mem_sInter],
    simp only [mem_at_top_sets, ge_iff_le] at hS_at_top,
    sorry
  end}

lemma real.eventually_le_limsup {u : ℕ → ℝ} (hu : bdd_above (set.range u)) :
  ∀ᶠ (n : ℕ) in at_top, u n ≤ filter.limsup u at_top :=
begin
  rw filter.limsup_eq,
  simp,
  use 0,intros n hn,
  apply le_cInf,
  { obtain ⟨B, hB⟩ := hu,
    use B,sorry },
  { intros x hx,
    simp only [set.mem_set_of_eq] at hx,
  sorry }
end

lemma real.eventually_le_limsup' {u : ℕ → ℝ} (hu : bdd_above (set.range u)) :
  ∀ᶠ (n : ℕ) in at_top, u n ≤ filter.limsup u at_top := 
begin
  have h_forall_le : ∀ᶠ y in at_top, ∀ n : ℕ, u y < limsup u at_top + (1 : ℝ)/(n + 1),
  {  --apply filter.forall_eventually_of_eventually_forall,
    --squeeze_simp,
    rw eventually_countable_forall,
    intros n,
    refine eventually_lt_of_limsup_lt _ _,
    simp only [one_div, lt_add_iff_pos_right, inv_pos, nat.cast_pos],
    { exact nat.cast_add_one_pos n},
    { simp only [auto_param_eq],
      rw is_bounded_under,
      rw is_bounded,
      obtain ⟨b, hb⟩ := hu,
      use b,
      --apply eventually_of_forall,
      simp only [mem_upper_bounds, set.mem_range, forall_exists_index,
       forall_apply_eq_imp_iff'] at hb,

      simp only [eventually_map],
      exact eventually_of_forall hb, }},
  refine h_forall_le.mono (λ y hy, le_of_forall_pos_le_add (λ r hr_pos, _)),
  cases (real.exists_inv_nat_lt (ne_of_gt hr_pos)) with i hi,
  rw inv_eq_one_div at hi,
  have hi' : 1 / (i + 1 : ℝ) < r := sorry,
  exact (hy i).le.trans (add_le_add_left hi'.le (limsup u at_top)),
end


 -/


lemma bdd_above.is_bounded_under {α : Type*} [preorder α] {u : α → ℝ} 
  (hu_bdd : bdd_above (set.range u)) : is_bounded_under has_le.le at_top u :=
begin
  obtain ⟨b, hb⟩ := hu_bdd,
  use b,
  simp only [mem_upper_bounds, set.mem_range, forall_exists_index,
    forall_apply_eq_imp_iff'] at hb,
  exact eventually_map.mpr (eventually_of_forall hb)
end


lemma exists_le_of_lt_cSup {α : Type*} [conditionally_complete_linear_order α] {s : set α} 
  {b : α} (hs : s.nonempty) (hb : b < has_Sup.Sup s) : ∃ a ∈ s, b ≤ a :=
by { contrapose! hb, apply cSup_le hs (λ x hx, (hb x hx).le) }

lemma filter.eventually_le_of_lt_liminf  {α β : Type*} {f : filter α} 
  [conditionally_complete_linear_order β] {u : α → β} {b : β} 
  (h : b < liminf u f) (hu : f.is_bounded_under (≥) u . is_bounded_default) :
  ∀ᶠ a in f, b ≤ u a :=
begin
  obtain ⟨c, hc, hbc⟩ : ∃ (c : β) (hc : c ∈ {c : β | ∀ᶠ (n : α) in f, c ≤ u n}), b ≤ c :=
    exists_le_of_lt_cSup hu h,
  exact hc.mono (λ x hx, le_trans hbc hx)
end

lemma filter.eventually_le_of_limsup_le {α β : Type*} {f : filter α} 
  [conditionally_complete_linear_order β] {u : α → β} {b : β} 
  (h : filter.limsup u f < b) 
  (hu : f.is_bounded_under (≤) u . is_bounded_default) :
  ∀ᶠ (a : α) in f, u a ≤ b := 
@filter.eventually_le_of_lt_liminf _ βᵒᵈ _ _ _ _ h hu


lemma real.eventually_le_limsup' {u : ℕ → ℝ} (hu : bdd_above (set.range u)) :
  ∀ᶠ (n : ℕ) in at_top, u n ≤ filter.limsup u at_top := 
sorry

lemma real.eventually_le_limsup {u : ℕ → ℝ} (hu : bdd_above (set.range u)) :
  ∀ᶠ (n : ℕ) in at_top, u n ≤ filter.limsup u at_top :=
begin
  have h_glb : is_glb {a : ℝ | ∀ᶠ (n : ℕ) in at_top, u n ≤ a}
    (Inf {a : ℝ | ∀ᶠ (n : ℕ) in at_top, u n ≤ a}),
  { apply  real.is_glb_Inf, 
    sorry,
    sorry, },
  rw is_glb_iff_le_iff at h_glb,
  --simp only [is_glb, is_greatest] at h_glb,
  rw limsup_eq,

  simp_rw [h_glb _, mem_lower_bounds],
  simp only [eventually_at_top, ge_iff_le, set.mem_set_of_eq, forall_exists_index],
  /- rw real.Inf_def,
  rw real.Sup_def,
  rw dif_pos, -/
  { sorry },


  /- have : ∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in at_top, u n < limsup u at_top + ε,
  { intros ε hε,
    exact eventually_lt_of_limsup_lt (lt_add_of_pos_right _ hε) hu.is_bounded_under },

  have h : ∀ᶠ (n : ℕ) in at_top, ∀ (ε : ℝ) (hε : 0 < ε), u n < limsup u at_top + ε,
  { sorry
  }, -/
  

  --simp only [eventually_at_top, ge_iff_le],

  --simp_rw le_iff_forall_pos_lt_add,
  --apply filter.forall_eventually_of_eventually_forall ,
  --apply eventually_lt_of_limsup_lt,
  /- rw limsup_eq,
  simp only [eventually_at_top, ge_iff_le],
  by_contra' h, -/
  
  /- by_contra' h,
  simp only [eventually_at_top, ge_iff_le, not_exists, not_forall, not_le, 
    exists_prop] at h, -/
end

lemma real.limsup_mul_le {u v : ℕ → ℝ} (hu_bdd : bdd_above (set.range u)) (hu0 : 0 ≤ u) 
  (hv_bdd : bdd_above (set.range v)) (hv0 : 0 ≤ u) :
  filter.limsup (u * v) at_top ≤ filter.limsup u at_top * filter.limsup v at_top :=
begin
  simp only [filter.limsup_eq, pi.mul_apply, eventually_at_top, ge_iff_le],

  rw le_iff_forall_pos_lt_add,
  intros ε hε,
  --apply cInf_lt_of_lt,
  
  
  /- apply limsup_le_of_le,

  { simp only [auto_param_eq],
    rw is_cobounded_under, rw is_cobounded,
    use 0,
    intros z hz,
    simp only [eventually_map, pi.mul_apply, eventually_at_top, ge_iff_le] at hz,
    obtain ⟨n, hn⟩ := hz,

    sorry },
  { simp only [pi.mul_apply, eventually_at_top, ge_iff_le],
    sorry } -/
end

lemma nnreal.limsup_mul_le /- {α : Type*} [preorder α] -/ (u v : ℕ → ℝ≥0) :
  filter.limsup (u * v) at_top ≤ filter.limsup u at_top * filter.limsup v at_top :=
begin
  haveI : nonempty ↥{a : ℝ≥0 | ∀ᶠ (n : ℕ) in at_top, u n ≤ a} := sorry,
  have hs : {a : ℝ≥0 | ∀ᶠ (n : ℕ) in at_top, u n ≤ a}.nonempty := sorry,
  
  
  --rw ← cInf_mul hs,
  sorry
end

/- lemma real.limsup_mul_le /- {α : Type*} [preorder α] -/ (u v : ℕ → ℝ) :
  filter.limsup (u * v) at_top ≤ filter.limsup u at_top  * filter.limsup v at_top := 
begin
  simp only [filter.limsup, filter.Limsup, eventually_map, pi.mul_apply, eventually_at_top, 
    ge_iff_le],
  rw cInf_le_iff,
  intros c hc,
  simp only [mem_lower_bounds, set.mem_set_of_eq, forall_exists_index] at hc,

  apply hc,
  /- simp only [Inf],
  simp only [conditionally_complete_lattice.Inf], -/
  
  sorry,
  { sorry },
  { use filter.limsup (u * v) at_top,
    --simp only [set.mem_set_of_eq],
    --refine eventually_at_top.mp _,
    
    sorry }, sorry,
end
 -/
/- lemma exists_le_of_limsup_le {x : ℝ} {u : ℕ → ℝ} (hu_nonneg : 0 ≤ u)
  (hu : filter.limsup u at_top ≤ x) {ε : ℝ} (hε : 0 < ε) : ∃ n : pnat, u n ≤ x + ε :=
begin
  rw [filter.limsup, filter.Limsup, real.Inf_le_iff] at hu,
  { obtain ⟨y, hy, hyx⟩ := hu ε hε,
    simp only [eventually_map, eventually_at_top, ge_iff_le, set.mem_set_of_eq] at hy,
    obtain ⟨n, hn⟩ := hy,
    exact ⟨⟨n + 1, nat.succ_pos _⟩, le_trans (hn (n + 1) (nat.le_succ _)) (le_of_lt hyx)⟩ },
  { use 0,
    rw mem_lower_bounds,
    intros y hy,
    simp only [eventually_map, eventually_at_top, ge_iff_le, set.mem_set_of_eq] at hy,
    obtain ⟨n, hn⟩ := hy,
    apply le_trans (hu_nonneg n) (hn n (le_refl n)) },
  { sorry/- use filter.limsup u at_top,
    exact real.eventually_le_limsup _, -/ }
end -/



lemma eventually_lt_of_limsup_le {α : Type*} [preorder α] {x : ℝ} {u : α → ℝ} 
  (hu_bdd : is_bounded_under has_le.le at_top u) (hu : filter.limsup u at_top ≤ x) 
  {ε : ℝ} (hε : 0 < ε) : ∀ᶠ (a : α ) in at_top, u a < x + ε :=
filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt hu (lt_add_of_pos_right x hε)) hu_bdd

lemma exists_lt_of_limsup_le {x : ℝ} {u : ℕ → ℝ} (hu_bdd : is_bounded_under has_le.le at_top u)
  (hu : filter.limsup u at_top ≤ x) {ε : ℝ} (hε : 0 < ε) :
  ∃ n : pnat, u n < x + ε :=
begin
  have h : ∀ᶠ (a : ℕ) in at_top, u a < x + ε := eventually_lt_of_limsup_le hu_bdd hu hε,
  simp only [eventually_at_top, ge_iff_le] at h,
  obtain ⟨n, hn⟩ := h,
  exact ⟨⟨n + 1, nat.succ_pos _⟩,hn (n + 1) (nat.le_succ _)⟩,
end


/- filter.eventually_lt_of_limsup_lt -/