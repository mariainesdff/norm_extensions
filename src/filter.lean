import data.real.basic
import order.filter.at_top_bot
import order.liminf_limsup
import topology.metric_space.basic

open_locale filter topological_space

theorem real.exists_is_glb (S : set ℝ) (hne : S.nonempty) (hbdd : bdd_below S) :
  ∃ x, is_glb S x :=
begin
  set T := - S with hT,
  have hT_ne : T.nonempty := set.nonempty_neg.mpr hne,
  have hT_bdd : bdd_above T := bdd_above_neg.mpr hbdd,
  use -classical.some (real.exists_is_lub T hT_ne hT_bdd),
  simpa [← is_lub_neg] using (classical.some_spec (real.exists_is_lub T hT_ne hT_bdd)),
end

lemma le_of_is_lub {α : Type*} [preorder α] (S : set α) (B : α) (hB : is_lub S B) :
  ∀ s ∈ S, s ≤ B := 
begin
  intros s hs,
  simp [is_lub, is_least, mem_upper_bounds] at hB,
  exact hB.1 s hs,
end

lemma filter.tendsto_of_is_bounded_monotone {f : ℕ → ℝ} (h_bdd : bdd_above (set.range f))
  (h_mon : monotone f) : ∃ r : ℝ, filter.tendsto f filter.at_top (𝓝 r) :=
begin
  obtain ⟨B, hB⟩ := (real.exists_is_lub ((set.range f)) (set.range_nonempty f) h_bdd),
  use B,
  rw metric.tendsto_at_top,
  intros ε hε,
  have hN : ∃ N : ℕ, B - ε < f N,
  { by_contra' h_contr,
    have h_bound : (B - ε) ∈ upper_bounds (set.range f) ,
    { rw mem_upper_bounds,
      intros x hx,
      cases (set.mem_range.mpr hx) with n hn,
      rw ← hn,
      exact h_contr n, },
    rw ← (is_lub_iff_le_iff.mp hB) (B - ε) at h_bound,
    linarith,},
  cases hN with N hN,
  use N,
  intros n hn,
  simp only [dist, abs_lt],
  refine ⟨by linarith [h_mon hn], lt_of_le_of_lt _ (gt_iff_lt.mp hε)⟩,
  { rw [sub_nonpos],
    apply le_of_is_lub ((set.range f)) B hB,
    simp only [set.image_univ, set.mem_range_self], }
end

lemma antitone.neg {α β : Type*} [preorder α] [preorder β] [add_group β]
  [covariant_class β β (+) (preorder.to_has_le β).le]
  [covariant_class  β β (function.swap (+)) (preorder.to_has_le β).le] {f : α → β}
  (h_ant : antitone f) : monotone (-f) :=
λ x y hxy, by simpa [pi.neg_apply, neg_le_neg_iff] using h_ant hxy

lemma set.range_neg {α β : Type*} [add_group β] (f : α → β) :
  set.range (-f) = - (set.range f) :=
begin
  ext x,
  simp only [set.mem_range, pi.neg_apply, set.mem_neg],
  split; rintro ⟨y, hy⟩; use y,
  exacts [eq_neg_iff_eq_neg.mpr (eq.symm hy), (neg_eq_iff_neg_eq.mpr (eq.symm hy))],
end

lemma filter.tendsto_of_is_bounded_antitone {f : ℕ → ℝ} (h_bdd : bdd_below (set.range f)) 
  (h_ant : antitone f) : ∃ r : ℝ, filter.tendsto f filter.at_top (𝓝 r) :=
begin
  have h_bdd_ab : bdd_above (set.range (-f)),
  { simpa [set.range_neg f, bdd_above_neg] using h_bdd },
  obtain ⟨r, hr⟩ := filter.tendsto_of_is_bounded_monotone h_bdd_ab (antitone.neg h_ant),
  exact ⟨-r, by simpa [pi.neg_apply, neg_neg] using (filter.tendsto.neg hr)⟩
end