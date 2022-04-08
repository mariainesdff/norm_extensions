import data.real.basic
import order.filter.at_top_bot
import order.liminf_limsup
import topology.metric_space.basic
import topology.algebra.order.monotone_convergence


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

/- lemma le_of_is_lub {α : Type*} [preorder α] (S : set α) (B : α) (hB : is_lub S B) :
  ∀ s ∈ S, s ≤ B := 
begin
  intros s hs,
  simp [is_lub, is_least, mem_upper_bounds] at hB,
  exact hB.1 s hs,
end
 -/
lemma filter.tendsto_of_is_bounded_monotone {f : ℕ → ℝ} (h_bdd : bdd_above (set.range f))
  (h_mon : monotone f) : ∃ r : ℝ, filter.tendsto f filter.at_top (𝓝 r) :=
begin
  obtain ⟨B, hB⟩ := (real.exists_is_lub ((set.range f)) (set.range_nonempty f) h_bdd),
  use B,
  exact tendsto_at_top_is_lub h_mon hB,
end

/- lemma antitone.neg {α β : Type*} [preorder α] [preorder β] [add_group β]
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
end -/

lemma filter.tendsto_of_is_bounded_antitone {f : ℕ → ℝ} (h_bdd : bdd_below (set.range f)) 
  (h_ant : antitone f) : ∃ r : ℝ, filter.tendsto f filter.at_top (𝓝 r) :=
begin
  obtain ⟨B, hB⟩ := (real.exists_is_glb ((set.range f)) (set.range_nonempty f) h_bdd),
  use B,
  exact tendsto_at_top_is_glb h_ant hB,
end