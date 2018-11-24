/-
  The lemmas in this file will soon be in mathlib
-/

import data.list.basic
import data.int.basic
import tactic.ring

open list nat

variables {α : Type*} {β : Type*}

lemma reverse_range'_map_range' (a b : ℕ) : reverse (range' a (b+1-a)) = map (λ i, a+b-i) (range' a (b+1-a)) :=
begin
  rw [reverse_range', range'_eq_map_range, list.map_map],
  apply map_congr, intros i H,
  simp at *,
  rw [nat.add_sub_add_left, nat.add_sub_cancel'], {refl},
  apply le_of_not_le (λ h, _),
  rw sub_eq_zero_of_le h at H,
  exact not_lt_zero _ H
end

lemma filter_ext {α : Type*} {r: list α} (P P') [decidable_pred P] [decidable_pred P']
  (HP : ∀ i ∈ r, P i = P' i) : filter P r = filter P' r :=
begin
  induction r with h t IH,
  { simp },
  { have HPh : P h = P' h := HP h (by simp),
    have : ∀ (i : α), i ∈ t → P i = P' i,
    { intros i i_t,
      exact (HP i $ by simp [i_t]) },
    by_cases H : P h,
    { have H' : P' h := HPh ▸ H,
      simp [H, H', IH this] },
    { have H' : ¬ P' h := HPh ▸ H,
      simp [H, H', IH this] } }
end

lemma foldr_congr' {α : Type*} {β : Type*} {l : list α} (f f' : α → β → β) (s : β)
  (H : ∀ a ∈ l, ∀ b : β, f a b = f' a b) : foldr f s l = foldr f' s l :=
by induction l; simp * {contextual := tt}

lemma range'_add_map (a b k : ℕ) : range' (a+k) b = map (λ x, x + k) (range' a b) :=
begin
  revert a,
  induction b with b IH; intro a,
  { refl },
  { simpa using (IH $ a + 1) }
end

lemma range'_sub_map (a b k : ℕ) : range' a b = map (λ x, x - k) (range' (a+k) b) :=
begin
  suffices : (λ (x : ℕ), x - k) ∘ (λ (x : ℕ), x + k) = id,
  { rw [range'_add_map, list.map_map, this, map_id] },
  { funext, simp [nat.add_sub_cancel_left] }
end


lemma filter_map_comm {I : Type*} {J : Type*} (f : I → J) (P : J → Prop) (r: list I) [decidable_pred P] :
  filter P (map f r) = map f (filter (P ∘ f) r) :=
begin
  induction r with h _ IH,
  { simp },
  { by_cases H : P (f h) ; simp [filter_cons_of_pos, filter_cons_of_neg, H, IH] }
end

lemma list.map_eq_nil {α : Type*} {β : Type*} (f : α → β) (l : list α) : map f l = [] ↔ l = [] :=
⟨eq_nil_of_map_eq_nil, λ h, by rw h ; refl⟩

-- theorem mem_range_iff {m n r : ℤ} : r ∈ range m n ↔ m ≤ r ∧ r < n
lemma list.eq_nil_iff_not_mem {α : Type*} (l : list α) : l = [] ↔ ∀ x, x ∉ l :=
⟨λ h, by simp[h],
begin
  intro H,
  cases l with h t,
  refl,
  exfalso,
  specialize H h,
  have : h ∈ list.cons h t, by simp,
  exact H this
end
⟩

lemma list.range_eq_nil (n : ℕ) : range n = [] ↔ n = 0 :=
begin
  rw list.eq_nil_iff_not_mem,
  change (∀ (x : ℕ), ¬ x ∈ range n) ↔ n = 0,
  simp [mem_range],
  split ; intro h,
  exact eq_zero_of_le_zero (h 0),
  rw h,
  exact nat.zero_le,
end

@[simp]
lemma int.to_nat_zero : int.to_nat 0 = 0 := rfl

lemma int.to_nat_sub_eq_zero (a b : ℤ) : int.to_nat (b - a) = 0 ↔ b ≤ a :=
sorry

lemma int.range_eq_nil (a b) : int.range a b = [] ↔ b ≤ a :=
by unfold int.range ; rw [list.map_eq_nil, list.range_eq_nil, int.to_nat_sub_eq_zero]

lemma int.range_shift (a b k) : int.range (a+k) (b+k) = map (λ x, x+k) (int.range a b) :=
begin
  unfold int.range,
  rw [list.map_map, show b + k - (a + k) = b - a , by ring],
  congr,
  ext n,
  simp
end

lemma reverse_int_range_map_int_range (a b) : reverse (int.range a b) = map (λ i, a+b-i-(1 : ℤ)) (int.range a b) :=
begin
  unfold int.range,
  rw ←list.map_reverse,
  sorry
end

def h (a b) := concat (int.range a (b-1)) (b-1)

lemma int_range_eq_concat {a b} (h : a ≤ b) : int.range a b = concat (int.range a (b-1)) (b-1) :=
begin
  unfold int.range,
  sorry
end