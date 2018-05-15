import data.list.basic
import tactic.ring

open list

variables {R : Type*} {I : Type*} (op : R → R → R) (nil: R) 
          (r : list I) (P : I → Prop) [decidable_pred P] (F : I → R)

local infix ` ◆ `:70 := op -- type using \di 


/- Starting from `F : I → R`, `r : list I`, a composition law `op` on `R`, 
   a element `nil` in R, and a decidable predicate `P` on `I`,
   `apply_bigop op nil r P F` is the big "product", for operation `op`, 
   of all `F i` for `i` in `r` if `P i`. All parenthesis are closed after 
   inserting `nil` at the very end, like in `(a op (b op (c op nil)))`
   (using infix notation for op) -/
def apply_bigop := foldr (λ i, op (F i)) nil (filter P r)

-- alternate definition : foldr (λ i x, if P i then op (F i) x else x) nil r

/- We now define a notation with many variations depending on the list, 
   predicate, operation -/

/- variable in filtered list -/

notation `big[`:0 op`/`:0 nil`]_(`:0 binder `∈` r `|` P:(scoped p, p)`)` F:(scoped f, f) := 
apply_bigop op nil r P F

notation `Σ_(`:0 binder `∈` r `|` P:(scoped p, p) `)` F:(scoped f, f) := 
apply_bigop (+) 0 r P F

notation `Π_(`:0 binder `∈` r `|` P:(scoped p, p) `)` F:(scoped f, f) := 
apply_bigop (*) 1 r P F

/- variable in unfiltered list -/

notation `big[`:0 op `/`:0 nil `]_(`:0 binder `∈` r `)` F:(scoped f, f) := 
apply_bigop op nil r (λ i, true) F

notation `Σ_(`:0 binder `∈` r `)` F:(scoped f, f) := 
apply_bigop (+) 0 r (λ i, true) F

notation `Π_(`:0 binder `∈` r `)` F:(scoped f, f) := 
apply_bigop (*) 1 r (λ i, true) F

/- variable is natural numbers from a to b filtered -/

notation `big[`op`/`:0 nil`]_(`:0 binder`=`a`..`b `|` P:(scoped p, p)`)` F:(scoped f, f) := 
apply_bigop op nil (range' a (b+1-a)) P F

notation `Σ_(`:0 binder`=`a`..`b `|` P:(scoped p, p)`)` F:(scoped f, f) := 
apply_bigop (+) 0 (range' a (b+1-a)) P F

notation `Π_(`:0 binder`=`a`..` b `|` P:(scoped p, p)`)` F:(scoped f, f) := 
apply_bigop (*) 1 (range' a (b+1-a)) P F


/- variable is natural numbers from a to b -/

notation `big[`:0 op `/`:0 nil `]_(`:0 binder `=` a `..` b `)` F:(scoped f, f) := 
apply_bigop op nil (range' a (b+1-a)) (λ i, true) F

notation `Σ_(`:0 binder `=` a `..` b `)` F:(scoped f, f) := 
apply_bigop (+) 0 (range' a (b+1-a)) (λ i, true) F

notation `Π_(`:0 binder `=` a `..` b `)` F:(scoped f, f) := 
apply_bigop (*) 1 (range' a (b+1-a)) (λ i, true) F

local notation `?(F` h`)` := if P h then F h else nil

/- First lemmas, without assuming anything on `op` and `nil` -/


lemma big.nil : (big[(◆)/nil]_(i ∈ [] | (P i)) (F i)) = nil :=
by simp [apply_bigop]

lemma big_cons_true {h} (t) (Ph : P h) : 
  (big[(◆)/nil]_(i ∈ h::t | (P i)) (F i)) = F h ◆ (big[(◆)/nil]_(i ∈ t | (P i)) (F i)):=
by simp [apply_bigop, Ph]

lemma big_cons_false {h} (t) (Ph : ¬ P h) :
  (big[(◆)/nil]_(i ∈ h::t | (P i)) (F i)) = (big[(◆)/nil]_(i ∈ t | (P i)) (F i)) :=
by simp [apply_bigop, Ph]

lemma filter_congr {α : Type*} {p q : α → Prop} [decidable_pred p] [decidable_pred q]
  : ∀ {l : list α}, (∀ x ∈ l, p x ↔ q x) → filter p l = filter q l
| [] _     := rfl
| (a::l) h := by simp at h; by_cases pa : p a;
  [simp [pa, h.1.1 pa, filter_congr h.2],
   simp [pa, mt h.1.2 pa, filter_congr h.2]]

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

lemma foldr_ext {α : Type*} {β : Type*} {l : list α} (f f' : α → β → β) (s : β)
  (H : ∀ a ∈ l, ∀ b : β, f a b = f' a b) : foldr f s l = foldr f' s l :=
by induction l; simp * {contextual := tt}

-- A version of extensionality where we assume same (◆)/nil and same list
@[extensionality]
lemma big.ext (P') [decidable_pred P'] (F' : I → R) 
  (HP : ∀ i ∈ r, P i ↔ P' i) (HF : ∀ i ∈ r, F i = F' i) :
  (big[(◆)/nil]_(i ∈ r | (P i)) (F i)) = (big[(◆)/nil]_(i ∈ r | (P' i)) (F' i)) :=
begin
  unfold apply_bigop,
  rw filter_congr HP,
  apply foldr_ext,
  intros _ i_r _,
  simp[HF, mem_filter.1 i_r]
end

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
  { rw [range'_add_map, map_map, this, map_id] },
  { funext, simp [nat.add_sub_cancel_left] }
end


lemma filter_map_comm {I : Type*} {J : Type*} (f : I → J) (P : J → Prop) (r: list I) [decidable_pred P] :
  filter P (map f r) = map f (filter (P ∘ f) r) :=
begin
  induction r with h _ IH,
  { simp },
  { by_cases H : P (f h) ; simp [filter_cons_of_pos, filter_cons_of_neg, H, IH] }
end

lemma big.map {J : Type*} (f : I → J) (P : J → Prop) [decidable_pred P] (F : J → R) : 
  (big[(◆)/nil]_(j ∈ map f r | (P j)) (F j)) = (big[(◆)/nil]_(i ∈ r | (P (f i))) (F (f i))) :=
by simp[apply_bigop, filter_map_comm, foldr_map]

--set_option pp.all true

lemma big.empty_range (P : ℕ → Prop) [decidable_pred P] (F : ℕ → R) (a b : ℕ)
  (H : b < a) : (big[(◆)/nil]_(i=a..b | (P i)) (F i)) = nil :=
begin
  have t : range' a (b + 1 - a) = list.nil, by simp [nat.sub_eq_zero_iff_le.2 H],
  rw t,
  apply big.nil op nil P F,
end

lemma big.shift (P : ℕ → Prop) [decidable_pred P] (F : ℕ → R) (a b k : ℕ) : 
  (big[(◆)/nil]_(i=a..b | (P i)) (F i)) = (big[(◆)/nil]_(i=(a+k)..(b+k) | (P (i-k))) (F (i-k))) :=
begin
  rw [range'_add_map, big.map],
  have : b + k + 1 - (a + k) = b + 1 - a := 
    by rw [add_comm a, ← nat.sub_sub, add_right_comm, nat.add_sub_cancel],
  congr_n 1 ; funext; simp only [nat.add_sub_cancel,  this]
end

/- Now we go towards assuming (R, op, nil) is a monoid -/

/- Also need to make sure old hierarchy talks to new one.
   Associativity seems ok but we need: -/
instance add_monoid_is_left_id (α : Type*) [add_monoid α] : is_left_id α (+) 0 := ⟨by simp⟩

instance add_monoid_is_right_id (α : Type*) [add_monoid α] : is_right_id α (+) 0 := ⟨by simp⟩


instance monoid_is_left_id (α : Type*) [monoid α] : is_left_id α (*) 1 := ⟨by simp⟩

instance monoid_is_right_id (α : Type*) [monoid α] : is_right_id α (*) 1 := ⟨by simp⟩


section nil_left_id
/- Assuming only that nil is left neutral for op -/
variable [is_left_id R op nil]
open is_left_id

lemma big.cons {h} (t) : 
  (big[(◆)/nil]_(i ∈ h::t | (P i)) (F i)) = ?(F h) ◆ (big[(◆)/nil]_(i ∈ t | (P i)) (F i)):=
begin
  by_cases H : P h,
  { simp [H, big_cons_true] },
  { simp [H, big_cons_false, left_id op] }
end
end nil_left_id

section nil_right_id
/- Assuming only that nil is left neutral for op -/
variable [is_right_id R op nil]
open is_right_id

lemma big.one_term (i₀ : I) : (big[(◆)/nil]_(i ∈ [i₀]) F i) = F i₀ :=
by simp [apply_bigop, right_id op]

lemma big.one_term' (i₀ : I) : 
  (big[(◆)/nil]_(i ∈ [i₀] | P i) F i) = if P i₀ then F i₀ else nil :=
by by_cases H : P i₀;  simp [H, apply_bigop, right_id op]
 
end nil_right_id

section left_monoid
/- Assume that (R, op) is almost a monoid with neutral element nil -/

variables [is_left_id R op nil] [is_associative R op]
open is_left_id is_associative

lemma big.append (r₁ r₂ : list I) : 
  (big[(◆)/nil]_(i ∈ r₁++r₂ | (P i)) (F i)) = 
  (big[(◆)/nil]_(i ∈ r₁ | (P i)) (F i)) ◆ (big[(◆)/nil]_(i ∈ r₂ | (P i)) (F i)) :=
begin
  let Op := λ l, big[(◆)/nil]_(i ∈ l | (P i)) (F i),
  induction r₁ with h t IH,
  { exact (eq.symm $ calc
    Op [] ◆ Op r₂ =  nil ◆ (big[(◆)/nil]_(i ∈ r₂ | P i)F i) : by {dsimp [Op], rw big.nil}
    ... = _ : left_id _ _ )},
  { have : ?(F h) ◆ Op t = Op (h :: t) :=
    eq.symm (big.cons _ _ _ _ _),
    exact calc
    Op (h :: t ++ r₂) 
        = Op (h :: (t ++ r₂))      : rfl
    ... = ?(F h) ◆ Op (t ++ r₂)    : big.cons _ _ _ _ _
    ... = ?(F h) ◆ (Op t ◆ Op r₂)  : by simp [Op, IH]
    ... = (?(F h) ◆ Op t) ◆ Op r₂  : eq.symm $ assoc _ _ _ _
    ... = Op (h::t) ◆ Op r₂        : by rw this }
end

/- Sample specialization -/
lemma sum_append (r₁ r₂ : list I) (F : I → ℕ) :
  (Σ_(i ∈ r₁ ++ r₂ | P i) F i) =  (Σ_(i ∈ r₁ | P i) F i) + Σ_(i ∈ r₂ | P i) F i :=
by apply big.append
end left_monoid

section monoid
variables [is_left_id R op nil] [is_right_id R op nil] [is_associative R op]
open is_left_id is_right_id is_associative

lemma big.commute_through {a : R} (H : ∀ i ∈ r, P i → a ◆ F i = F i ◆ a) : 
  a ◆ (big[(◆)/nil]_(i ∈ r | (P i)) F i) = (big[(◆)/nil]_(i ∈ r | (P i)) (F i)) ◆ a := 
begin
  induction r with h t IH,
  { rw [big.nil, left_id op, right_id op] },
  { rw big.cons,
    have : a ◆ ?(F h) = ?(F h) ◆ a,
    { by_cases H' : P h,
      { simp [H', H h (by simp)] },
      { simp [H', left_id op, right_id op] }},
    conv in (op _ a) { rw (assoc op) },
    rw [←IH, ←(assoc op), this, ←(assoc op)],
    intros i i_in_t,
    exact H _ (mem_cons_of_mem h i_in_t) }
end

lemma big.gather_of_commute (F G : ℕ → R) (k l : ℕ)
  (H : ∀ i j, i ≠ j → F i ◆ G j = G j ◆ F i) : 
  (big[(◆)/nil]_(i = k..(k+l)) F i) ◆ (big[(◆)/nil]_(i = k..(k+l)) G i) = 
  big[(◆)/nil]_(i = k..(k+l)) F i ◆ G i := 
begin
  induction l with l IH,
  { have : k + 1 - k = 1,
    rw [add_comm, nat.add_sub_cancel],
    simp [big.one_term, this] },
  { have obs : ∀ i, (i ∈ (range' k (l + 1))) → k + l + 1 ≠ i:=
      assume i h, ne_of_gt (mem_range'.1 h).2,
    
    have : ∀ j, k + j + 1 - k = j +1 :=
      λ j, calc 
        k + j + 1 - k = k + (j + 1) - k : rfl
                  ... = j+1 : by rw [add_comm, nat.add_sub_cancel],
    rw this at IH ⊢,
    rw [show range' k (nat.succ l + 1) = (range' k ( l + 1)) ++ [k+l+1],
        by simp [range'_concat]],
    repeat { rw [big.append, big.one_term] },
    
    conv { to_lhs, 
           rw assoc op,
           congr,
           skip,
           rw ← assoc op },
    rw [big.commute_through op, assoc op, ← assoc op, IH],
    intros i h,
    simpa using H (k+l+1) i (obs i h) }
end

lemma apply_ite {nil : R} {φ : R → R} (Hnil : φ nil = nil) (h : I) : 
  φ (ite (P h) (F h) nil) = ite (P h) (φ (F h)) nil :=
calc 
      φ (ite (P h) (F h) nil) = ite (P h) (φ $ F h) (φ nil) : by { by_cases H : P h; simp[H] }
      ... = ite (P h) (φ $ F h) nil : by rw Hnil

lemma big.mph {φ : R → R} 
  (Hop : ∀ a b : R, φ (a ◆ b) = φ a ◆ φ b) (Hnil : φ nil = nil) : 
  φ (big[(◆)/nil]_(i ∈ r | (P i)) F i) = big[(◆)/nil]_(i ∈ r | (P i)) φ (F i) := 
begin
  induction r with h t IH,
  { simp [big.nil, Hnil] },
  { rw [big.cons, Hop, IH, apply_ite _ _ Hnil, ←(big.cons op nil P _ t)] }
end

lemma big.anti_mph {φ : R → R} 
  (Hop : ∀ a b : R, φ (a ◆ b) = φ b ◆ φ a) (Hnil : φ nil = nil) :
  φ (big[(◆)/nil]_(i ∈ r | (P i)) F i) = big[(◆)/nil]_(i ∈ r.reverse | (P i)) φ (F i) := 
begin
  induction r with h t IH,
  { simp [big.nil, Hnil] },
  { rw [big.cons, Hop, apply_ite _ _ Hnil, reverse_cons', big.append, IH, big.one_term'] }
end
variables (a b : nat)


variables {α : Type*} {β : Type*}
theorem nth_map (f : α → β) : ∀ l n, nth (map f l) n = (nth l n).map f
| []       n     := rfl
| (a :: l) 0     := rfl
| (a :: l) (n+1) := nth_map l n

theorem nth_le_map (f : α → β) {l n} (H1 H2) : nth_le (map f l) n H1 = f (nth_le l n H2) :=
option.some.inj $ by rw [← nth_le_nth, nth_map, nth_le_nth]; refl

#check nth_le_reverse

#reduce let a:=5 in let b := 8 in map (λ i, 2 * a + (b + 1 - a) - i - 1) (range' a (b+1-a))
#reduce let a:=5 in let b := 8 in map (λ i, a + b - i) (range' a (b+1-a))

lemma reverse_range' (a b : ℕ) : reverse (range' a b) = map (λ i, 2*a+b-i-1) (range' a b) :=
begin
  sorry
end

lemma big.range_anti_mph {φ : R → R} (P : ℕ → Prop) [decidable_pred P] (F : ℕ → R) (a b : ℕ)
  (Hop : ∀ a b : R, φ (a ◆ b) = φ b ◆ φ a) (Hnil : φ nil = nil) :
  φ (big[(◆)/nil]_(i=a..b | (P i)) F i) = big[(◆)/nil]_(i=a..b | (P (a+b-i))) φ (F (a+b-i)) := 
begin
  by_cases H : b < a,
  { simp [big.empty_range, *] },
  { rw big.anti_mph op nil _ _ _ Hop Hnil,
    rw reverse_range',
    rw big.map op nil _ _ _,
    apply big.ext ; intros i i_in; have : 2 * a + (b + 1 - a) - i - 1 = a+b-i := 
    begin
      replace H : a ≤ b := le_of_not_gt H,
      exact calc 2 * a + (b + 1 - a) - i - 1 = a + (a + (b + 1 - a)) - i - 1 : by simp [two_mul]
        ... = a + (b + 1) - i - 1 : by rw nat.add_sub_of_le (le_trans H (nat.le_succ _))
        ... = (a + b) + 1 - (i + 1)  : by simp [add_assoc,nat.sub_sub]
        ... = a + b - i : by rw nat.add_sub_add_right,
    end; rw this }
end
end monoid
