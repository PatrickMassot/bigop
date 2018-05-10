import data.list.basic

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
apply_bigop op nil (range' a (b-a+1)) P F

notation `Σ_(`:0 binder`=`a`..`b `|` P:(scoped p, p)`)` F:(scoped f, f) := 
apply_bigop (+) 0 (range' a (b-a+1)) P F

notation `Π_(`:0 binder`=`a`..` b `|` P:(scoped p, p)`)` F:(scoped f, f) := 
apply_bigop (*) 1 (range' a (b-a+1)) P F


/- variable is natural numbers from a to b -/

notation `big[`:0 op `/`:0 nil `]_(`:0 binder `=` a `..` b `)` F:(scoped f, f) := 
apply_bigop op nil (range' a (b-a+1)) (λ i, true) F

notation `Σ_(`:0 binder `=` a `..` b `)` F:(scoped f, f) := 
apply_bigop (+) 0 (range' a (b-a+1)) (λ i, true) F

notation `Π_(`:0 binder `=` a `..` b `)` F:(scoped f, f) := 
apply_bigop (*) 1 (range' a (b-a+1)) (λ i, true) F

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

lemma range'_add_map (a b k : ℕ) : range' (a+k) b = map (λ x, x + k) (range' a b) :=
begin
  revert a,
  induction b with b IH; intro a,
  { refl },
  { simpa using (IH $ a + 1) }
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

lemma big.shift (P : ℕ → Prop) [decidable_pred P] (F : ℕ → R) (a b k : ℕ) : 
  (big[(◆)/nil]_(i=a..b | (P i)) (F i)) = (big[(◆)/nil]_(i=(a+k)..(b+k) | (P (i-k))) (F (i-k))) :=
begin
  rw [range'_add_map, big.map],
  congr_n 1 ; funext ; simp only [nat.add_sub_cancel, nat.add_sub_add_right]
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
  { simp [big.one_term, nat.sub_self] },
  { have obs : ∀ i, (i ∈ (range' k (l + 1))) → k + l + 1 ≠ i:=
      assume i h, ne_of_gt (mem_range'.1 h).2,
    
    have : ∀ j, k + j - k + 1 = j + 1 :=
      λ j, by conv in  (_ - _) {rw [add_comm, nat.add_sub_cancel]},
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
end monoid
