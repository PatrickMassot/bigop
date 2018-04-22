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


/- First lemmas, without assuming anything on `op` and `nil` -/

lemma big_cons_true {h} (t) (Ph : P h) : 
  (big[op/nil]_(i ∈ h::t | (P i)) (F i)) = F h ◆ (big[op/nil]_(i ∈ t | (P i)) (F i)):=
by simp [apply_bigop, Ph]

lemma big_cons_false {h} (t) (Ph : ¬ P h) :
  (big[op/nil]_(i ∈ h::t | (P i)) (F i)) = (big[op/nil]_(i ∈ t | (P i)) (F i)) :=
by simp [apply_bigop, Ph]

/- Now we go towards assuming (R, op, nil) is a monoid -/

/- We use the new algebraic hierarchy for more fine grained control.
   Some lemmas are missing? -/
lemma op_assoc [is_associative R op] : ∀ a b c, (a ◆ b) ◆ c = a ◆ (b ◆ c) :=
is_associative.assoc op

lemma op_left_id {nil} [is_left_id R op nil] : ∀ a, op nil a = a :=
is_left_id.left_id op

/- Assuming only that nil is left neutral for op -/

local notation `?(F` h`)` := if P h then F h else nil

lemma big_cons [is_left_id R op nil] {h} (t) : 
  (big[op/nil]_(i ∈ h::t | (P i)) (F i)) = ?(F h) ◆ (big[op/nil]_(i ∈ t | (P i)) (F i)):=
begin
  by_cases H : P h,
  { simp [H, big_cons_true] },
  { simp [H, big_cons_false, op_left_id op] }
end

/- Also need to make sure old hierarchy talks to new one.
   Associativity seems ok but we need: -/
instance add_monoid_is_left_id (α : Type*) [add_monoid α] : is_left_id α (+) 0 := ⟨by simp⟩


lemma big_nil [is_left_id R op nil] : (big[op/nil]_(i ∈ [] | (P i)) (F i)) = nil :=
by simp [apply_bigop]

lemma big_append [is_associative R op] [is_left_id R op nil] (r₁ r₂ : list I) : 
  (big[op/nil]_(i ∈ r₁++r₂ | (P i)) (F i)) = 
  (big[op/nil]_(i ∈ r₁ | (P i)) (F i)) ◆ (big[op/nil]_(i ∈ r₂ | (P i)) (F i)) :=
begin
  let Op := λ l, big[op/nil]_(i ∈ l | (P i)) (F i),
  induction r₁ with h t IH,
  { exact (eq.symm $ calc
    Op [] ◆ Op r₂ =  nil ◆ (big[op/nil]_(i ∈ r₂ | P i)F i) : by {dsimp [Op], rw big_nil}
    ... = _ : op_left_id _ _ )},
  { have : ?(F h) ◆ Op t = Op (h :: t) :=
    eq.symm (big_cons _ _ _ _ _),
    exact calc
    Op (h :: t ++ r₂) 
        = Op (h :: (t ++ r₂))      : rfl
    ... = ?(F h) ◆ Op (t ++ r₂)    : big_cons _ _ _ _ _
    ... = ?(F h) ◆ (Op t ◆ Op r₂)  : by simp [Op, IH]
    ... = (?(F h) ◆ Op t) ◆ Op r₂  : eq.symm $ op_assoc _ _ _ _
    ... = Op (h::t) ◆ Op r₂        : by rw this }
end

/- Sample specialization -/
lemma sum_append (r₁ r₂ : list I) (F : I → ℕ) :
  (Σ_(i ∈ r₁ ++ r₂ | P i) F i) =  (Σ_(i ∈ r₁ | P i) F i) + Σ_(i ∈ r₂ | P i) F i :=
by apply big_append