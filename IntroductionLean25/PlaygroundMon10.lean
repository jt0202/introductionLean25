#check 1
#check "123"
#check true

#eval 1+2
#eval 3-5
#eval (3 : Int) - 5

#check Nat
#check String
#check Type
#check Type 1

inductive Color
| Red
| Green
| Blue

#check Color
#check Color.Red

def isRed (c : Color) : Bool :=
  match c with
  | .Red => true
  | .Blue => false
  | .Green => false

def isGreen (c : Color) : Bool :=
  match c with
  | .Red => false
  | .Blue => false
  | .Green => true

def isBlue (c : Color) : Bool := ! isRed c && ! isGreen c

#eval isBlue Color.Blue
#eval isBlue Color.Green

#check 2=2
#check 2=5
#check True ∨ False

theorem test1 : True ∨ False := by
  left
  apply True.intro

#check Or.inl (b:= False) True.intro

theorem test2 : 2 = 5 := by
  sorry

#print axioms test2
#print axioms test1
-- Erlaubt Classical.choice, propext, Quot.sound

#check Quot.sound

theorem test3 (p : Prop) : p → p := by
  intro hp
  apply hp

theorem test4 (p q : Prop) : p → (q → p) := by
  intro hp
  intro hq
  apply hp

theorem test4' (p q : Prop) (hp : p) : q → p := by
  intro hq
  apply hp

theorem test4'' : ∀ (p q : Prop), p → q → p := by
  intro p
  intro q
  apply test4

theorem test5 (p r : Prop) (hrp : r → p) (hr : r) : p := by
  apply hrp
  apply hr

theorem test6 (p q r : Prop) (hpq : p ∨ q) (hpr : p → r)
    (hqr : q → r) : r := by
  cases hpq with
  | inl hp =>
    apply hpr
    apply hp
  | inr hq =>
    apply hqr hq

theorem test7 (p q r : Prop) (hpq : p ∧ q ∧ r) : p := by
  rcases hpq with ⟨hp, hq, hr⟩
  apply hp

theorem test8 (p : Prop) : p ∨ ¬ p := by
  by_cases hp : p
  · left
    apply hp
  · right
    apply hp

#print axioms test8
-- comment
theorem test9 (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · apply hp
  · apply hq

theorem test10 (p q : Prop) (hpq : p → q) (hnq : ¬ q) : ¬ p := by
  by_cases hp : p
  · have hq : q := by
      apply hpq
      apply hp
    apply absurd hq hnq
  · apply hp

theorem test10' (p q : Prop) (hpq : p → q) (hnq : ¬ q) : ¬ p := by
  -- ¬ p = p → False
  intro hp
  apply hnq
  apply hpq
  apply hp

theorem test11 : 2 = 2 := by
  rfl

theorem test12 : 2 * 4 = 8 := by
  rfl

class Group (α : Type) where
  mul : α → α → α
  unit : α
  inv : α → α
  mul_unit : ∀ (a : α), mul a unit = a
  unit_mul : ∀ (a : α), mul unit a = a
  inv_mul : ∀ (a : α), mul (inv a) a = unit
  mul_inv : ∀ (a : α), mul a (inv a) = unit

theorem test13 (α : Type) (h : Group α) (x : α) :
    h.mul (h.mul x (h.inv x)) (h.mul (h.inv x) x) = h.unit := by
  rw [h.mul_inv]
  rw [h.inv_mul]
  rw [h.mul_unit]

inductive MyList (α : Type)
| nil : MyList α
| cons : α → MyList α → MyList α

--[1,2]
#check (MyList.cons 1 (MyList.cons 2 MyList.nil))

def map (α β : Type) (f : α → β) (l : MyList α) : MyList β :=
  match l with
  | .nil => .nil
  | .cons hd tl => .cons (f hd) (map α β f tl)

theorem test14 (α β : Type) (f : α → β) (l : MyList α) (h : l ≠ MyList.nil) : (map α β f l) ≠ MyList.nil := by
  cases l with
  | nil => simp at h
  | cons hd tl =>
    unfold map
    simp

def length (α : Type) (l : MyList α) : Nat :=
  match l with
  | .nil => 0
  | .cons hd tl => 1 + length α tl

theorem test15 (α β : Type) (f : α → β) (l : MyList α) : length β (map α β f l) = length α l := by
  induction l with
  | nil =>
    unfold map
    unfold length
    rfl
  | cons hd tl ih =>
    unfold map
    unfold length
    rw [ih]
