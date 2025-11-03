#check 1
#check "123"
#check true
#check [1,2,3]

#eval 2-5
#eval (2 : Int) - 5
#eval 2 - (5 : Int)

#check Nat
#check Type
#check Type 1

inductive Color
| Red
| Blue
| Green

#check Color.Green
#check Color

def isRed (c : Color) : Bool :=
  match c with
  | .Red => true
  | .Blue => false
  | .Green => false

#eval isRed Color.Red

def isGreen (c : Color) : Bool :=
  match c with
  | .Green => true
  | _ => false

def isBlue (c : Color) : Bool :=
  ! isRed c && ! isGreen c

#check True ∨ False
#check 2 = 5
#check (2 == 5) = true
#check (2 = 2) ∨ (2 = 5)

theorem test1 : True ∨ False := by
  left
  apply True.intro

theorem test2 (c : Color) (h : c ≠ Color.Red) (h₂ : c ≠ Color.Blue) : c = Color.Green := by
  cases c with
  | Green => rfl
  | Blue => simp at h₂
  | Red => simp at h

#check Or.inl (b:= False) True.intro

theorem test3 : 2 = 5 := by
  sorry

#print axioms test1
#print axioms test3
#print axioms test2
#check propext

theorem test4 : ∀ (x : Nat), x = x := by
  intro x
  rfl

theorem test5 : ∀ (s : String), s = s := by
  intro s
  rfl

theorem test6 (p : Prop) : p → p := by
  intro abc
  apply abc

theorem test7 (p q : Prop) : (p ∧ q) → p := by
  intro hpq
  rcases hpq with ⟨hp, hq⟩
  apply hp

theorem test8 (p q r : Prop) (h : p ∨ q) (g : p → r) (f : q → r) : r := by
  cases h with
  | inl h₁ =>
    apply g
    apply h₁
  | inr h₂ =>
    apply f h₂

theorem axiomHK1 (p q : Prop) : p → (q → p) := by
  intro hp
  intro hq
  apply hp

theorem axiomHK1' (p q : Prop) (hp : p) : q → p := by
  intro hq
  apply hp

theorem axiomsHK'' : ∀ (p q : Prop), p → (q → p) := by
  intro p
  intro q hp hq
  apply hp

theorem test9 (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · apply hp
  · apply hq

theorem test10 : 2 * 5 = 10 := by rfl

class Group (α : Type) where
  mul : α → α → α
  unit : α
  inv : α → α
  mul_unit : ∀ (a : α), mul a unit = a
  unit_mul : ∀ (a : α), mul unit a = a
  inv_mul : ∀ (a : α), mul (inv a) a = unit
  mul_inv : ∀ (a : α), mul a (inv a) = unit
  assoc : ∀ (a b c : α), mul a (mul b c) = mul (mul a b) c

instance : Group Int where
  mul := fun x y => x + y
  unit := 0
  inv := fun x => - x
  mul_unit := by simp
  unit_mul := by simp
  inv_mul := by grind
  mul_inv := by grind
  assoc := by grind

theorem test11 {α : Type} (h : Group α) (x : α) :
    h.mul (h.mul x (h.inv x)) (h.mul (h.inv x) x) = h.unit := by
  rw [h.mul_inv]
  rw [h.inv_mul]
  rw [h.mul_unit]

inductive MyList (α : Type)
| nil
| cons : α → MyList α → MyList α

--[1,2]
#check MyList.cons 1 (MyList.cons 2 (MyList.nil))

def map {α β : Type} (f : α → β) (l : MyList α) : MyList β :=
  match l with
  | .nil => .nil
  | .cons hd tl => .cons (f hd) (map f tl)

theorem map_map {α β γ : Type} (f : α → β) (g : β → γ) (l : MyList α) :
    map g (map f l) = map (fun x => g (f x)) l := by
  induction l with
  | nil =>
    simp [map]
  | cons hd tl ih =>
    simp [map]
    apply ih
