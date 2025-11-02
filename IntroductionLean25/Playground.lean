-- Jedes Element hat einen Typ in Lean

#check 1
#check true
#check [1,2,3,4]

-- Manchmal müssen wir dem Typ nachhelfen für Listen mit mehreren Typen
#check ([.inl 1, .inr "1"] : List (Sum Nat String))
-- oder um eine Zahl als Int zu haben
#check (1: Int)

#eval 2- 5
#eval (2: Int) -5

-- Welchen Typ hat Typ?
#check Type
#check Type 1
#check Type 2
-- Es ergibt sich eine unendliche Typenhierarchie. Type kann nicht in
-- Type sein, da es sonst ein Russel-Paradox gibt.

-- Ein spezieller Typ heißt Prop
#check True ∨ False
#check 2 = 5

-- Terme des Typen Prop sind Beweise

theorem test : True ∨ False := by
  left
  apply True.intro

#check Or.inl (b:= False) True.intro

-- Sorry beweist jedes Theorem, aber ist ein zusätzliches Axiom
theorem test2 : 2 = 5 := by sorry

#print axioms test
#print axioms test2
-- Bei print axioms sollte maximal funext, Classical.choice und
-- Quot.sound stehen. Ist dort mehr, dann gibt es unbewiesene Annahmen.

-- Gleiche Sachen sind gleich. Zeige dies mit der Reflexivität (rfl)

-- Sei α ein beliebiger Typ und x ein Element davon. Dann ist x gleich sich selbst.
theorem test3 {α : Type} (x : α) : x = x := by rfl

-- rfl kann auch Funktionen ausführen

theorem test4 : 2* 4 = 8 := by rfl

class Group (α : Type) where
  mul : α → α → α
  unit : α
  inv : α → α
  mul_unit : ∀ (a : α), mul a unit = a
  unit_mul : ∀ (a : α), mul unit a = a
  inv_mul : ∀ (a : α), mul (inv a) a = unit
  mul_inv : ∀ (a : α), mul a (inv a) = unit

-- rfl klappt nicht für beliebige Gruppen sondern nur für konkrete Implementierungen. Hier können wir rw verwenden. rw nimmt eine Gleichung
-- und ersetzt alle linken Seite im Ziel durch die rechte Seite der Gleichung
theorem test5 {α : Type} (h : Group α) (x : α) :
    h.mul (h.mul x (h.inv x)) (h.mul x (h.inv x)) = h.unit := by
  rw [h.mul_inv]
  rw [h.mul_unit]


-- Die Addition auf ganzen Zahlen ist eine Gruppe. Simp und grind sind wichtige Automatisierungstools. Simp versucht eine Normalform herzustellen und grind nutzt Gleichungen um systematisch Äquivalenzklassen aufzustellen.
-- Beide funktionieren, da viele Theoreme der Bibliotheken mittels tags
-- als geeignet für diese Klassen markiert wurden.
instance : Group Int where
  mul := fun x y => x + y
  unit := 0
  inv := fun x => - x
  mul_unit := by simp
  unit_mul := by simp
  inv_mul := by grind
  mul_inv := by grind

theorem test6 (p q r : Prop) (h : p ↔ q) (h' : q ↔ r) : p ↔ r := by
  rw [h]
  rw [h']

-- Falls das Ziel schon eine Annahme ist, können wir apply verwenden.
theorem test6' (p q r : Prop) (h : p ↔ q) (h' : q ↔ r) : p ↔ r := by
  rw [h]
  apply h'

theorem test7 (p q : Prop) (h : p) (h' : p → q) : q := by
  apply h'
  apply h

-- Wir können auch schon die Vorraussetzungen der Implikation mitgeben.
theorem test7' (p q : Prop) (h : p) (h' : p → q) : q := by
  apply h' h

-- Sind Annahmen oder Hypothesen im Ziel, können wir diese mittel intro heraus bewegen
theorem test11 (p q: Prop) (h : p) : q → p := by
  intro hq
  apply h
-- Exercise
theorem ex1 {p q : Prop} : p → (q → p) := by
  sorry

-- Mittels exists geben wir Zeugen wir Existenzquantoren
theorem test12 : ∃ (x : Nat), x ≥ 13 := by
  exists 14

-- Mit Rcases kann man Hypthosen aufteilen. Das selbe geht auch mit Cases, aber dann hat nicht jeder einen Namen bzw. es ist nicht rekursiv
theorem test8 (p q r: Prop) (h : p ∧ q ∧ r) : p := by
  -- apply h fails
  rcases h with ⟨hp, hq, hr⟩
  apply hp

-- Constructor macht das selbe im Ziel
theorem test9 (p q : Prop) (h : p) (h' : q) : p ∧ q := by
  constructor
  · apply h
  · apply h'

theorem test10 (p q r : Prop) (h : p ∨ q) (h' : p → r) (h₂ : q → r) : r := by
  -- Teilen wir ein oder auf, gibt es mehrere Fälle
  cases h with
  | inl h =>
    apply h' h
  | inr h =>
    apply h₂ h

theorem test13 : 4 < 10 ∨ 10 ≤ 4 := by
  left
  simp

inductive MyList (α : Type)
| nil : MyList α
| cons : α → MyList α → MyList α

-- Es muss immer ein Element zurückgegeben werden. Daher verwenden wir
-- den Optiontype
def getHead? {α : Type} : MyList α → Option α
| .nil => none
| .cons hd _ => some hd

-- Eine Funktion kann auch Beweise entgegen nehmen.
def getHead {α : Type} (l : MyList α) (hl : l ≠ MyList.nil) : α :=
  match l with
  | .nil =>
    -- Dieser Fall kann nicht auftreten
    by simp at hl
  | .cons hd _ => hd

def map {α β: Type} (l : MyList α) (f : α → β) : MyList β :=
  match l with
  | .nil => MyList.nil
  | .cons hd tl => .cons (f hd) (map tl f)

-- Cases können wir auch für induktive Definitionen benutzen
-- simp vereinfacht es danach
theorem map_getHead {α β : Type} (f : α → β) (l : MyList α) (hl : l ≠ MyList.nil):
    some (f (getHead l hl)) = getHead? (map l f) := by
  cases l with
  | nil => simp at hl
  | cons hd tl =>
    unfold getHead
    unfold map
    unfold getHead?
    simp

-- Exercise
theorem map_not_empty {α β : Type} (f : α → β) (l : MyList α) (hl : l ≠ MyList.nil) :
    map l f ≠ MyList.nil := by
  sorry

-- Manchmal braucht man mehr als eine Fallunterscheidung. Nutze dann
-- induction
theorem map_map {α β γ : Type} (f : α → β) (g : β → γ) (l : MyList α) :
    map (map l f) g = map l (fun x => g (f x)) := by
  induction l with
  | nil => simp [map]
  | cons hd tl ih =>
    simp [map]
    rw [ih]

-- Exercise
def length {α : Type} (l : MyList α) : Nat := sorry

theorem length_map {α β : Type} (f : α → β) (l : MyList α) :
    length (map l f) = length l := by
  sorry
