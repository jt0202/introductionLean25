set_option autoImplicit false

structure Graph (α : Type) where
  vertices : List α
  edge : α → α → Bool

variable {α : Type}

def findNeighbor? (G : Graph α) (a : α) : Option α :=
  G.vertices.find? (fun x => G.edge a x)

def isSink (a : α) (G : Graph α) : Prop := ∀ (x : α), x ∈ G.vertices → G.edge a x = false

theorem isSink_iff_findNeighbor?_eq_none (a : α) (G : Graph α): isSink a G ↔ findNeighbor? G a = none := by
  simp [isSink, findNeighbor?]

def isWalk (l : List α) (G : Graph α) : Prop :=
  ∀ (i : Nat) (h : i + 1 < l.length), G.edge (l[i+1]'h) (l[i]'(by exact Nat.lt_of_succ_lt h))

theorem isWalk_of_cons_findNeighbor_isWalk {x : α} {l : List α}
  {G : Graph α} (h₁ : l ≠ []) (h₂ : isWalk l G)
  (h₃ : findNeighbor? G (l.head h₁) = some x) :
    isWalk (x::l) G := by
  unfold isWalk
  intro i hi
  cases i with
  | zero =>
    simp
    unfold findNeighbor? at h₃
    rw [List.find?_eq_some_iff_getElem] at h₃
    rw [List.head_eq_getElem] at h₃
    apply h₃.left
  | succ m =>
    simp
    unfold isWalk at h₂
    simp at hi
    specialize h₂ m hi
    exact h₂

def isCycle (l : List α) (G : Graph α) : Prop :=
  isWalk l G ∧ ∀ (h : l ≠ []), l.head h = l.getLast h

def isAcyclic (G : Graph α) : Prop := ∀ (l : List α), ¬ isCycle l G

open Classical in
def exploreGraph (G : Graph α) (l : List α) (h : isWalk l G) (h' : l ≠ []): Sum α (List α) :=
  let currVertex := l.head h'

  match h₂: findNeighbor? G currVertex with
  | some x =>
    if h₃ : x ∈ l
    then Sum.inr (x::l)
    else exploreGraph G (x::l) (isWalk_of_cons_findNeighbor_isWalk h' h (by simp [currVertex] at h₂; exact h₂)) (by simp)
  | none => Sum.inl currVertex
termination_by G.vertices.length - l.length
decreasing_by
  have h₁ : (x::l).length ≤ G.vertices.length := by sorry
  have h₂ : l.length < G.vertices.length := by grind
  exact Nat.sub_succ_lt_self G.vertices.length l.length h₂

theorem every_graph_has_sink_or_cycle (G : Graph α) (h : ∃ (x : α), x ∈ G.vertices) :
    (∃ (v : α), v ∈ G.vertices ∧ isSink v G) ∨ ∃ (l : List α), isCycle l G := by
  rcases h with ⟨x, hx⟩
  cases h: exploreGraph G [x] (by sorry) (by simp) with
  | inl v =>
    unfold exploreGraph at h
    simp at h
    cases findNeighbor? G x with
    | some v' =>
      sorry
  | inr l => sorry
