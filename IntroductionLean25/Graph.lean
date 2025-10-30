set_option autoImplicit false

structure Graph (α : Type) where
  vertices : List α
  edge : α → α → Bool

variable {α : Type} [DecidableEq α]

def findNeighbor? (G : Graph α) (a : α) : Option α :=
  if a ∈ G.vertices
  then G.vertices.find? (fun x => G.edge a x)
  else none

theorem mem_findNeighbor? {G : Graph α} {a x : α} (h : findNeighbor? G a = some x) :
    x ∈ G.vertices := by
  simp [findNeighbor?, List.find?_eq_some_iff_getElem] at h
  rcases h with ⟨_, _, i, hi, h, _⟩
  rw [← h]
  simp

def isSink (a : α) (G : Graph α) : Prop := a ∈ G.vertices ∧ ∀ (x : α), x ∈ G.vertices → G.edge a x = false

theorem isSink_iff_findNeighbor?_eq_none (a : α) (G : Graph α): isSink a G ↔ a ∈ G.vertices ∧ findNeighbor? G a = none  := by
  simp [isSink, findNeighbor?]
  grind

def isWalk [DecidableEq α] (l : List α) (G : Graph α) : Prop :=
  (∀ (x : α), x ∈ l → x ∈ G.vertices) ∧ ∀ (i : Nat) (h : i + 1 < l.length), G.edge (l[i+1]'h) (l[i]'(by exact Nat.lt_of_succ_lt h))

theorem isWalk_singleton {x : α} {G : Graph α} (h : x ∈ G.vertices): isWalk [x] G := by
  unfold isWalk
  simp
  apply h

theorem head_of_walk_is_mem {l : List α} {G : Graph α} (h : l ≠ []) (h' : isWalk l G) :
    (l.head h) ∈ G.vertices := by
  have : l.head h ∈ l := by grind
  apply h'.1
  apply this

theorem isWalk_of_cons_findNeighbor_isWalk {x : α} {l : List α}
  {G : Graph α} (h₁ : l ≠ []) (h₂ : isWalk l G)
  (h₃ : findNeighbor? G (l.head h₁) = some x) :
    isWalk (x::l) G := by
  unfold isWalk
  constructor
  · intro a mem
    simp at mem
    cases mem with
    | inl h =>
      rw [h]
      apply mem_findNeighbor? h₃
    | inr h =>
      apply h₂.1 a h
  · intro i hi
    cases i with
    | zero =>
      simp
      unfold findNeighbor? at h₃
      simp [head_of_walk_is_mem h₁ h₂] at h₃
      rw [List.find?_eq_some_iff_getElem] at h₃
      rw [List.head_eq_getElem] at h₃
      apply h₃.left
    | succ m =>
      simp
      unfold isWalk at h₂
      rcases h₂ with ⟨_, h₂⟩
      simp at hi
      specialize h₂ m hi
      exact h₂

def isCycle (l : List α) (G : Graph α) : Prop :=
  isWalk l G ∧ ∀ (h : l ≠ []), l.head h = l.getLast h

def isAcyclic (G : Graph α) : Prop := ∀ (l : List α), ¬ isCycle l G

theorem length_le_length_of_subset_of_nodup {l l' : List α} (h : l ⊆ l') (h' : List.Nodup l) : l.length ≤ l'.length := by
  induction l generalizing l' with
  | nil => simp
  | cons hd tl ih =>
    simp
    simp at h
    simp at h'
    specialize @ih (l'.erase hd)
    have : tl ⊆ l'.erase hd := by
      intro a mem
      have : a ≠ hd := by
        intro ahd
        rw [ahd] at mem
        exact absurd mem h'.1
      rw [List.mem_erase_of_ne this]
      apply h.2 mem
    specialize ih this h'.2
    rw [List.length_erase, if_pos h.1] at ih
    apply Nat.le_trans (m := (l'.length - 1) + 1)
    · simp [ih]
    · grind

theorem length_walk_le_length_vertices_of_nodup {G : Graph α} {l : List α} (h : isWalk l G) (h₂ : List.Nodup l) :
    l.length ≤ G.vertices.length := by
  apply length_le_length_of_subset_of_nodup ?_ h₂
  unfold isWalk at h
  apply h.1

noncomputable def exploreGraph (G : Graph α) (l : List α) (h : isWalk l G) (h₂ : List.Nodup l) (h' : l ≠ []): Sum α (List α) :=
  let currVertex := l.head h'
  match h₄: findNeighbor? G currVertex with
  | some x =>
    if h₃ : x ∈ l
    then Sum.inr (x::l)
    else exploreGraph G (x::l) (isWalk_of_cons_findNeighbor_isWalk h' h (by simp [currVertex] at h₄; exact h₄)) (by simp[h₃, h₂]) (by simp)
  | none => Sum.inl currVertex
termination_by G.vertices.length - l.length
decreasing_by
  have h₁ : (x::l).length ≤ G.vertices.length :=  by
    apply length_walk_le_length_vertices_of_nodup
    · apply isWalk_of_cons_findNeighbor_isWalk h' h h₄
    · simp
      constructor
      · apply h₃
      · apply h₂
  have h₂ : l.length < G.vertices.length := by grind
  exact Nat.sub_succ_lt_self G.vertices.length l.length h₂

theorem isSink_of_exploreGraph_eq_node {G : Graph α} {x : α} {l : List α} (h : isWalk l G) (h₂ : List.Nodup l) (h' : l ≠ []) :
    exploreGraph G l h h₂ h' = Sum.inl x → isSink x G := by
  rw [isSink_iff_findNeighbor?_eq_none]
  induction hl: G.vertices.length - l.length generalizing l with
  | zero =>
    rw [Nat.sub_eq_zero_iff_le] at hl
    have := length_walk_le_length_vertices_of_nodup h h₂
    unfold exploreGraph
    simp
    split
    · rename_i y hy
      split
      · simp
      · rename_i hy'
        have walky := isWalk_of_cons_findNeighbor_isWalk _ h hy
        have walky_nodup : List.Nodup (y::l) := by grind
        have walky_length : (y::l).length ≤ G.vertices.length := by
          apply length_walk_le_length_vertices_of_nodup walky walky_nodup
        grind
    · intro hx
      have : x = l.head h' := by grind
      rw [this]
      constructor
      · apply head_of_walk_is_mem h' h
      · assumption
  | succ m ih =>
    unfold exploreGraph
    simp
    split
    · rename_i y hy
      split
      · simp
      · apply ih
        simp
        grind
    · intro hx
      have : x = l.head h' := by grind
      rw [this]
      constructor
      · apply head_of_walk_is_mem h' h
      · assumption

theorem every_graph_has_sink_or_cycle (G : Graph α) (h : ∃ (x : α), x ∈ G.vertices) :
    (∃ (v : α), isSink v G) ∨ ∃ (l : List α), isCycle l G := by
  rcases h with ⟨x, hx⟩
  cases h: exploreGraph G [x] (isWalk_singleton hx) (by simp) (by simp) with
  | inl v =>
    left
    exists v
    apply isSink_of_exploreGraph_eq_node (isWalk_singleton hx) (by simp) (by simp) h
  | inr l => sorry
