set_option autoImplicit false

structure Graph (α : Type) where
  vertices : List α
  edge : α → α → Bool

variable {α : Type} [DecidableEq α]

def isNeighbor (G : Graph α) (a b : α) : Prop := G.edge a b = true ∧ a ∈ G.vertices ∧ b ∈ G.vertices

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

theorem isNeighbor_of_findNeighbor_eq_some {G : Graph α} {a x : α} (h : findNeighbor? G a = some x) :
    isNeighbor G a x := by
  simp [findNeighbor?, List.find?_eq_some_iff_getElem] at h
  rcases h with ⟨ha, hax, i, hi, hx, _⟩
  simp [isNeighbor]
  grind

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

theorem isWalk_of_cons {hd : α} {tl : List α} {G : Graph α} (h : isWalk (hd::tl) G) :
    isWalk tl G := by
  simp [isWalk]
  constructor
  · intro x hx
    apply h.1
    simp
    right
    exact hx
  · intro i hi
    simp [isWalk] at h
    rcases h with ⟨_, h⟩
    specialize h (i+1) (by grind)
    apply h

theorem head_of_walk_is_mem {l : List α} {G : Graph α} (h : l ≠ []) (h' : isWalk l G) :
    (l.head h) ∈ G.vertices := by
  have : l.head h ∈ l := by grind
  apply h'.1
  apply this

theorem isWalk_of_cons_isNeighbor_isWalk {x : α} {l : List α}
  {G : Graph α} (h₁ : l ≠ []) (h₂ : isWalk l G)
  (h₃ : isNeighbor G (l.head h₁) x) :
    isWalk (x::l) G := by
  unfold isWalk
  constructor
  · intro a mem
    simp at mem
    cases mem with
    | inl h =>
      rw [h]
      simp [isNeighbor] at h₃
      apply h₃.2.2
    | inr h =>
      apply h₂.1 a h
  · intro i hi
    cases i with
    | zero =>
      simp
      rw [List.head_eq_getElem] at h₃
      apply h₃.left
    | succ m =>
      simp
      unfold isWalk at h₂
      rcases h₂ with ⟨_, h₂⟩
      simp at hi
      specialize h₂ m hi
      exact h₂

theorem isWalk_of_cons_findNeighbor_isWalk {x : α} {l : List α}
  {G : Graph α} (h₁ : l ≠ []) (h₂ : isWalk l G)
  (h₃ : findNeighbor? G (l.head h₁) = some x) :
    isWalk (x::l) G := by
  apply isWalk_of_cons_isNeighbor_isWalk h₁ h₂
  apply isNeighbor_of_findNeighbor_eq_some h₃

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

noncomputable def exploreGraph (G : Graph α) (l : List α) (h : isWalk l G) (h₂ : List.Nodup l) (h' : l ≠ []): Sum α (α ×List α) :=
  let currVertex := l.head h'
  match h₄: findNeighbor? G currVertex with
  | some x =>
    if h₃ : x ∈ l
    then Sum.inr ⟨x,l⟩
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

theorem exploreGraph_pair {G : Graph α} {x : α} {l l': List α} (h : isWalk l G) (h₂ : List.Nodup l) (h' : l ≠ []) :
    exploreGraph G l h h₂ h' = .inr (x, l') → l' ≠ [] ∧ isWalk (x :: l') G ∧ x ∈ l' := by
  induction hl: G.vertices.length - l.length generalizing l with
  | zero =>
    rw [Nat.sub_eq_zero_iff_le] at hl
    have := length_walk_le_length_vertices_of_nodup h h₂
    unfold exploreGraph
    simp
    split
    · rename_i y hy
      split
      · rename_i mem
        intro h₄
        injections
        rename_i h₅ h₆
        rw [← h₅, ← h₆]
        constructor
        · apply h'
        · constructor
          · apply isWalk_of_cons_findNeighbor_isWalk h' h hy
          · apply mem
      · rename_i hy'
        have walky := isWalk_of_cons_findNeighbor_isWalk _ h hy
        have walky_nodup : List.Nodup (y::l) := by grind
        have walky_length : (y::l).length ≤ G.vertices.length := by
          apply length_walk_le_length_vertices_of_nodup walky walky_nodup
        grind
    · simp
  | succ m ih =>
    unfold exploreGraph
    simp
    split
    · rename_i y hy
      split
      · rename_i mem
        intro h₄
        injections
        rename_i h₅ h₆
        rw [← h₅, ← h₆]
        constructor
        · apply h'
        · constructor
          · apply isWalk_of_cons_findNeighbor_isWalk h' h hy
          · apply mem
      · apply ih
        simp
        grind
    · simp

def takeUntil (x : α) (l : List α) (hx : x ∈ l) : List α :=
  match l with
  | .nil => by simp at hx
  | .cons hd tl =>
    if h: x = hd
    then [hd]
    else hd::(takeUntil x tl (by grind))

theorem takeUntil_not_empty {x : α} {l : List α} (hx : x ∈ l) : takeUntil x l hx ≠ [] := by
  cases l with
  | nil => simp at hx
  | cons hd tl =>
    simp [takeUntil]
    split
    · simp
    · simp

theorem takeUntil_head_eq_head {x : α} {l : List α} (hx : x ∈ l) :
    l.head (by grind) = (takeUntil x l hx).head (takeUntil_not_empty hx) := by
  cases l with
  | nil => simp at hx
  | cons hd tl =>
    simp [takeUntil]
    split
    · simp
    · simp

theorem getLast_takeUntil {x : α} {l : List α} (hx : x ∈ l) :
    (takeUntil x l hx).getLast (takeUntil_not_empty hx) = x := by
  induction l with
  | nil => simp at hx
  | cons hd tl ih =>
    simp [takeUntil]
    by_cases h: x = hd
    · simp [h]
    · simp [h] at hx
      simp [h,List.getLast_cons (takeUntil_not_empty hx)]
      apply ih

theorem isWalk_takeUntil_of_isWalk  {x : α} {G : Graph α} {l : List α} (hx : x ∈ l) (h : isWalk l G) :
    isWalk (takeUntil x l hx) G := by
  induction l with
  | nil => simp at hx
  | cons hd tl ih =>
    simp [takeUntil]
    by_cases h' : x = hd
    · simp [h']
      apply isWalk_singleton
      apply h.1
      simp
    · simp [h'] at hx

      simp [h']
      apply isWalk_of_cons_isNeighbor_isWalk
      · apply ih
        apply isWalk_of_cons h
      · rw [← takeUntil_head_eq_head hx]
        simp [isNeighbor]
        simp [isWalk] at h
        rcases h with ⟨h₁,h₂⟩
        constructor
        · specialize h₂ 0 (by grind)
          simp at h₂
          rw [List.head_eq_getElem]
          apply h₂
        · constructor
          · apply h₁.2
            simp
          · apply h₁.1

theorem every_graph_has_sink_or_cycle (G : Graph α) (h : ∃ (x : α), x ∈ G.vertices) :
    (∃ (v : α), isSink v G) ∨ ∃ (l : List α), isCycle l G := by
  rcases h with ⟨x, hx⟩
  cases h: exploreGraph G [x] (isWalk_singleton hx) (by simp) (by simp) with
  | inl v =>
    left
    exists v
    apply isSink_of_exploreGraph_eq_node (isWalk_singleton hx) (by simp) (by simp) h
  | inr y =>
    cases y with
    | mk v l =>
      have := exploreGraph_pair (isWalk_singleton hx) (by simp) (by simp) h
      rcases this with ⟨h₁, h₂, h₃⟩
      right
      exists (v :: takeUntil v l h₃)
      simp [isCycle]
      constructor
      · apply isWalk_of_cons_isNeighbor_isWalk (takeUntil_not_empty h₃)
        · apply isWalk_takeUntil_of_isWalk h₃ (isWalk_of_cons h₂)
        · rw [← takeUntil_head_eq_head]
          simp [isNeighbor]
          simp [isWalk] at h₂
          constructor
          · have := h₂.2 0 (by grind)
            rw [List.head_eq_getElem]
            apply this
          · constructor
            · rw [List.head_eq_getElem]
              apply h₂.1.2 (l[0]'(by grind)) (by grind)
            · apply h₂.1.1
      · intro _
        rw [List.getLast_cons (takeUntil_not_empty h₃)]
        rw [getLast_takeUntil]
