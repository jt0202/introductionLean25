set_option autoImplicit false
set_option linter.unusedSectionVars false

/-
  Ein Graph ist eine Liste von Knoten eines Typs und eine Funktion, die für zwei Elemente sagt, ob es eine Kanten dazwischen gibt. Tatsächlich wollen wir Kanten nur zwischen Knoten, aber es ist einfacher die Definition möglichst allgemein zu halten und später in den Anwendungen sinnlose Fälle auszuschließen.
-/
structure Graph (α : Type) where
  vertices : List α
  edge : α → α → Bool

variable {α : Type} [DecidableEq α]

/-
  b ist ein Nachbar von a in G, wenn es eine Kante zwischen a und b gibt und sowohl a als auch b in dem Graphen sind.
-/
def isNeighbor (G : Graph α) (a b : α) : Prop := G.edge a b = true ∧ a ∈ G.vertices ∧ b ∈ G.vertices

/-
  Diese Funktion sucht einen Nachbarn für einen gegebenen Knoten in einen Graphen. Da nicht
  jeder Knoten einen Nachbarn hat, müssen wir allerdings eine Option zurückgeben.
-/
def findNeighbor? (G : Graph α) (a : α) : Option α :=
  if a ∈ G.vertices
  then G.vertices.find? (fun x => G.edge a x)
  else none

/-
  Wenn findNeighbor? für einen Graphen G und ein Element a ein Element x findet, dann ist
  x tatsächlich ein Nachbar von a in G
-/
theorem isNeighbor_of_findNeighbor_eq_some {G : Graph α} {a x : α} (h : findNeighbor? G a = some x) :
    isNeighbor G a x := by
  -- Ersetzte findNeigbor im Beweis, dass findNeighbor x liefert durch seine Definition.
  unfold findNeighbor? at h
  -- Vereinfache den Ausdruck, da nur der erste Fall eintreten darf, da nicht none
  -- zurückgegeben wird
  simp at h
  -- Verwenden einen Satz aus der Bibiliothek, der besagt, dass find? ein Element x zurückgibt
  -- genau dann wenn es eine Kante von a nach x gibt, x an einem zulässigen (h) Index i
  -- steht und es keinen früheren Index j gibt, der das erfüllt.
  rw [List.find?_eq_some_iff_getElem] at h
  -- Ersetze die Annahme h durch einzelne Annahmen, die durch das Aufspalten von Unds
  -- und die Gewinnung von Zeugen von existentiellen Aussagen bestehen.
  rcases h with ⟨ha, hax, i, hi, hx, _⟩
  -- Ersetze isNeighbor durch seine Definition
  unfold isNeighbor
  -- Das Ziel besteht nun aus mehreren Termen, die mit einem und verknüpft sind.
  --Zeige diese Ziele separat
  constructor
  · -- Nach Annahme gibt es eine Kante zwischen a und x
    apply hax
  · constructor
    · -- Nach Annahme ist a ein Knoten in G, da sonst findNeighbor none zurück gibt
      apply ha
    · -- Ersetze x durch G.vertices[i], da i der Index von x in G.vertices ist.
      -- Da diese Gleichung falsch herum steht, verwenden wir ← um die Richtung zu
      -- ändern
      rw [← hx]
      -- Ein Theorem der Bibliothek sagt uns, dass l[i] ∈ l für alle l ist.
      simp

/-
  Wenn findNeighbor etwas zurück gibt, dann ist es ein Knoten
-/
theorem mem_findNeighbor? {G : Graph α} {a x : α} (h : findNeighbor? G a = some x) :
    x ∈ G.vertices := by
  -- Nach dem vorherigen Lemma gibt es einen Nachbarn von a zurück
  have := isNeighbor_of_findNeighbor_eq_some h
  unfold isNeighbor at this
  -- Nutze die Aussage nach Annahme
  apply this.2.2

/-
  Wenn ein Element ein Nachbar eines anderen Elementes ist, ist es ein Knoten.
-/
theorem mem_isNeighbor {G : Graph α} {a x : α} (h : isNeighbor G a x) :
    x ∈ G.vertices := h.2.2

/-
  Eine Senke ist ein Knoten in einem Graphen, der zu keinem anderen Knoten einen Nachfolger hat.
-/
def isSink (a : α) (G : Graph α) : Prop := a ∈ G.vertices ∧ ∀ (x : α), x ∈ G.vertices → G.edge a x = false

/-
  a ist eine Senke in G gdw. a ein Knoten von G ist und findNeighbor keinen Nachbarn liefert
-/
theorem isSink_iff_findNeighbor?_eq_none (a : α) (G : Graph α): isSink a G ↔ a ∈ G.vertices ∧ findNeighbor? G a = none  := by
  -- Ersetze isSink und findNeighbor und verwende gängige Vereinfachungsregelungen
  simp [isSink, findNeighbor?]
  -- Grind ist eine Taktik zur Beweisautomatisierungen, da wir die Tautologie p → (p ∨ q) haben.
  grind

/-
  Ein Walk ist eine Liste von Knoten, sodass benachbarte Posiitonen der Liste Nachbarn im Graph sind.
-/
def isWalk [DecidableEq α] (l : List α) (G : Graph α) : Prop :=
  (∀ (x : α), x ∈ l → x ∈ G.vertices) ∧ ∀ (i : Nat) (h : i + 1 < l.length), G.edge (l[i+1]'h) (l[i]'(by exact Nat.lt_of_succ_lt h))

/-
  Jede einelementige Liste, die einen Knoten von G enthält ist ein Walk.
-/
theorem isWalk_singleton {x : α} {G : Graph α} (h : x ∈ G.vertices): isWalk [x] G := by
  unfold isWalk
  simp
  apply h


/-
  Wenn ich einen Walk habe, dann kann ich den ersten Knoten weglassen.
-/
theorem isWalk_of_cons {hd : α} {tl : List α} {G : Graph α} (h : isWalk (hd::tl) G) :
    isWalk tl G := by
  -- Ersetze isWalk durch Definition und beweise beide Kriterien separat
  simp [isWalk]
  constructor
  · -- Sei x ein beliebiges Element der Liste tl
    intro x hx
    -- Da x in tl ist, ist x auch in hd::tl nach diesem Theorem
    have xmem : x ∈ (hd :: tl) := List.mem_cons_of_mem hd hx
    -- h.1 sagt, dass alle Elemente von (hd::tl) Knoten in G sind.
    -- Da x in hd::tl ist, ist es ein Knoten von g
    apply h.1 x xmem
  · -- Sei i ein beliebier Index, der zulässig ist und nicht der letzte
    -- da der letzte keinen Nachfolger hat den wir prüfen müssen.
    intro i hi
    -- Wenn wir das Element an Stelle i in tl überprüfen wollen, dann steht es
    -- an Stelle i+1 in tl.

    -- Zeige, dass i+1 ein valider und nicht der letzte Index in hd::tl ist
    have hi' : (i+1) + 1 < (hd::tl).length := by
      simp [hi]

    -- Nutze, dass hd::tl ein Walk nach Annhame ist.
    have h' := h.2 (i+1) hi'
    -- Vereinfache die Indices in h'. Da wir i+1 als Index verwenden, wird nie
    -- die Stelle 0 aufgerufen und wir können auf tl arbeiten
    simp at h'
    -- Dies ist unser Ziel
    apply h'

/-
  Wenn ein Walk nicht leer ist, können wir das erste Element mit List.head bestimmmen.
  Dieses ist ein Knoten in G
-/
theorem head_of_walk_is_mem {l : List α} {G : Graph α} (h : l ≠ []) (h' : isWalk l G) :
    (l.head h) ∈ G.vertices := by
  -- Der Kopf von l ist in l
  have mem_head: l.head h ∈ l :=  List.head_mem h
  -- Nach Annahme j' ist l ein Walk, daher sind alle Elemente in l Knoten von G
  -- nach erster Walk-Bedingung. Da der Knopf von l in l ist, können wir das nutzen.
  apply h'.1 (l.head h) mem_head

/-
  Wenn ein Pfad nicht leer ist, können wir einen Nachbarn des vordersten Elements an
  den Walk anfügen und erhalten wieder einen Walk
-/
theorem isWalk_of_cons_isNeighbor_isWalk {x : α} {l : List α}
  {G : Graph α} (h₁ : l ≠ []) (h₂ : isWalk l G)
  (h₃ : isNeighbor G (l.head h₁) x) :
    isWalk (x::l) G := by
  unfold isWalk
  constructor
  · -- Sei a ein beliebiges Element aus x::l
    intro a mem
    -- Vereinfache, dass a ∈ x::l zu a = x ∨ a ∈ l
    simp at mem
    -- Fallunterscheidung wo a in Liste ist.
    cases mem with
    | inl h =>
      -- Da a = x ist, ersetze a durch x
      rw [h]
      apply mem_isNeighbor h₃
    | inr h =>
      -- Wenn a in l ist, ist es per Annahme ein Knoten.
      apply h₂.1 a h
  · intro i hi
    cases i with
    | zero =>
      -- Das erste Element von x::l ist x und das Zweite l[0]
      simp
      -- l[0] und l.head sind identisch
      rw [List.head_eq_getElem] at h₃
      -- Daher ist eine Kante zwischen x und l[0], da x ein Nachbar von l[0] per
      --- Annahme ist
      apply h₃.left
    | succ m =>
      -- Wird betrachten Elemente aus l. Diese sind per Annahme (und Indexanpassung verbunden)
      simp
      apply h₂.2 m (by grind)

/-
  Da findNeighbor? einen Nachbarn des Kopfes liefert, können wir auch das Resultat davon
  anhängen und erhalten einen neuen Walk.
-/
theorem isWalk_of_cons_findNeighbor_isWalk {x : α} {l : List α}
  {G : Graph α} (h₁ : l ≠ []) (h₂ : isWalk l G)
  (h₃ : findNeighbor? G (l.head h₁) = some x) :
    isWalk (x::l) G := by
  apply isWalk_of_cons_isNeighbor_isWalk h₁ h₂
  apply isNeighbor_of_findNeighbor_eq_some h₃

/-
  Ein Kreis in G ist ein Walk dessen Anfang und Ende gleich sind und der mindestens Länge 2 hat.
  [x] ist kein Kreis, da die dort stehen bleiben, während [x,x] eine Selbstschleife ist
-/
def isCycle (l : List α) (G : Graph α) : Prop :=
  isWalk l G ∧ (∀ (h : l ≠ []), l.head h = l.getLast h) ∧ 2 ≤ l.length

/-
  Ein Graph ist azyklisch, wenn er keine Kreise hat.
-/
def isAcyclic (G : Graph α) : Prop := ∀ (l : List α), ¬ isCycle l G

/-
  Eine Liste l ist eine Teilmenge einer Liste l', wenn jedes Element aus l auch in l'
  ist. Die Reihenfolge ist dabei aber egal. Enthält l keine Duplikate, dann ist
  die Länge von l' kleiner gleich der Länge von l. Dieses Theorem benötigen wir für den Beweis der Terminierung.
-/
theorem length_le_length_of_subset_of_nodup {l l' : List α} (h : l ⊆ l') (h' : List.Nodup l) : l.length ≤ l'.length := by
  -- Wir beweisen die Aussage mittels Induktion über l für beliebige l'. Dafür
  -- benutzen wir generalizing um dies nicht für ein festes l' zu zeigen, was nicht
  -- gehen würde.
  induction l generalizing l' with
  | nil => simp
  | cons hd tl ih =>
    -- Aufspaltung der Hypothesen in Kopf und Körper der Liste
    simp
    simp at h
    simp at h'
    -- Wir zeigen, dass tl ⊆ l'.erase hd ist, da dies für die Nutzung der Induktions
    -- hypothese benötigt wird.
    have : tl ⊆ l'.erase hd := by
      intro a mem
      have : a ≠ hd := by
        intro ahd
        rw [ahd] at mem
        -- Wenn a = hd ist und a ∈ tl, dann ist l nicht duplikatfrei.
        exact absurd mem h'.1
      rw [List.mem_erase_of_ne this]
      apply h.2 mem
    specialize ih this h'.2
    -- tl.length ≤ (l'.erase hd).length -1
    rw [List.length_erase, if_pos h.1] at ih
    -- Nutze Transitivität
    apply Nat.le_trans (m := (l'.length - 1) + 1)
    · simp [ih]
    · grind

/-
  Nutzung des vorherigen Theorems für Graphen, da jeder Walk eine Teilmenge der Knotenliste ist.
-/
theorem length_walk_le_length_vertices_of_nodup {G : Graph α} {l : List α} (h : isWalk l G) (h₂ : List.Nodup l) :
    l.length ≤ G.vertices.length := by
  apply length_le_length_of_subset_of_nodup ?_ h₂
  unfold isWalk at h
  apply h.1

def exploreGraph (G : Graph α) (l : List α) (h : isWalk l G) (h₂ : List.Nodup l) (h' : l ≠ []): List α  :=
  let currVertex := l.head h'
  match h₄: findNeighbor? G currVertex with
  | some x =>
    if h₃ : x ∈ l
    then x::l
    else exploreGraph G (x::l) (isWalk_of_cons_findNeighbor_isWalk h' h (by simp [currVertex] at h₄; exact h₄)) (by simp[h₃, h₂]) (by simp)
  | none => l
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

theorem exploreGraph_semantics  {G : Graph α} {l l': List α} (h : isWalk l G) (h₂ : List.Nodup l) (h' : l ≠ []) (h₃ : exploreGraph G l h h₂ h' = l') :
    ∃ (hl : l' ≠ []), isWalk l' G ∧ (isSink (l'.head hl) G ∨ (l'.head hl ∈ l'.tail)) := by
  -- Nutze simp statt rw, da simp unter dem Quantor umschreiben kann.
  simp [isSink_iff_findNeighbor?_eq_none]
  induction hl: G.vertices.length - l.length generalizing l with
  | zero =>
    unfold exploreGraph at h₃
    simp at h₃
    split at h₃
    · -- x ist Nachbar des Kopfes
      rename_i x hx
      split at h₃
      · -- x in l
        rename_i hx'
        simp [← h₃]
        constructor
        · apply isWalk_of_cons_findNeighbor_isWalk h' h hx
        · -- rechter Fall
          right
          apply hx'
      · -- Dieser Fall kann nicht eintreten. Unser Walk ist bereits so lang, wie der
        -- Graph und enthält keine Duplikate. Wir zeigen, dass dies nicht möglich ist.
        rename_i hx'
        -- Fügen wir x an l an, ist es immer noch ein walk
        have walky := isWalk_of_cons_findNeighbor_isWalk _ h hx
        -- da x nicht in l, ist (x::l) duplikatfrei
        have walky_nodup : List.Nodup (x::l) := by grind
        -- (x::l).length = 1 + l.length ≤ G.vertices.length da duplikatfreier Walk
        have walky_length : (x::l).length ≤ G.vertices.length := by
          apply length_walk_le_length_vertices_of_nodup walky walky_nodup
        -- Nutze grind um Widerspruch zu erzeugen.
        grind
    · rename_i h₄
      simp [← h₃]
      constructor
      · apply h
      · -- da l=l' können wir den Beweis, dass l ≠ [] verwenden für den Existenzquantor
        exists h'
        -- Fall Senke
        left
        constructor
        · -- Zeige, dass der Kopf von l ein Knoten ist, da l ein Walk ist.
          apply h.1
          simp
        · -- Kopf ist Senke
          apply h₄
  | succ m ih =>
    -- Der Induktionsschritt funktioniert größtenteils genauso
    unfold exploreGraph at h₃
    simp at h₃
    split at h₃
    · rename_i x hx
      split at h₃
      · rename_i hx'
        simp [← h₃]
        constructor
        · apply isWalk_of_cons_findNeighbor_isWalk h' h hx
        · right
          apply hx'
      · rename_i hx'
        -- Induktionsschritt da rekursiver Fall. Wir bereitn diesen vor indem wir
        -- zeigen, dass immer noch ein Walk entsteht.
        have ih₁: isWalk (x::l) G := by
          apply isWalk_of_cons_findNeighbor_isWalk h' h hx
        -- die restlichen Fälle können per grind übernommen werden.
        apply ih ih₁ (by grind) (by simp) h₃ (by grind)
    · simp [← h₃]
      constructor
      · apply h
      · exists h'
        left
        constructor
        · apply h.1
          simp
        · assumption

/-
  takeUntil nimmt ein Element, eine Liste und einen Beweis, dass das Element in der Liste ist
  und behält die Elemente der Liste bis zum Element.
-/
def takeUntil (x : α) (l : List α) (hx : x ∈ l) : List α :=
  match l with
  | .nil =>
    -- Da x in l ist per Annahme und l=[], kann dieser Fall nicht auftreten.
    -- Zur Vollständigkeit muss er dennoch aufgeführt werden. Mittels simp
    -- zeigen wir, dass false entsteht und können dies als Wert benutzen, da
    -- aus false beliebiges folgt.
    by simp at hx
  | .cons hd tl =>
    if h: x = hd
    then [hd]
    else hd::(takeUntil x tl (by grind))

/-
  Die enstehende Liste ist nicht leer. Beweis per Fallunterscheidung.
-/
theorem takeUntil_not_empty {x : α} {l : List α} (hx : x ∈ l) : takeUntil x l hx ≠ [] := by
  cases l with
  | nil => simp at hx
  | cons hd tl =>
    simp [takeUntil]
    split
    · simp
    · simp

/-
  Der Kopf der neuen Liste ist im jeden Fall der selbe.
-/
theorem takeUntil_head_eq_head {x : α} {l : List α} (hx : x ∈ l) :
    l.head (by grind) = (takeUntil x l hx).head (takeUntil_not_empty hx) := by
  cases l with
  | nil => simp at hx
  | cons hd tl =>
    simp [takeUntil]
    split
    · simp
    · simp

/-
  Die Liste endet mit dem gesuchten Element. Beweis per Induktion.
-/
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

/-
  Da das gesuchte Element in der Liste auftaucht, hat es mindestens Länge 1.
-/
theorem one_le_length_takeUntil {x : α} {l : List α} (hx : x ∈ l) :
    1 ≤ (takeUntil x l hx).length := by
  cases l with
  | nil => simp at hx
  | cons hd tl =>
    simp [takeUntil]
    split
    · simp
    · simp

/-
  Diese Operation erhält die Walkeigenschaft. Beweis mit vorherigen Lemmas und simp.
-/
theorem isWalk_takeUntil_of_isWalk  {x : α} {G : Graph α} {l : List α} (hx : x ∈ l) (h : isWalk l G) :
    isWalk (takeUntil x l hx) G := by
  induction l with
  | nil => simp at hx
  | cons hd tl ih =>
    simp [takeUntil]
    -- Fallunterscheidung ob x = hd ist.
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

/-
  Unser Hauptsatz: Jeder Graph mit mindestens einem Knoten hat eine Senke oder einen Kreis.
-/
theorem every_graph_has_sink_or_cycle (G : Graph α) (h : ∃ (x : α), x ∈ G.vertices) :
    (∃ (v : α), isSink v G) ∨ ∃ (l : List α), isCycle l G := by
  -- x ist der Knoten
  rcases h with ⟨x, hx⟩
  -- Das Resultat, wenn wir exploreGraph von x starten.
  let l' := exploreGraph G [x] (isWalk_singleton hx) (by simp) (by simp)
  have := exploreGraph_semantics (G:= G) (l:= [x])
    (l' := l') (isWalk_singleton hx) (by simp) (by simp) (by rfl)
  rcases this with ⟨hl', hwalk, h⟩
  cases h with
  | inl h =>
    -- Fall Senke
    left
    exists l'.head hl'
  | inr h =>
    -- Fall Kreis. Nutze takeUntil um Kreis aus Pfad zu erhalten.
    right
    exists (l'.head hl') :: (takeUntil (l'.head hl') l'.tail h)
    -- Definition von isCycle
    simp [isCycle]
    constructor
    · -- Walkeigenschaft
      apply isWalk_of_cons_isNeighbor_isWalk (takeUntil_not_empty h)
      · -- l' kann zerlegt werden
        have : l' = (l'.head hl')::(l'.tail) := by exact Eq.symm (List.cons_head_tail hl')
        rw [this] at hwalk
        apply isWalk_takeUntil_of_isWalk h (isWalk_of_cons hwalk)
      · -- Kopf darf an neuen Pfad angefügt werden
        rw [← takeUntil_head_eq_head]
        simp [isNeighbor]
        simp [isWalk] at hwalk
        constructor
        · have := hwalk.2 0 (by grind)
          simp [List.head_eq_getElem]
          apply this
        · constructor
          · apply hwalk.1
            simp
          · apply hwalk.1
            simp
    · constructor
      · -- Anfang und Ende gleich
        intro _
        rw [List.getLast_cons (takeUntil_not_empty h)]
        rw [getLast_takeUntil]
      · -- Kreis hat mindestens Länge 2
        -- Durch simp reicht es aus, dass takeUntil mindestens Länge 1 hat,
        -- da der Rest vorne angefügt wird.
        apply one_le_length_takeUntil
