import Std

/-!
# Go — board model

A formal model of the rules engine in `go.html` (Chinese rules): points, colours,
orthogonal neighbours, the enumeration of all points, and the position key used
for positional superko. No Mathlib — everything here is Lean 4 core.
-/

namespace Go

/-- The three states a point can hold. Mirrors `EMPTY/BLACK/WHITE` in go.html. -/
inductive Color where
  | empty
  | black
  | white
  deriving DecidableEq, Repr

namespace Color

def opponent : Color → Color
  | .empty => .empty
  | .black => .white
  | .white => .black

@[simp] theorem black_opponent : black.opponent = white := rfl
@[simp] theorem white_opponent : white.opponent = black := rfl
@[simp] theorem empty_opponent : empty.opponent = empty := rfl

/-- Only black and white are stones; empty is not. -/
def isStone : Color → Bool
  | .empty => false
  | .black => true
  | .white => true

theorem isStone_iff (c : Color) : c.isStone = true ↔ c ≠ .empty := by
  cases c <;> simp [isStone]

end Color

/-- A point on an n×n board: column `x`, row `y`. go.html uses the flat index
    `y * n + x`; the two encodings are interchangeable. -/
structure Point (n : Nat) where
  x : Fin n
  y : Fin n
  deriving DecidableEq, Repr

/-- A board position: the colour of every point. -/
abbrev Board (n : Nat) := Point n → Color

/-- Orthogonal neighbours — left, right, up, down — omitting points off the
    board. Mirrors `neighbours()` in go.html, where an edge stone has three
    neighbours and a corner has two. -/
def neighbours (p : Point n) : List (Point n) :=
  (if _ : 0 < p.x.val then [(⟨⟨p.x.val - 1, by omega⟩, p.y⟩ : Point n)] else []) ++
  (if _ : p.x.val + 1 < n then [(⟨⟨p.x.val + 1, by omega⟩, p.y⟩ : Point n)] else []) ++
  (if _ : 0 < p.y.val then [(⟨p.x, ⟨p.y.val - 1, by omega⟩⟩ : Point n)] else []) ++
  (if _ : p.y.val + 1 < n then [(⟨p.x, ⟨p.y.val + 1, by omega⟩⟩ : Point n)] else [])

/-- Orthogonally adjacent (either direction). Connectivity is undirected, so
    stating adjacency with both orientations keeps proofs symmetric. -/
def Adj {n : Nat} (p q : Point n) : Prop := q ∈ neighbours p ∨ p ∈ neighbours q

/-- A point of `neighbours p` differs from `p` by at most one in each
    coordinate. Used by the concrete board examples to bound which colours a
    region can border. -/
theorem mem_neighbours_bounds {p r : Point n} (h : r ∈ neighbours p) :
    r.x.val ≤ p.x.val + 1 ∧ p.x.val ≤ r.x.val + 1 ∧
    r.y.val ≤ p.y.val + 1 ∧ p.y.val ≤ r.y.val + 1 := by
  simp only [neighbours, List.mem_append] at h
  rcases h with (((h | h) | h) | h)
  · by_cases c : 0 < p.x.val
    · simp [c, List.mem_cons, List.not_mem_nil] at h
      have hx : r.x.val = p.x.val - 1 := by rw [h]
      have hy : r.y.val = p.y.val := by rw [h]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
    · simp [c] at h
  · by_cases c : p.x.val + 1 < n
    · simp [c, List.mem_cons, List.not_mem_nil] at h
      have hx : r.x.val = p.x.val + 1 := by rw [h]
      have hy : r.y.val = p.y.val := by rw [h]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
    · simp [c] at h
  · by_cases c : 0 < p.y.val
    · simp [c, List.mem_cons, List.not_mem_nil] at h
      have hx : r.x.val = p.x.val := by rw [h]
      have hy : r.y.val = p.y.val - 1 := by rw [h]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
    · simp [c] at h
  · by_cases c : p.y.val + 1 < n
    · simp [c, List.mem_cons, List.not_mem_nil] at h
      have hx : r.x.val = p.x.val := by rw [h]
      have hy : r.y.val = p.y.val + 1 := by rw [h]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
    · simp [c] at h

/-- Every point of an n×n board, enumerated row-major. -/
def allPoints (n : Nat) : List (Point n) :=
  (List.finRange n).flatMap fun x => (List.finRange n).map fun y => Point.mk x y

theorem sum_map_const {α : Type} (xs : List α) (m : Nat) :
    (List.map (fun _ => m) xs).sum = xs.length * m := by
  induction xs with
  | nil => simp
  | cons a as ih => simp [List.sum_cons, List.length_cons, ih, Nat.succ_mul,
                          Nat.add_comm]

theorem length_allPoints (n : Nat) : (allPoints n).length = n * n := by
  simp [allPoints, List.length_flatMap, List.length_map, List.length_finRange,
        sum_map_const]

/-- The enumeration is exhaustive: every point occurs in `allPoints`. -/
theorem mem_allPoints (p : Point n) : p ∈ allPoints n := by
  simp only [allPoints, List.mem_flatMap]
  exact ⟨p.x, List.mem_finRange _, by
    simp only [List.mem_map]
    exact ⟨p.y, List.mem_finRange _, rfl⟩⟩

theorem nodup_map {α β : Type} {f : α → β} :
    ∀ (xs : List α), List.Nodup xs →
      (∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b) →
      List.Nodup (xs.map f) := by
  intro xs
  induction xs with
  | nil => intro _ _; simp
  | cons a as ih =>
    intro h hinj
    simp only [List.map_cons]
    rw [List.nodup_cons] at h ⊢
    refine ⟨?_, ih h.2 (fun b hb c hc heq =>
      hinj b (List.mem_cons_of_mem a hb) c (List.mem_cons_of_mem a hc) heq)⟩
    intro hm
    obtain ⟨b, hb, heq⟩ := List.mem_map.mp hm
    have e : b = a := hinj b (List.mem_cons_of_mem a hb) a List.mem_cons_self heq
    subst e
    exact h.1 hb

theorem nodup_flatMap {α β : Type} {f : α → List β} :
    ∀ (xs : List α), List.Nodup xs →
      (∀ a ∈ xs, List.Nodup (f a)) →
      (∀ a ∈ xs, ∀ b ∈ xs, a ≠ b → ∀ c, c ∈ f a → c ∉ f b) →
      List.Nodup (xs.flatMap f) := by
  intro xs
  induction xs with
  | nil => intro _ _ _; simp
  | cons a as ih =>
    intro h hrec hdisj
    simp only [List.flatMap_cons]
    rw [List.nodup_cons] at h
    obtain ⟨hnotin, hnd⟩ := h
    rw [List.nodup_append]
    refine ⟨hrec a List.mem_cons_self, ih hnd
      (fun b hb => hrec b (List.mem_cons_of_mem a hb))
      (fun b hb c hc => hdisj b (List.mem_cons_of_mem a hb)
        c (List.mem_cons_of_mem a hc)), ?_⟩
    intro c hc d hd
    obtain ⟨b, hb, hdf⟩ := List.mem_flatMap.mp hd
    have hne : a ≠ b := by
      intro he
      subst he
      exact hnotin hb
    intro he
    subst he
    exact hdisj a List.mem_cons_self b (List.mem_cons_of_mem a hb) hne c hc hdf

theorem nodup_filter {α : Type} (p : α → Bool) {l : List α}
    (h : List.Nodup l) : List.Nodup (List.filter p l) := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.nodup_cons] at h
    by_cases hp : p a = true
    · simp [hp]
      exact ⟨h.1, ih h.2⟩
    · simp [hp]
      exact ih h.2

theorem nodup_allPoints (n : Nat) : List.Nodup (allPoints n) := by
  simp only [allPoints]
  exact nodup_flatMap _ (List.nodup_finRange n)
    (fun x _ => nodup_map _ (List.nodup_finRange n)
      (fun y _ z _ heq => by
        have := congrArg Point.y heq
        simpa using this))
    (fun x _ y _ hxy c hc hd => by
      obtain ⟨cy, _, rfl⟩ := List.mem_map.mp hc
      obtain ⟨cz, _, heq⟩ := List.mem_map.mp hd
      exact hxy (congrArg Point.x heq).symm)

/-- go.html keys a position by joining its array (`key = b.join("")`). This is
    the same idea: the list of colours over `allPoints`. -/
def key (b : Board n) : List Color := (allPoints n).map b

theorem map_eq_of_mem {α β : Type} {f g : α → β} {xs : List α}
    (h : List.map f xs = List.map g xs) : ∀ x ∈ xs, f x = g x := by
  induction xs with
  | nil => intro x hx; cases hx
  | cons a as ih =>
    simp only [List.map_cons] at h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | htail
    · injection h
    · exact ih (by injection h) x htail

/-- The key determines the position: two boards with equal keys agree at every
    point. Justifies superko detection via `key`. -/
theorem key_injective {b b' : Board n} (h : key b = key b') (p : Point n) : b p = b' p :=
  map_eq_of_mem h p (mem_allPoints p)

end Go
