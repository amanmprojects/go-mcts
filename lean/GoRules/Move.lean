import GoRules.Fill

/-!
# Go — moves: placement, capture, and the rule check

The move machinery of `go.html`: landing a stone, lifting dead opponent
chains, and `illegal()` — occupied, ko, suicide, positional superko.
Chinese rules: a capturing move is never suicide, and the suicide check
runs after captures.
-/

namespace Go

/-! ### Liberties and placement -/

/-- `group(...).liberties.size > 0`: the region touches an empty point. -/
def HasLiberty (b : Board n) (S : Region n) : Prop :=
  ∃ q r, S q = true ∧ r ∈ neighbours q ∧ b r = .empty

/-- The Boolean form used by the rule check. -/
def hasLiberty (b : Board n) (S : Region n) : Bool :=
  (allPoints n).any fun q => S q && (neighbours q).any fun r => decide (b r = .empty)

theorem hasLiberty_iff {b : Board n} {S : Region n} :
    hasLiberty b S = true ↔ HasLiberty b S := by
  constructor
  · intro h
    obtain ⟨q, _, hq⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true] at hq
    obtain ⟨hs, hl⟩ := hq
    obtain ⟨r, hr, hb⟩ := List.any_eq_true.mp hl
    exact ⟨q, r, hs, hr, by simpa using hb⟩
  · intro ⟨q, r, hq, hr, hb⟩
    refine List.any_eq_true.mpr ⟨q, mem_allPoints q, ?_⟩
    simp only [Bool.and_eq_true]
    exact ⟨hq, List.any_eq_true.mpr ⟨r, hr, by simp [hb]⟩⟩

/-- Place a stone at `p`, lifting nothing. -/
def place0 (b : Board n) (p : Point n) (c : Color) : Board n :=
  fun q => if q = p then c else b q

@[simp] theorem place0_self (b : Board n) (p : Point n) (c : Color) :
    place0 b p c p = c := by simp [place0]

theorem place0_of_ne {b : Board n} {p q : Point n} {c : Color} (h : q ≠ p) :
    place0 b p c q = b q := by simp [place0, h]

/-- Empty every point of `S`. -/
def clear (b : Board n) (S : Region n) : Board n :=
  fun q => if S q = true then .empty else b q

/-- The stone at `p` has landed and `q` is lifted: an opponent chain that
    touched `p` and had no liberty left in that resulting position. -/
def killsAt (b : Board n) (p : Point n) (c : Color) (q : Point n) : Bool :=
  let t := place0 b p c
  (neighbours p).any fun r =>
    decide (t r = c.opponent) && decide (chain t r q = true) &&
      !hasLiberty t (chain t r)

theorem killsAt_iff {b : Board n} {p q : Point n} {c : Color} :
    killsAt b p c q = true ↔
      ∃ r, r ∈ neighbours p ∧ place0 b p c r = c.opponent ∧
        chain (place0 b p c) r q = true ∧
        ¬ HasLiberty (place0 b p c) (chain (place0 b p c) r) := by
  simp only [killsAt, List.any_eq_true, Bool.and_eq_true, decide_eq_true_iff]
  constructor
  · intro ⟨r, hr, h⟩
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨r, hr, h1, h2, ?_⟩
    intro hl
    have h4 := hasLiberty_iff.mpr hl
    cases hx : hasLiberty (place0 b p c) (chain (place0 b p c) r)
    · simp [hx] at h4
    · simp [hx] at h3
  · intro ⟨r, hr, h1, h2, hneg⟩
    refine ⟨r, hr, ?_⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    by_cases hl : hasLiberty (place0 b p c) (chain (place0 b p c) r)
    · exact absurd (hasLiberty_iff.mp hl) hneg
    · simp [hl]

/-- The move: land the stone, lift every dead opponent chain. The lift is
    simultaneous, which matches go.html's loop because two distinct chains
    of the same colour are never adjacent, so clearing one cannot change
    another's liberties. -/
def place (b : Board n) (p : Point n) (c : Color) : Board n :=
  clear (place0 b p c) (killsAt b p c)

theorem place_eq {b : Board n} {p q : Point n} {c : Color} :
    place b p c q =
      (if killsAt b p c q = true then .empty
       else if q = p then c else b q) := by
  simp [place, clear, place0]

/-- The placed stone stands, even when the move captures. -/
theorem place_self (b : Board n) (p : Point n) (c : Color) :
    place b p c p = c := by
  by_cases hk : killsAt b p c p = true
  · obtain ⟨r, hr, htc, hchain, _⟩ := killsAt_iff.mp hk
    have h1 : place0 b p c p = c := place0_self ..
    have hp := fill_color (b := place0 b p c) (t := place0 b p c r)
      (p₀ := r) (r := p) rfl hchain
    rw [h1, htc] at hp
    cases c <;> try simp at hp
    · simp [place, clear]
  · rw [place_eq]
    simp [hk]

/-- Lifted stones come out empty. -/
theorem place_of_kills {b : Board n} {p q : Point n} {c : Color}
    (h : killsAt b p c q = true) : place b p c q = .empty := by
  simp [place, clear, h]

/-- Everything else is untouched. -/
theorem place_of_not_kills {b : Board n} {p q : Point n} {c : Color}
    (h : killsAt b p c q = false) (hne : q ≠ p) :
    place b p c q = b q := by
  simp [place, clear, place0, h, hne]

/-! ### Capture beats suicide -/

/-- If the move lifts a stone, the played stone has a liberty: the cleared
    enemy point sits next to it. go.html checks this after captures, so a
    capturing move is never suicide. -/
theorem capture_not_suicide {b : Board n} {p q : Point n} {c : Color}
    (h : killsAt b p c q = true) :
    HasLiberty (place b p c) (chain (place b p c) p) := by
  obtain ⟨r, hr, htc, hchain, hlib⟩ := killsAt_iff.mp h
  have hrr : chain (place0 b p c) r r = true :=
    fill_mono_le (Nat.zero_le _) (seed_mem r)
  have hkill : killsAt b p c r = true :=
    killsAt_iff.mpr ⟨r, hr, htc, hrr, hlib⟩
  have hre : place b p c r = .empty := place_of_kills hkill
  have hpc : chain (place b p c) p p = true :=
    fill_mono_le (Nat.zero_le _) (seed_mem p)
  exact ⟨p, r, hpc, hr, hre⟩

/-! ### The rule check -/

/-- Why a move is refused — go.html's `illegal()` return strings. -/
inductive IllegalReason where
  | occupied
  | ko
  | suicide
  | superko
  deriving DecidableEq, Repr

/-- Mirrors `illegal()` in go.html: `none` when the move is legal. `ko` is
    the point forbidden by simple ko; `seen` holds every position key that
    has occurred, for positional superko. -/
def illegal (b : Board n) (p : Point n) (c : Color) (ko : Option (Point n))
    (seen : List (List Color)) : Option IllegalReason :=
  if b p ≠ .empty then some .occupied
  else if ko = some p then some .ko
  else
    let t := place b p c
    if !hasLiberty t (chain t p) then some .suicide
    else if decide (key t ∈ seen) then some .superko
    else none

theorem illegal_eq_some_occupied {b : Board n} {p : Point n} {c : Color}
    {ko : Option (Point n)} {seen : List (List Color)} :
    illegal b p c ko seen = some .occupied ↔ b p ≠ .empty := by
  by_cases h : b p = .empty <;>
    by_cases hk : ko = some p <;>
    by_cases hl : hasLiberty (place b p c) (chain (place b p c) p) = true <;>
    by_cases hm : key (place b p c) ∈ seen <;>
    simp [illegal, h, hk, hl, hm]

theorem illegal_eq_some_ko {b : Board n} {p : Point n} {c : Color}
    {ko : Option (Point n)} {seen : List (List Color)} :
    illegal b p c ko seen = some .ko ↔ b p = .empty ∧ ko = some p := by
  by_cases h : b p = .empty <;>
    by_cases hk : ko = some p <;>
    by_cases hl : hasLiberty (place b p c) (chain (place b p c) p) = true <;>
    by_cases hm : key (place b p c) ∈ seen <;>
    simp [illegal, h, hk, hl, hm]

theorem illegal_eq_some_suicide {b : Board n} {p : Point n} {c : Color}
    {ko : Option (Point n)} {seen : List (List Color)} :
    illegal b p c ko seen = some .suicide ↔
      b p = .empty ∧ ko ≠ some p ∧
      hasLiberty (place b p c) (chain (place b p c) p) = false := by
  by_cases h : b p = .empty <;>
    by_cases hk : ko = some p <;>
    by_cases hl : hasLiberty (place b p c) (chain (place b p c) p) = true <;>
    by_cases hm : key (place b p c) ∈ seen <;>
    simp [illegal, h, hk, hl, hm]

theorem illegal_eq_some_superko {b : Board n} {p : Point n} {c : Color}
    {ko : Option (Point n)} {seen : List (List Color)} :
    illegal b p c ko seen = some .superko ↔
      b p = .empty ∧ ko ≠ some p ∧
      hasLiberty (place b p c) (chain (place b p c) p) = true ∧
      key (place b p c) ∈ seen := by
  by_cases h : b p = .empty <;>
    by_cases hk : ko = some p <;>
    by_cases hl : hasLiberty (place b p c) (chain (place b p c) p) = true <;>
    by_cases hm : key (place b p c) ∈ seen <;>
    simp [illegal, h, hk, hl, hm]

theorem illegal_eq_none {b : Board n} {p : Point n} {c : Color}
    {ko : Option (Point n)} {seen : List (List Color)} :
    illegal b p c ko seen = none ↔
      b p = .empty ∧ ko ≠ some p ∧
      hasLiberty (place b p c) (chain (place b p c) p) = true ∧
      key (place b p c) ∉ seen := by
  by_cases h : b p = .empty <;>
    by_cases hk : ko = some p <;>
    by_cases hl : hasLiberty (place b p c) (chain (place b p c) p) = true <;>
    by_cases hm : key (place b p c) ∈ seen <;>
    simp [illegal, h, hk, hl, hm]

/-! ### Simple ko -/

/-- The ko point after a move: the lifted stone, when exactly one fell —
    go.html's `captured.length === 1 ? captured[0] : -1`. -/
def koPoint (b : Board n) (p : Point n) (c : Color) : Option (Point n) :=
  match (allPoints n).filter (killsAt b p c) with
  | [q] => some q
  | _ => none

theorem killsAt_of_koPoint {b : Board n} {p q : Point n} {c : Color}
    (h : koPoint b p c = some q) : killsAt b p c q = true := by
  unfold koPoint at h
  cases hl : (allPoints n).filter (killsAt b p c) with
  | nil => simp [hl] at h
  | cons a as =>
    cases ha : as with
    | nil =>
      simp [hl, ha] at h
      subst h
      have haf : a ∈ (allPoints n).filter (killsAt b p c) := by
        rw [hl]
        exact List.mem_cons_self
      exact (List.mem_filter.mp haf).2
    | cons b' bs => simp [hl, ha] at h

theorem koPoint_eq_some {b : Board n} {p q : Point n} {c : Color}
    (hq : killsAt b p c q = true)
    (hu : ∀ r, killsAt b p c r = true → r = q) : koPoint b p c = some q := by
  unfold koPoint
  have hmem : q ∈ (allPoints n).filter (killsAt b p c) := by
    rw [List.mem_filter]
    exact ⟨mem_allPoints q, hq⟩
  have hall : ∀ x ∈ (allPoints n).filter (killsAt b p c), x = q := by
    intro x hx
    obtain ⟨_, hk⟩ := List.mem_filter.mp hx
    exact hu x hk
  have hnd := nodup_filter (killsAt b p c) (nodup_allPoints n)
  have hfil : (allPoints n).filter (killsAt b p c) = [q] := by
    cases hl : (allPoints n).filter (killsAt b p c) with
    | nil => exact absurd hmem (by simp [hl])
    | cons a as =>
      have heq1 : a = q := hall a (by simp [hl])
      cases ha : as with
      | nil => simp [heq1]
      | cons b' bs =>
        have heq2 : b' = q := hall b' (by simp [hl, ha])
        simp [hl, ha] at hnd
        have hab : a = b' := heq1.trans heq2.symm
        exact absurd hab hnd.1.1
  simp [hfil]

/-- A recorded ko point is refused as simple ko. -/
theorem ko_refused {b : Board n} {p q : Point n} {c : Color}
    {seen : List (List Color)} (h : koPoint b p c = some q) :
    illegal (place b p c) q c.opponent (koPoint b p c) seen = some .ko := by
  have hb : place b p c q = .empty :=
    place_of_kills (killsAt_of_koPoint h)
  simp [illegal, hb, h]

end Go
