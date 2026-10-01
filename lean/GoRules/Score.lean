import GoRules.Fill
import GoRules.Move

/-!
# Chinese area scoring

Mirrors `scoreOn()` in `go.html`: every empty region's border colours decide
whose territory it is (`border.size === 1` → that colour, else neutral), and
stones count per side. The headline theorem is the score partition: stones +
territory + neutral = N² for every position.
-/

namespace Go

/-- Territory ownership of an empty region: black, white, or neither. -/
inductive Label where
  | black | white | neutral
  deriving DecidableEq, Repr

/-- Does the region `S` touch a black stone? The Lean form of collecting
    `border.add(b[n])` for non-empty neighbours in `scoreOn()` (go.html). -/
def touchesBlack (b : Board n) (S : Region n) : Bool :=
  (allPoints n).any fun q => S q && (neighbours q).any fun r => decide (b r = .black)

/-- Does the region `S` touch a white stone? -/
def touchesWhite (b : Board n) (S : Region n) : Bool :=
  (allPoints n).any fun q => S q && (neighbours q).any fun r => decide (b r = .white)

/-- `border.size === 1 ? (border.has(BLACK) ? black : white) : neutral`
    from `scoreOn()` (go.html): a region touching exactly one colour is that
    colour's territory, anything else is neutral. -/
def labelOf (b : Board n) (S : Region n) : Label :=
  if touchesBlack b S && !touchesWhite b S then .black
  else if touchesWhite b S && !touchesBlack b S then .white
  else .neutral

theorem labelOf_cases (b : Board n) (S : Region n) :
    labelOf b S = .black ∨ labelOf b S = .white ∨ labelOf b S = .neutral := by
  simp only [labelOf]
  cases hb : touchesBlack b S <;> cases hw : touchesWhite b S <;> simp

/-- Black's stones on `b`. -/
def stones (b : Board n) (c : Color) : Nat :=
  List.countP (fun p => decide (b p = c)) (allPoints n)

/-- One empty point's bucket: it contributes to `l`'s territory exactly when
    it is empty and its region carries label `l`. -/
def bucket (b : Board n) (l : Label) (p : Point n) : Bool :=
  decide (b p = .empty) && decide (labelOf b (emptyRegion b p) = l)

/-- Territory of label `l` on `b`: count empty points by their region's label.
    Every point of a region shares one label, so this counts each region's
    size exactly once, as `scoreOn()` does with `counted[]`. -/
def terr (b : Board n) (l : Label) : Nat :=
  List.countP (bucket b l) (allPoints n)

/-- The Chinese area score of a position, split the way `scoreGame()` reports
    it (terr[0..2], stones[0..1]; komi is outside this record). -/
structure Score where
  stonesBlack : Nat
  stonesWhite : Nat
  terrBlack : Nat
  terrWhite : Nat
  terrNeutral : Nat
  deriving DecidableEq, Repr

def scoreOn (b : Board n) : Score where
  stonesBlack := stones b .black
  stonesWhite := stones b .white
  terrBlack := terr b .black
  terrWhite := terr b .white
  terrNeutral := terr b .neutral

/-! ### Counting lemmas -/

/-- Counting is congruent pointwise. -/
theorem countP_congr_of_eq {α : Type} {f g : α → Bool} (xs : List α)
    (h : ∀ x ∈ xs, f x = g x) : List.countP f xs = List.countP g xs := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    have ha : f a = g a := h a List.mem_cons_self
    have ht : ∀ x ∈ as, f x = g x := fun x hx => h x (List.mem_cons_of_mem a hx)
    have htail := ih ht
    simp only [List.countP_cons, ha, htail]

theorem countP_const_true (xs : List α) :
    List.countP (fun _ => true) xs = xs.length := by
  induction xs with
  | nil => simp
  | cons a as ih => simp [ih]

/-- For pairwise disjoint Bool predicates the counts add up to the count of
    their pointwise disjunction. -/
theorem countP_add3 {α : Type} (f g h : α → Bool) (xs : List α)
    (hdisj : ∀ x, (f x && g x) = false ∧ (f x && h x) = false ∧ (g x && h x) = false) :
    List.countP f xs + List.countP g xs + List.countP h xs
      = List.countP (fun x => f x || g x || h x) xs := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    simp only [List.countP_cons]
    have hd := hdisj a
    cases hf : f a <;> cases hg : g a <;> cases hh : h a <;>
      simp [hf, hg, hh] at hd ⊢ <;> omega

/-! ### The partition theorem -/

/-- Every point has exactly one colour, so the three colour buckets sum to
    the board size. -/
theorem stones_sum (b : Board n) :
    stones b .black + stones b .white + stones b .empty = n * n := by
  simp only [stones]
  have hdisj : ∀ p : Point n,
      (decide (b p = .black) && decide (b p = .white)) = false ∧
      (decide (b p = .black) && decide (b p = .empty)) = false ∧
      (decide (b p = .white) && decide (b p = .empty)) = false := by
    intro p; cases c : b p <;> simp
  rw [countP_add3 _ _ _ _ hdisj]
  have hc : ∀ p ∈ allPoints n,
      (decide (b p = .black) || decide (b p = .white) || decide (b p = .empty)) = true := by
    intro p _; cases c : b p <;> simp
  rw [countP_congr_of_eq _ hc, countP_const_true, length_allPoints]

/-- The three territory buckets cover exactly the empty points: an empty
    point's region has one label, a non-empty point belongs to none. -/
theorem terr_sum (b : Board n) :
    terr b .black + terr b .white + terr b .neutral = stones b .empty := by
  simp only [terr, stones]
  have hdisj : ∀ p : Point n,
      (bucket b .black p && bucket b .white p) = false ∧
      (bucket b .black p && bucket b .neutral p) = false ∧
      (bucket b .white p && bucket b .neutral p) = false := by
    intro p
    rcases labelOf_cases b (emptyRegion b p) with hL | hL | hL <;>
      simp [bucket, hL]
  rw [countP_add3 _ _ _ _ hdisj]
  have hc : ∀ p ∈ allPoints n,
      (bucket b .black p || bucket b .white p || bucket b .neutral p)
        = decide (b p = .empty) := by
    intro p _
    simp only [bucket]
    by_cases he : b p = .empty
    · rcases labelOf_cases b (emptyRegion b p) with hL | hL | hL <;>
        simp [he, hL]
    · simp [he]
  rw [countP_congr_of_eq _ hc]

/-- Stones + territory + neutral = N² on every board — the `checkTotals()`
    invariant from `test.js`, for `scoreOn()` positions. -/
theorem scoreOn_partition (b : Board n) :
    (scoreOn b).stonesBlack + (scoreOn b).stonesWhite
      + (scoreOn b).terrBlack + (scoreOn b).terrWhite
      + (scoreOn b).terrNeutral = n * n := by
  have hA := stones_sum b
  have hT := terr_sum b
  simp only [scoreOn]
  omega

end Go
