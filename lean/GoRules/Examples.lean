import GoRules.Score

/-!
# Worked examples — the positions from `test.js`

Each block mirrors a test in `test.js`, on the smallest board that has the
same local geometry (corner and edge neighbours do not depend on board size,
so 9×9 tests whose stones sit in one corner are restated on 3×3). Score
examples use 5×5 exactly as `test.js` does.

Direct `decide` is fine for moves on small boards, but evaluating
`emptyRegion` (25 rounds of flood fill) at every point of a 5×5 is far too
slow, so the 5×5 scores are proved from a structural characterisation of the
regions instead: each region is identified with a set of columns, and only
the final cheap count is evaluated.
-/

namespace Go

/-- Point from coordinate literals; `omega` discharges the bounds. -/
def pt (n x y : Nat) (hx : x < n := by omega) (hy : y < n := by omega) : Point n :=
  ⟨⟨x, hx⟩, ⟨y, hy⟩⟩

/-- Is `p` the point `(x, y)`? -/
def isPt {n : Nat} (p : Point n) (x y : Nat) : Bool :=
  decide (p.x.val = x ∧ p.y.val = y)

/-- Empty points adjacent to the region `S` — `group(...).liberties.size`. -/
def libertyCount (b : Board n) (S : Region n) : Nat :=
  List.countP (fun q => decide (b q = .empty) &&
    ((neighbours q).any S ||
      (allPoints n).any fun s => S s && decide (q ∈ neighbours s))) (allPoints n)

/-! ### Generic path helpers (used by the 5×5 region proofs) -/

theorem adj_right (p : Point n) (h : p.x.val + 1 < n) :
    Adj p ⟨⟨p.x.val + 1, h⟩, p.y⟩ := by
  refine Or.inl ?_
  simp [neighbours, h]

theorem adj_left (p : Point n) (h : 0 < p.x.val) :
    Adj p ⟨⟨p.x.val - 1, by omega⟩, p.y⟩ := by
  refine Or.inl ?_
  simp [neighbours, h]

theorem adj_up (p : Point n) (h : p.y.val + 1 < n) :
    Adj p ⟨p.x, ⟨p.y.val + 1, h⟩⟩ := by
  refine Or.inl ?_
  simp [neighbours, h]

theorem adj_down (p : Point n) (h : 0 < p.y.val) :
    Adj p ⟨p.x, ⟨p.y.val - 1, by omega⟩⟩ := by
  refine Or.inl ?_
  simp [neighbours, h]

theorem point_ext {n} {p q : Point n} (hx : p.x.val = q.x.val) (hy : p.y.val = q.y.val) :
    p = q := by
  cases p with | mk px py =>
  cases q with | mk qx qy =>
  have e1 : px = qx := Fin.ext hx
  have e2 : py = qy := Fin.ext hy
  subst e1; subst e2
  rfl

/-- Adjacency by coordinates: `q` sits one column to the right of `p`. -/
theorem adj_right_eq {p q : Point n} (hx : p.x.val + 1 = q.x.val)
    (hy : p.y.val = q.y.val) (h : p.x.val + 1 < n) : Adj p q := by
  have e : q = ⟨⟨p.x.val + 1, h⟩, p.y⟩ := point_ext hx.symm hy.symm
  rw [e]
  exact adj_right p h

/-- Adjacency by coordinates: `q` sits one column to the left of `p`. -/
theorem adj_left_eq {p q : Point n} (hx : p.x.val - 1 = q.x.val)
    (hy : p.y.val = q.y.val) (h : 0 < p.x.val) : Adj p q := by
  have e : q = ⟨⟨p.x.val - 1, by omega⟩, p.y⟩ := point_ext hx.symm hy.symm
  rw [e]
  exact adj_left p h

/-- Walk up within a fixed column. -/
theorem col_up {b : Board n} {t : Color} {p₀ : Point n} {x : Fin n}
    (ht : ∀ j : Fin n, b ⟨x, j⟩ = t)
    {a : Fin n} (hc : Connected b t p₀ ⟨x, a⟩) :
    ∀ (k : Nat) (hk : a.val + k < n),
      Connected b t p₀ ⟨x, ⟨a.val + k, hk⟩⟩ := by
  intro k
  induction k with
  | zero => intro _; exact hc
  | succ k ih =>
    intro hk
    have hk1 : a.val + k < n := by omega
    have h1 := ih hk1
    refine Connected.step h1 (adj_up ⟨x, ⟨a.val + k, hk1⟩⟩ (by omega)) ?_
    exact ht ⟨a.val + (k + 1), hk⟩

/-- Walk down within a fixed column. -/
theorem col_down {b : Board n} {t : Color} {p₀ : Point n} {x : Fin n}
    (ht : ∀ j : Fin n, b ⟨x, j⟩ = t)
    {a : Fin n} (hc : Connected b t p₀ ⟨x, a⟩) :
    ∀ (k : Nat) (_hk : k ≤ a.val) (hb : a.val - k < n),
      Connected b t p₀ ⟨x, ⟨a.val - k, hb⟩⟩ := by
  intro k
  induction k with
  | zero => intro _ _; exact hc
  | succ k ih =>
    intro hk hb
    have hk1 : k ≤ a.val := by omega
    have hb1 : a.val - k < n := by omega
    have h1 := ih hk1 hb1
    have hpos : 0 < a.val - k := by omega
    refine Connected.step h1 (adj_down ⟨x, ⟨a.val - k, hb1⟩⟩ hpos) ?_
    exact ht ⟨a.val - (k + 1), hb⟩

/-- Reach any row of a fixed column from any other. -/
theorem col_walk {b : Board n} {t : Color} {p₀ : Point n} {x : Fin n}
    (ht : ∀ j : Fin n, b ⟨x, j⟩ = t)
    {a c : Fin n} (hc : Connected b t p₀ ⟨x, a⟩) :
    Connected b t p₀ ⟨x, c⟩ := by
  by_cases hle : a.val ≤ c.val
  · have hk : a.val + (c.val - a.val) < n := by omega
    have walk := col_up (ht := ht) (hc := hc) (c.val - a.val) hk
    have hp : (⟨x, ⟨a.val + (c.val - a.val), hk⟩⟩ : Point n) = ⟨x, c⟩ :=
      point_ext rfl (by
        show a.val + (c.val - a.val) = c.val
        omega)
    rw [← hp]
    exact walk
  · have hk : c.val ≤ a.val := by omega
    have hb : a.val - (a.val - c.val) < n := by omega
    have walk := col_down (ht := ht) (hc := hc) (a.val - c.val) (by omega) hb
    have hp : (⟨x, ⟨a.val - (a.val - c.val), hb⟩⟩ : Point n) = ⟨x, c⟩ :=
      point_ext rfl (by
        show a.val - (a.val - c.val) = c.val
        omega)
    rw [← hp]
    exact walk

/-! ### 1. captures (test.js §1) -/

/-- W(1,1) is walled in by black; black fills its last liberty at (1,0). -/
def capB : Board 3 := fun p =>
  if isPt p 0 1 || isPt p 2 1 || isPt p 1 2 then .black
  else if isPt p 1 1 then .white
  else .empty

example : place capB (pt 3 1 0) .black (pt 3 1 1) = .empty := by decide
example : place capB (pt 3 1 0) .black (pt 3 1 0) = .black := by decide
example : illegal capB (pt 3 1 0) .black none [] = none := by decide

/-- Chain of three, one shared liberty at (1,0). -/
def cap3B : Board 3 := fun p =>
  if isPt p 0 2 || isPt p 2 1 || isPt p 1 2 then .black
  else if isPt p 0 0 || isPt p 0 1 || isPt p 1 1 then .white
  else .empty

example : place cap3B (pt 3 1 0) .black (pt 3 0 0) = .empty := by decide
example : place cap3B (pt 3 1 0) .black (pt 3 0 1) = .empty := by decide
example : place cap3B (pt 3 1 0) .black (pt 3 1 1) = .empty := by decide
example : place cap3B (pt 3 1 0) .black (pt 3 1 0) = .black := by decide

/-! ### 2. suicide (test.js §2) -/

/-- Same corner: black filling (0,0) would have no liberty and lifts nothing. -/
def suiB : Board 3 := fun p =>
  if isPt p 1 0 || isPt p 0 1 || isPt p 1 2 then .white
  else .empty

example : illegal suiB (pt 3 0 0) .black none [] = some .suicide := by decide

/-- The move captures first — legal, and both whites die. -/
def suiCapB : Board 3 := fun p =>
  if isPt p 1 0 || isPt p 0 1 then .white
  else if isPt p 1 1 || isPt p 2 0 || isPt p 0 2 then .black
  else .empty

example : illegal suiCapB (pt 3 0 0) .black none [] = none := by decide
example : place suiCapB (pt 3 0 0) .black (pt 3 0 0) = .black := by decide
example : place suiCapB (pt 3 0 0) .black (pt 3 1 0) = .empty := by decide
example : place suiCapB (pt 3 0 0) .black (pt 3 0 1) = .empty := by decide

/-! ### 3. board edges (test.js §3) -/

/-- Corner stone dies when the one point it touches is filled. -/
def edgeB : Board 3 := fun p =>
  if isPt p 0 0 then .white
  else if isPt p 0 1 || isPt p 1 1 || isPt p 2 0 then .black
  else .empty

example : illegal edgeB (pt 3 1 0) .black none [] = none := by decide
example : place edgeB (pt 3 1 0) .black (pt 3 0 0) = .empty := by decide

/-- A chain running across the corner: 4 stones, 4 liberties (not 6). -/
def chainB : Board 3 := fun p =>
  if isPt p 0 1 || isPt p 0 0 || isPt p 1 0 || isPt p 1 1 then .white
  else .empty

example : count (chain chainB (pt 3 0 0)) = 4 := by decide
example : libertyCount chainB (chain chainB (pt 3 0 0)) = 4 := by decide

/-! ### 4. ko (test.js §4) -/

/-- White surrounds B(1,1), which has its last liberty at (2,1). The position
    needs column 3 for the supporting black stones, so it lives on 4×4 (the
    local geometry matches test.js's 9×9 corner exactly). -/
def koB : Board 4 := fun p =>
  if isPt p 0 1 || isPt p 1 0 || isPt p 1 2 then .white
  else if isPt p 1 1 || isPt p 2 0 || isPt p 2 2 || isPt p 3 1 then .black
  else .empty

example : illegal koB (pt 4 2 1) .white none [] = none := by decide
example : place koB (pt 4 2 1) .white (pt 4 1 1) = .empty := by decide
example : place koB (pt 4 2 1) .white (pt 4 2 1) = .white := by decide
example : koPoint koB (pt 4 2 1) .white = some (pt 4 1 1) := by decide

/-- The immediate recapture is refused as simple ko. -/
example :
    illegal (place koB (pt 4 2 1) .white) (pt 4 1 1) .black
      (koPoint koB (pt 4 2 1) .white) [] = some .ko := by decide

/-- With the ko point forgotten (a ko threat was answered elsewhere) the
    retake is legal again — and no position repeats. -/
example :
    illegal (place koB (pt 4 2 1) .white) (pt 4 1 1) .black none [] = none := by
  decide

/-! ### 5. positional superko (test.js §5) -/

def superB : Board 3 := fun p =>
  if isPt p 0 0 then .black else if isPt p 1 0 then .white else .empty

example : illegal superB (pt 3 2 0) .black none [] = none := by decide

example :
    illegal superB (pt 3 2 0) .black none [key (place superB (pt 3 2 0) .black)]
      = some .superko := by decide

example :
    key (place superB (pt 3 2 0) .black) ∈
      [key (place superB (pt 3 2 0) .black)] := List.mem_cons_self

/-! ### 7. area scoring (test.js §7) -/

/-- 5×5: column 2 black wall, column 3 white; columns 0–1 black's
    territory (10), column 4 white's (5). test.js expects 15 – 10. -/
def splitB : Board 5 := fun p =>
  if p.x.val = 2 then .black
  else if p.x.val = 3 then .white
  else .empty

/-- Which region an `x`-column of `splitB` belongs to: 0 for columns 0–1,
    1 for column 4, 2 for the non-empty columns. -/
def splitComp (x : Nat) : Nat := if x < 2 then 0 else if x = 4 then 1 else 2

theorem splitComp_zero {x : Nat} : splitComp x = 0 ↔ x < 2 := by
  by_cases h : x < 2 <;> by_cases h4 : x = 4 <;> simp [splitComp, h, h4]

theorem splitComp_one {x : Nat} : splitComp x = 1 ↔ x = 4 := by
  by_cases h : x < 2 <;> by_cases h4 : x = 4 <;> simp [splitComp, h, h4]

theorem splitB_empty_iff {p : Point 5} :
    splitB p = .empty ↔ p.x.val < 2 ∨ p.x.val = 4 := by
  by_cases h2 : p.x.val = 2
  · simp [splitB, h2]
  · by_cases h3 : p.x.val = 3
    · simp [splitB, h3]
    · have hE : splitB p = .empty := by simp [splitB, h2, h3]
      constructor
      · intro
        by_cases hlt : p.x.val < 2
        · exact Or.inl hlt
        · right; omega
      · intro; exact hE

/-- One step along the board keeps `splitB`'s component index stable: a
    neighbour of an empty point is either in the same component or nonempty. -/
theorem splitB_adj_comp {q r : Point 5} (hqr : Adj q r) (hr : splitB r = .empty) :
    splitComp r.x.val ≠ 2 ∧ (splitComp q.x.val ≠ 2 → splitComp r.x.val = splitComp q.x.val) := by
  have hre := splitB_empty_iff.mp hr
  obtain ⟨hb1, hb2⟩ : r.x.val ≤ q.x.val + 1 ∧ q.x.val ≤ r.x.val + 1 := by
    rcases hqr with h | h
    · exact ⟨(mem_neighbours_bounds h).1, (mem_neighbours_bounds h).2.1⟩
    · exact ⟨(mem_neighbours_bounds h).2.1, (mem_neighbours_bounds h).1⟩
  constructor
  · intro h2
    rcases hre with h | h
    · rw [splitComp_zero.mpr h] at h2
      omega
    · rw [splitComp_one.mpr h] at h2
      omega
  · intro hq2
    have hqe : q.x.val < 2 ∨ q.x.val = 4 := by
      by_cases h : q.x.val < 2
      · exact Or.inl h
      · by_cases h4 : q.x.val = 4
        · exact Or.inr h4
        · simp [splitComp, h, h4] at hq2
    rcases hqe with hql | hqh
    · have hrb : r.x.val < 2 := by omega
      rw [splitComp_zero.mpr hrb, splitComp_zero.mpr hql]
    · have hrb : r.x.val = 4 := by omega
      rw [splitComp_one.mpr hrb, splitComp_one.mpr hqh]

/-- Connectivity along `splitB`'s empty points preserves the component. -/
theorem connected_splitB {p q : Point 5} (hp : splitB p = .empty)
    (hc : Connected splitB .empty p q) : splitComp q.x.val = splitComp p.x.val := by
  have hpc : splitComp p.x.val ≠ 2 := by
    rcases splitB_empty_iff.mp hp with h | h
    · simp [splitComp, h]
    · simp [splitComp, h]
  induction hc with
  | seed => rfl
  | step _ hqr hcol ih =>
    have hlocal := splitB_adj_comp hqr hcol
    exact (hlocal.2 (by rw [ih]; exact hpc)).trans ih

/-- The converse: two empty points of the same component are connected —
    walk along the shared column, then at most one step sideways. -/
theorem connected_splitB_of {p q : Point 5} (hp : splitB p = .empty)
    (h : splitComp p.x.val = splitComp q.x.val) : Connected splitB .empty p q := by
  have hpe := splitB_empty_iff.mp hp
  rcases hpe with hpx | hpx
  · have hcp : splitComp p.x.val = 0 := splitComp_zero.mpr hpx
    have hcq : splitComp q.x.val = 0 := by rw [← h]; exact hcp
    have hqx : q.x.val < 2 := splitComp_zero.mp hcq
    have hqE : splitB q = .empty := splitB_empty_iff.mpr (Or.inl hqx)
    have hcol : ∀ j : Fin 5, splitB ⟨p.x, j⟩ = .empty := by
      intro j
      apply splitB_empty_iff.mpr
      left
      simpa using hpx
    have hvert : Connected splitB .empty p ⟨p.x, q.y⟩ :=
      col_walk (ht := hcol)
        (hc := show Connected splitB .empty p ⟨p.x, p.y⟩ from Connected.seed)
    by_cases hlt : p.x.val < q.x.val
    · have h1 : p.x.val + 1 = q.x.val := by omega
      have hb : p.x.val + 1 < 5 := by omega
      have hadj : Adj ⟨p.x, q.y⟩ q := adj_right_eq h1 rfl hb
      refine Connected.step hvert hadj hqE
    · by_cases hlt2 : q.x.val < p.x.val
      · have h3 : p.x.val - 1 = q.x.val := by omega
        have hb : 0 < p.x.val := by omega
        have hadj : Adj ⟨p.x, q.y⟩ q := adj_left_eq h3 rfl hb
        refine Connected.step hvert hadj hqE
      · have hpq : (⟨p.x, q.y⟩ : Point 5) = q :=
          point_ext (by
            show p.x.val = q.x.val
            omega) rfl
        rw [← hpq]
        exact hvert
  · have hcp : splitComp p.x.val = 1 := splitComp_one.mpr hpx
    have hcq : splitComp q.x.val = 1 := by rw [← h]; exact hcp
    have hqx : q.x.val = 4 := splitComp_one.mp hcq
    have hcol : ∀ j : Fin 5, splitB ⟨p.x, j⟩ = .empty := by
      intro j
      apply splitB_empty_iff.mpr
      right
      simpa using hpx
    have hvert : Connected splitB .empty p ⟨p.x, q.y⟩ :=
      col_walk (ht := hcol)
        (hc := show Connected splitB .empty p ⟨p.x, p.y⟩ from Connected.seed)
    have hpq : (⟨p.x, q.y⟩ : Point 5) = q :=
      point_ext (by
        show p.x.val = q.x.val
        omega) rfl
    rw [← hpq]
    exact hvert

/-- The flood fill of an empty point of `splitB` is exactly its component. -/
theorem emptyRegion_splitB {p q : Point 5} (hp : splitB p = .empty) :
    emptyRegion splitB p q = true ↔ splitComp p.x.val = splitComp q.x.val := by
  show fill splitB .empty (5 * 5) (seed p) q = true ↔ _
  rw [fill_iff_connected hp]
  constructor
  · intro h; exact (connected_splitB hp h).symm
  · exact connected_splitB_of hp

/-- The same, as an equality of regions — what the score computation needs. -/
theorem emptyRegion_splitB_eq {p : Point 5} (hp : splitB p = .empty) :
    emptyRegion splitB p =
      (fun q => decide (splitComp p.x.val = splitComp q.x.val)) := by
  funext q
  cases h : emptyRegion splitB p q with
  | true => simp [(emptyRegion_splitB hp).mp h]
  | false =>
    have hne : ¬(splitComp p.x.val = splitComp q.x.val) := by
      intro he
      have h1 := (emptyRegion_splitB hp).mpr he
      rw [h] at h1
      exact Bool.noConfusion h1
    simp [hne]

def splitChar (x : Point 5) : Region 5 :=
  fun q => decide (splitComp x.x.val = splitComp q.x.val)

/-- A bucket whose region is given directly, so it evaluates cheaply. -/
def cheapBucket {n : Nat} (b : Board n) (charP : Point n → Region n)
    (l : Label) (x : Point n) : Bool :=
  decide (b x = .empty) && decide (labelOf b (charP x) = l)

theorem bucket_cheap {n : Nat} (b : Board n) {charP : Point n → Region n}
    (hreg : ∀ x, b x = .empty → emptyRegion b x = charP x)
    (l : Label) (x : Point n) : bucket b l x = cheapBucket b charP l x := by
  by_cases h : b x = .empty
  · simp [bucket, cheapBucket, h, hreg x h]
  · simp [bucket, cheapBucket, h]

theorem terr_splitB_count (l : Label) :
    terr splitB l = List.countP (cheapBucket splitB splitChar l) (allPoints 5) := by
  rw [terr]
  exact countP_congr_of_eq _
    (fun x _ => bucket_cheap _ (fun x hx => emptyRegion_splitB_eq hx) l x)

theorem stones_splitB_black : stones splitB .black = 5 := by decide
theorem stones_splitB_white : stones splitB .white = 5 := by decide
theorem terr_splitB_black : terr splitB .black = 10 := by rw [terr_splitB_count]; decide
theorem terr_splitB_white : terr splitB .white = 5 := by rw [terr_splitB_count]; decide
theorem terr_splitB_neutral : terr splitB .neutral = 0 := by rw [terr_splitB_count]; decide

theorem scoreOn_splitB : scoreOn splitB =
    {stonesBlack := 5, stonesWhite := 5, terrBlack := 10, terrWhite := 5,
     terrNeutral := 0} := by
  simp [scoreOn, stones_splitB_black, stones_splitB_white,
    terr_splitB_black, terr_splitB_white, terr_splitB_neutral]

example : scoreOn splitB =
    {stonesBlack := 5, stonesWhite := 5, terrBlack := 10, terrWhite := 5,
     terrNeutral := 0} := scoreOn_splitB

example : (scoreOn splitB).stonesBlack + (scoreOn splitB).terrBlack = 15 := by
  rw [scoreOn_splitB]; decide
example : (scoreOn splitB).stonesWhite + (scoreOn splitB).terrWhite = 10 := by
  rw [scoreOn_splitB]; decide

example :
    (scoreOn splitB).stonesBlack + (scoreOn splitB).stonesWhite
      + (scoreOn splitB).terrBlack + (scoreOn splitB).terrWhite
      + (scoreOn splitB).terrNeutral = 25 :=
  scoreOn_partition splitB

/-- 3×3 dame: the centre point touches both colours, stays neutral, and the
    board scores 4 – 4 (test.js "dame board"). -/
def dameB : Board 3 := fun p =>
  if isPt p 0 0 || isPt p 0 1 || isPt p 0 2 || isPt p 1 0 then .black
  else if isPt p 2 0 || isPt p 2 1 || isPt p 2 2 || isPt p 1 2 then .white
  else .empty

example : scoreOn dameB =
    {stonesBlack := 4, stonesWhite := 4, terrBlack := 0, terrWhite := 0,
     terrNeutral := 1} := by decide

example : (scoreOn dameB).terrNeutral = 1 := by decide
example : (scoreOn dameB).stonesBlack + (scoreOn dameB).terrBlack = 4 := by decide
example : (scoreOn dameB).stonesWhite + (scoreOn dameB).terrWhite = 4 := by decide

/-- 5×5 lone wall: it owns every empty point around it — 5 stones +
    20 territory (test.js "lone wall owns 20 points"). -/
def loneWall : Board 5 := fun p =>
  if p.x.val = 2 then .black else .empty

/-- Which region an `x`-column of `loneWall` belongs to: 0 for columns 0–1,
    1 for columns 3–4, 2 for the black wall. -/
def loneComp (x : Nat) : Nat := if x < 2 then 0 else if 2 < x then 1 else 2

theorem loneComp_zero {x : Nat} : loneComp x = 0 ↔ x < 2 := by
  by_cases h : x < 2
  · simp [loneComp, h]
  · by_cases h2 : 2 < x
    · simp [loneComp, h, h2]
    · have : x = 2 := by omega
      simp [loneComp, this]

theorem loneComp_one {x : Nat} : loneComp x = 1 ↔ 2 < x := by
  by_cases h : x < 2
  · have hne : ¬(2 < x) := by omega
    simp [loneComp, h, hne]
  · by_cases h2 : 2 < x
    · simp [loneComp, h, h2]
    · have : x = 2 := by omega
      simp [loneComp, this]

theorem loneComp_two {x : Nat} : loneComp x = 2 ↔ x = 2 := by
  by_cases h : x < 2
  · have ne : x ≠ 2 := by omega
    simp [loneComp, h, ne]
  · by_cases h2 : 2 < x
    · have ne : x ≠ 2 := by omega
      simp [loneComp, h, h2, ne]
    · have : x = 2 := by omega
      simp [loneComp, this]

theorem loneWall_empty_iff {p : Point 5} :
    loneWall p = .empty ↔ p.x.val ≠ 2 := by
  by_cases h2 : p.x.val = 2
  · simp [loneWall, h2]
  · simp [loneWall, h2]

/-- One step along the board keeps `loneWall`'s component index stable. -/
theorem loneWall_adj_comp {q r : Point 5} (hqr : Adj q r) (hr : loneWall r = .empty) :
    loneComp r.x.val ≠ 2 ∧ (loneComp q.x.val ≠ 2 → loneComp r.x.val = loneComp q.x.val) := by
  have hre : r.x.val ≠ 2 := loneWall_empty_iff.mp hr
  obtain ⟨hb1, hb2⟩ : r.x.val ≤ q.x.val + 1 ∧ q.x.val ≤ r.x.val + 1 := by
    rcases hqr with h | h
    · exact ⟨(mem_neighbours_bounds h).1, (mem_neighbours_bounds h).2.1⟩
    · exact ⟨(mem_neighbours_bounds h).2.1, (mem_neighbours_bounds h).1⟩
  constructor
  · exact fun h2 => hre (loneComp_two.mp h2)
  · intro hq2
    have hqq : q.x.val ≠ 2 := fun h => hq2 (loneComp_two.mpr h)
    have hqe : q.x.val < 2 ∨ 2 < q.x.val := by omega
    rcases hqe with hql | hqh
    · have hrb : r.x.val < 2 := by omega
      rw [loneComp_zero.mpr hrb, loneComp_zero.mpr hql]
    · have hrb : 2 < r.x.val := by omega
      rw [loneComp_one.mpr hrb, loneComp_one.mpr hqh]

/-- Connectivity along `loneWall`'s empty points preserves the component. -/
theorem connected_loneWall {p q : Point 5} (hp : loneWall p = .empty)
    (hc : Connected loneWall .empty p q) : loneComp q.x.val = loneComp p.x.val := by
  have hpc : loneComp p.x.val ≠ 2 :=
    fun h => loneWall_empty_iff.mp hp (loneComp_two.mp h)
  induction hc with
  | seed => rfl
  | step _ hqr hcol ih =>
    have hlocal := loneWall_adj_comp hqr hcol
    exact (hlocal.2 (by rw [ih]; exact hpc)).trans ih

/-- Two empty points of the same `loneWall` component are connected. -/
theorem connected_loneWall_of {p q : Point 5} (hp : loneWall p = .empty)
    (h : loneComp p.x.val = loneComp q.x.val) : Connected loneWall .empty p q := by
  have hpe : p.x.val ≠ 2 := loneWall_empty_iff.mp hp
  have hpc0 : loneComp p.x.val = 0 ∨ loneComp p.x.val = 1 := by
    by_cases hlt : p.x.val < 2
    · exact Or.inl (loneComp_zero.mpr hlt)
    · exact Or.inr (loneComp_one.mpr (by omega))
  have hcol : ∀ j : Fin 5, loneWall ⟨p.x, j⟩ = .empty := by
    intro j
    apply loneWall_empty_iff.mpr
    simpa using hpe
  have hvert : Connected loneWall .empty p ⟨p.x, q.y⟩ :=
    col_walk (ht := hcol)
      (hc := show Connected loneWall .empty p ⟨p.x, p.y⟩ from Connected.seed)
  rcases hpc0 with hpc | hpc
  · have hqx : q.x.val < 2 :=
      loneComp_zero.mp (by rw [← h]; exact hpc)
    have hpx : p.x.val < 2 := loneComp_zero.mp hpc
    have hqE : loneWall q = .empty := loneWall_empty_iff.mpr (by omega)
    by_cases hlt : p.x.val < q.x.val
    · have h1 : p.x.val + 1 = q.x.val := by omega
      have hb : p.x.val + 1 < 5 := by omega
      have hadj : Adj ⟨p.x, q.y⟩ q := adj_right_eq h1 rfl hb
      refine Connected.step hvert hadj hqE
    · by_cases hlt2 : q.x.val < p.x.val
      · have h3 : p.x.val - 1 = q.x.val := by omega
        have hb : 0 < p.x.val := by omega
        have hadj : Adj ⟨p.x, q.y⟩ q := adj_left_eq h3 rfl hb
        refine Connected.step hvert hadj hqE
      · have hpq : (⟨p.x, q.y⟩ : Point 5) = q :=
          point_ext (by
            show p.x.val = q.x.val
            omega) rfl
        rw [← hpq]
        exact hvert
  · have hqx : 2 < q.x.val :=
      loneComp_one.mp (by rw [← h]; exact hpc)
    have hpx : 2 < p.x.val := loneComp_one.mp hpc
    have hqE : loneWall q = .empty := loneWall_empty_iff.mpr (by omega)
    by_cases hlt : p.x.val < q.x.val
    · have h1 : p.x.val + 1 = q.x.val := by omega
      have hb : p.x.val + 1 < 5 := by omega
      have hadj : Adj ⟨p.x, q.y⟩ q := adj_right_eq h1 rfl hb
      refine Connected.step hvert hadj hqE
    · by_cases hlt2 : q.x.val < p.x.val
      · have h3 : p.x.val - 1 = q.x.val := by omega
        have hb : 0 < p.x.val := by omega
        have hadj : Adj ⟨p.x, q.y⟩ q := adj_left_eq h3 rfl hb
        refine Connected.step hvert hadj hqE
      · have hpq : (⟨p.x, q.y⟩ : Point 5) = q :=
          point_ext (by
            show p.x.val = q.x.val
            omega) rfl
        rw [← hpq]
        exact hvert

/-- The flood fill of an empty point of `loneWall` is exactly its component. -/
theorem emptyRegion_loneWall {p q : Point 5} (hp : loneWall p = .empty) :
    emptyRegion loneWall p q = true ↔ loneComp p.x.val = loneComp q.x.val := by
  show fill loneWall .empty (5 * 5) (seed p) q = true ↔ _
  rw [fill_iff_connected hp]
  constructor
  · intro h; exact (connected_loneWall hp h).symm
  · exact connected_loneWall_of hp

theorem emptyRegion_loneWall_eq {p : Point 5} (hp : loneWall p = .empty) :
    emptyRegion loneWall p =
      (fun q => decide (loneComp p.x.val = loneComp q.x.val)) := by
  funext q
  cases h : emptyRegion loneWall p q with
  | true => simp [(emptyRegion_loneWall hp).mp h]
  | false =>
    have hne : ¬(loneComp p.x.val = loneComp q.x.val) := by
      intro he
      have h1 := (emptyRegion_loneWall hp).mpr he
      rw [h] at h1
      exact Bool.noConfusion h1
    simp [hne]

def loneChar (x : Point 5) : Region 5 :=
  fun q => decide (loneComp x.x.val = loneComp q.x.val)

theorem terr_loneWall_count (l : Label) :
    terr loneWall l = List.countP (cheapBucket loneWall loneChar l) (allPoints 5) := by
  rw [terr]
  exact countP_congr_of_eq _
    (fun x _ => bucket_cheap _ (fun x hx => emptyRegion_loneWall_eq hx) l x)

theorem stones_loneWall_black : stones loneWall .black = 5 := by decide
theorem stones_loneWall_white : stones loneWall .white = 0 := by decide
theorem terr_loneWall_black : terr loneWall .black = 20 := by rw [terr_loneWall_count]; decide
theorem terr_loneWall_white : terr loneWall .white = 0 := by rw [terr_loneWall_count]; decide
theorem terr_loneWall_neutral : terr loneWall .neutral = 0 := by rw [terr_loneWall_count]; decide

theorem scoreOn_loneWall : scoreOn loneWall =
    {stonesBlack := 5, stonesWhite := 0, terrBlack := 20, terrWhite := 0,
     terrNeutral := 0} := by
  simp [scoreOn, stones_loneWall_black, stones_loneWall_white,
    terr_loneWall_black, terr_loneWall_white, terr_loneWall_neutral]

example : scoreOn loneWall =
    {stonesBlack := 5, stonesWhite := 0, terrBlack := 20, terrWhite := 0,
     terrNeutral := 0} := scoreOn_loneWall

/-! ### 8. handicap (test.js §8) -/

/-- go.html's star-point layout, per board size; other sizes have none. -/
def handicapLayout (n : Nat) : List (Nat × Nat) :=
  if n = 9 then [(2, 6), (6, 6), (2, 2), (6, 2), (4, 4)]
  else if n = 13 then
    [(3, 9), (9, 9), (3, 3), (9, 3), (6, 6), (3, 6), (9, 6), (6, 9), (6, 3)]
  else if n = 19 then
    [(3, 15), (15, 15), (3, 3), (15, 3), (9, 9), (3, 9), (15, 9), (9, 15), (9, 3)]
  else []

/-- Every star-point list has distinct points, so handicap stones never
    collide (test.js "handicap stones sit on star points"). -/
theorem handicap_distinct (n : Nat) : List.Nodup (handicapLayout n) := by
  by_cases h : n = 9
  · subst h; simp [handicapLayout]
  · by_cases h2 : n = 13
    · subst h2; simp [handicapLayout]
    · by_cases h3 : n = 19
      · subst h3; simp [handicapLayout]
      · simp [handicapLayout, h, h2, h3]

/-- Any number of handicap stones (a prefix of the layout) stays distinct. -/
theorem handicap_stones_distinct (n k : Nat) :
    List.Nodup ((handicapLayout n).take k) :=
  List.Sublist.nodup (List.take_sublist k (handicapLayout n)) (handicap_distinct n)

/-- A 9×9 has exactly five handicap points, a 13×13 and 19×19 nine — the
    clamp `Math.min(handicap, layout.length)` in go.html. -/
example : (handicapLayout 9).length = 5 := by decide
example : (handicapLayout 13).length = 9 := by decide
example : (handicapLayout 19).length = 9 := by decide
example : handicapLayout 7 = [] := by decide

end Go
