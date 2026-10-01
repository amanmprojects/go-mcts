import GoRules.Board

/-!
# Go — flood fill and connectivity

The heart of the rules engine: chains of same-coloured stones and maximal
empty regions, computed by bounded expansion. `fill` with `n²` rounds is
proven equivalent to graph connectivity: sound (`fill_connected`) and
complete (`connected_fill`).

go.html computes the same thing with a worklist flood fill in `group()`;
this model states the spec directly, so the theorems are about the spec,
not about the loop bookkeeping.
-/

namespace Go

/-- A set of points, as a characteristic function. -/
abbrev Region (n : Nat) := Point n → Bool

/-- The one-point region containing `p`. -/
def seed (p : Point n) : Region n := fun q => decide (q = p)

/-- One expansion round: keep the current set, and add every point of colour
    `t` that touches it. Both adjacency orientations are checked, since
    connectivity does not depend on the order `neighbours` lists things. -/
def expand (b : Board n) (t : Color) (S : Region n) : Region n :=
  fun r => S r || (decide (b r = t) &&
    ((neighbours r).any S ||
      (allPoints n).any fun s => S s && decide (r ∈ neighbours s)))

/-- `fuel` rounds of expansion. -/
def fill (b : Board n) (t : Color) : Nat → Region n → Region n
  | 0, S => S
  | k + 1, S => expand b t (fill b t k S)

/-- The chain of same-coloured stones containing `p`. -/
def chain (b : Board n) (p : Point n) : Region n := fill b (b p) (n * n) (seed p)

/-- The maximal empty region containing `p` — go.html's territory regions. -/
def emptyRegion (b : Board n) (p : Point n) : Region n := fill b .empty (n * n) (seed p)

/-! ### Basic fill lemmas -/

theorem seed_mem (p : Point n) : seed p p = true := by simp [seed]

theorem expand_mono {S : Region n} {r : Point n} (h : S r = true) :
    expand b t S r = true := by simp [expand, h]

theorem fill_mono {S : Region n} {k : Nat} {r : Point n}
    (h : fill b t k S r = true) : fill b t (k + 1) S r = true := by
  simpa [fill] using expand_mono h

theorem fill_mono_le {S : Region n} {k k' : Nat} (hk : k ≤ k') {r : Point n}
    (h : fill b t k S r = true) : fill b t k' S r = true := by
  induction hk with
  | refl => exact h
  | step _ ih => exact fill_mono ih

/-- Fill only ever contains points of the target colour — when the seed is
    that colour. -/
theorem fill_color {p₀ : Point n} (hseed : b p₀ = t) {k : Nat} {r : Point n}
    (h : fill b t k (seed p₀) r = true) : b r = t := by
  induction k generalizing r with
  | zero =>
    simp [fill, seed] at h
    subst h
    exact hseed
  | succ k ih =>
    have h' : expand b t (fill b t k (seed p₀)) r = true := by simpa [fill] using h
    simp only [expand, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff] at h'
    rcases h' with h' | ⟨hb, _⟩
    · exact ih h'
    · exact hb

/-! ### Connectivity spec -/

/-- Graph reachability from `p₀` along points of colour `t`: the spec that
    `fill` computes. -/
inductive Connected (b : Board n) (t : Color) (p₀ : Point n) : Point n → Prop
  | seed : Connected b t p₀ p₀
  | step {q r : Point n} : Connected b t p₀ q → Adj q r → b r = t → Connected b t p₀ r

/-- Soundness: everything in the fill is connected to the seed. -/
theorem fill_connected {p₀ : Point n} (hseed : b p₀ = t) {k : Nat} {q : Point n}
    (h : fill b t k (seed p₀) q = true) : Connected b t p₀ q := by
  induction k generalizing q with
  | zero =>
    simp [fill, seed] at h
    subst h
    exact Connected.seed
  | succ k ih =>
    have h' : expand b t (fill b t k (seed p₀)) q = true := by simpa [fill] using h
    simp only [expand, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff] at h'
    rcases h' with h' | ⟨hb, han⟩
    · exact ih h'
    · have hex : ∃ s, fill b t k (seed p₀) s = true ∧ Adj s q := by
        rcases han with h1 | h2
        · obtain ⟨s, hsq, hs⟩ := List.any_eq_true.mp h1
          exact ⟨s, hs, Or.inr hsq⟩
        · obtain ⟨s, _, hs⟩ := List.any_eq_true.mp h2
          have ⟨hfill, hadj⟩ :
              fill b t k (seed p₀) s = true ∧ q ∈ neighbours s := by
            simpa using hs
          exact ⟨s, hfill, Or.inl hadj⟩
      obtain ⟨s, hs, hadj⟩ := hex
      exact Connected.step (ih hs) hadj hb

/-! ### Counting points of a region -/

theorem countP_le_length (f : α → Bool) (xs : List α) :
    List.countP f xs ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    cases hf : f a <;> simp [hf, List.length_cons] <;> omega

theorem countP_mono {f g : α → Bool} (h : ∀ x, f x = true → g x = true)
    (xs : List α) : List.countP f xs ≤ List.countP g xs := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    cases hf : f a
    · cases hg : g a <;> simp [hf, hg] <;> omega
    · have hg : g a = true := h a (by simp [hf])
      simp [hf, hg] <;> omega

theorem countP_strict {f g : α → Bool} (hmono : ∀ x, f x = true → g x = true)
    {xs : List α} {x : α} (hxs : x ∈ xs) (hg : g x = true) (hf : f x = false) :
    List.countP f xs < List.countP g xs := by
  induction xs with
  | nil => cases hxs
  | cons a as ih =>
    rcases List.mem_cons.mp hxs with rfl | htail
    · have m := countP_mono (fun y hy => hmono y hy) as
      simp [hf, hg]
      omega
    · have ih' := ih htail
      cases ha : f a
      · cases ha2 : g a <;> simp [ha, ha2] <;> omega
      · have hg' : g a = true := hmono a (by simp [ha])
        simp [ha, hg']
        omega

theorem countP_one_of_mem {f : α → Bool} {xs : List α} {x : α}
    (hx : x ∈ xs) (hf : f x = true) : 1 ≤ List.countP f xs := by
  induction xs with
  | nil => cases hx
  | cons a as ih =>
    rcases List.mem_cons.mp hx with rfl | htail
    · simp [hf]
    · have ih' := ih htail
      cases ha : f a <;> simp only [List.countP_cons, ha] <;> omega

/-- How many board points are in `S`. -/
def count {n : Nat} (S : Region n) : Nat := List.countP S (allPoints n)

theorem count_le (S : Region n) : count S ≤ n * n := by
  have := countP_le_length S (allPoints n)
  simpa [count, length_allPoints] using this

theorem count_seed_pos {p₀ : Point n} : 1 ≤ count (seed p₀) :=
  countP_one_of_mem (mem_allPoints p₀) (by simp [seed])

/-- One more round that adds anything strictly increases the count. -/
theorem expand_count_lt {S : Region n} (hne : expand b t S ≠ S) :
    count S < count (expand b t S) := by
  have hex : ∃ r, expand b t S r = true ∧ S r = false := by
    apply Classical.byContradiction
    intro h
    apply hne
    funext r
    cases he : expand b t S r
    · cases hs : S r
      · rfl
      · exact absurd (expand_mono (b := b) (t := t) (S := S) (r := r) hs)
          (by simp [he])
    · cases hs : S r
      · exact absurd ⟨r, he, hs⟩ h
      · rfl
  obtain ⟨r, hTr, hSr⟩ := hex
  exact countP_strict (fun x hx => expand_mono (b := b) (t := t) (r := x) hx)
    (mem_allPoints r) hTr hSr

/-- The expansion has reached a fixed point by round `n²`: growth cannot
    continue for n² rounds without exceeding the board. -/
theorem fill_fixed (b : Board n) (t : Color) (p₀ : Point n) :
    expand b t (fill b t (n * n) (seed p₀)) = fill b t (n * n) (seed p₀) := by
  have key : ∀ k, k ≤ n * n →
      expand b t (fill b t k (seed p₀)) = fill b t k (seed p₀) ∨
      count (seed p₀) + k ≤ count (fill b t k (seed p₀)) := by
    intro k
    induction k with
    | zero => intro _; right; simp [fill]
    | succ k ih =>
      intro hk
      rcases ih (Nat.le_of_succ_le hk) with hf | hc
      · left
        have e : fill b t (k + 1) (seed p₀) = fill b t k (seed p₀) := by
          simp [fill, hf]
        rw [e]
        exact hf
      · rcases Classical.em (expand b t (fill b t k (seed p₀)) =
            fill b t k (seed p₀)) with hf | hne
        · left
          have e : fill b t (k + 1) (seed p₀) = fill b t k (seed p₀) := by
            simp [fill, hf]
          rw [e]
          exact hf
        · right
          have lt := expand_count_lt (b := b) (t := t)
            (S := fill b t k (seed p₀)) hne
          simp only [fill] at lt ⊢
          omega
  rcases key (n * n) (Nat.le_refl _) with hf | hge
  · exact hf
  · have hle := count_le (fill b t (n * n) (seed p₀))
    have h1 : 1 ≤ count (seed p₀) := count_seed_pos
    have : False := by omega
    exact this.elim

/-- Completeness: everything connected to the seed is in the fill at fuel
    n² — the fill never misses a same-coloured neighbour. -/
theorem connected_fill {p₀ q : Point n} (_hseed : b p₀ = t)
    (hc : Connected b t p₀ q) : fill b t (n * n) (seed p₀) q = true := by
  have hf := fill_fixed b t p₀
  have hstable : fill b t (n * n + 1) (seed p₀) = fill b t (n * n) (seed p₀) := by
    simp [fill, hf]
  induction hc
  case seed => exact fill_mono_le (Nat.zero_le _) (seed_mem p₀)
  case step q r hq hqr hrt ih =>
    have h1 : fill b t (n * n) (seed p₀) q = true := ih
    have he : expand b t (fill b t (n * n) (seed p₀)) r = true := by
      simp only [expand, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff]
      refine Or.inr ⟨hrt, ?_⟩
      rcases hqr with h | h
      · exact Or.inr (List.any_eq_true.mpr ⟨q, mem_allPoints q, by simp [h1, h]⟩)
      · exact Or.inl (List.any_eq_true.mpr ⟨q, h, by simp [h1]⟩)
    have h2 : fill b t (n * n + 1) (seed p₀) r = true := by
      simpa [fill] using he
    simpa [← hstable] using h2

/-- The flood fill computes exactly graph connectivity: `fill` and
    `Connected` agree at fuel n². -/
theorem fill_iff_connected {p₀ q : Point n} (hseed : b p₀ = t) :
    fill b t (n * n) (seed p₀) q = true ↔ Connected b t p₀ q :=
  ⟨fill_connected hseed, connected_fill hseed⟩

end Go
