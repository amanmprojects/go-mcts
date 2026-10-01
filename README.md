# go-mcts

Go (the board game) with Chinese rules and a Monte-Carlo tree search opponent, in one
HTML file with no dependencies and no build step.

Open `go.html` in a browser. That is the whole install.

```
xdg-open go.html      # or just double-click it
```

Play against a person, or set **Opponent** to *Bot plays White*, *Bot plays Black*, or
*Bot plays both* and press **Restart**.

## What is implemented

Rules, under Chinese (area) scoring:

- Board sizes 9×9, 13×13, 19×19.
- Area scoring, default komi 5.5 on 9×9 and 7.5 on 13×13 and 19×19, editable.
- Captures, suicide forbidden, simple ko, and positional superko (a position may not
  recur, not just the last one).
- Handicap stones from 2 to 9, placed on the traditional points, which differ by board
  size — a 9×9 has only five handicap points and the menu clamps to that.
- Seki counts for both sides. Dead stones are marked by clicking during scoring; the
  click works on whole chains, since marking part of a chain is not a real thing.
- SGF export (FF[4]), including handicap as `AB` setup stones and passes as empty
  values.

Interface:

- Undo takes back both sides of a bot reply, so one keypress rewinds a full exchange.
  Right-clicking the board does the same.
- Clicking an earlier move in the move list shows the board as it was then, without
  changing the game; click it again to come back to the live position.
- `u` undo, `p` pass, `Enter` count score, `Escape` back out of scoring or review.
- Resign, and a score breakdown showing stones, territory, and neutral points
  separately.

## The bot

Monte-Carlo tree search. It plays games to the end from each candidate move and plays
the one that wins most often. It knows about a dozen local rules and nothing else.

One iteration: walk down the tree picking children by UCT (win rate plus
`c·√(ln(visits)/visits)`, `c` from 0.8 to 1.5 by difficulty), expanding one untried
child when it reaches one, then simulate a whole game from the bottom, score it by
area, squash the margin into 0–1, and add that to every node on the path back to the
root. The tree survives between moves and is re-rooted onto the move actually played.

The playout policy is what keeps the simulations from being noise. At each step it
samples 4 empty points, scores each one, and takes the best:

| Situation | Score |
| --- | --- |
| fills a real eye (all neighbours are your own stones) | −400 |
| plays inside its own area, no enemy contact | −260 |
| walks into self-atari (1 liberty) | −200 |
| leaves only 2 liberties | −10 |
| captures | +40, plus 15 per stone |
| saves a friendly group in atari | +440 |
| puts an enemy group in atari | +30 |
| random jitter | 0–25 |

If the best of the 4 samples scores below −120 it passes instead, which is how
playouts end on a settled position rather than running to the ply limit. Without that
threshold, 119 of 120 playouts hit the cap.

The root is handled differently from the rest of the tree. On an empty board the
candidates are star points and their neighbours — where a human opens — and after
that only points adjacent to an existing stone, capped at 40. The cap matters: with 82
candidates each move got about two playouts and the choice was noise. Pass is not
offered at the root until the board has at least one stone per line.

Three difficulties, all wall-clock budgets rather than search depths:

| | Time | Minimum playouts | c |
| --- | --- | --- | --- |
| Casual | 0.7 s | 120 | 1.5 |
| Strong | 2.2 s | 400 | 1.0 |
| Best | 6.0 s | 900 | 0.8 |

The search is single-threaded, so a bigger board means fewer playouts per move, not a
better search. Measured cost of one playout: 0.26 ms on 9×9, 0.48 ms on 13×13, 1.07 ms
on 19×19.

## Tests

```
node test.js
```

112 assertions, no dependencies, no test framework. `harness.js` stubs the ~15 DOM
calls the page needs, loads the real `go.html` through `vm`, and exports the engine
internals, so the tests run the shipping code rather than a copy of it.

Covered: captures, suicide, edge and corner chains, ko including a retake after a
threat, positional superko, pass/undo/review including the cases that used to crash,
area scoring against hand-built positions (each one also checked for the invariant
`stones + territory + neutral = N²`), handicap layouts on all three board sizes, SGF
structure, 500 random self-play moves, and the bot — playout termination, a whole
bot-vs-bot game, and that searching leaves the real board untouched.

### Why the harness stubs `performance.now`

`botTick` loops until `performance.now()` passes its budget. The stub originally
returned a constant, so any test that switched the bot on spun in that loop forever.
It now returns real time.

## Formal verification

`lean/` contains a Lean 4 (v4.34.1, no Mathlib) formalization of the rules engine.
Everything in `go.html`'s kernel has a counterpart: points and adjacency, flood-fill
regions as an inductive `Connected` relation, groups, liberties, captures, the
suicide/ko/superko checks in `illegal`, and Chinese area scoring with the partition
invariant `stones + territory + neutral = N²` (`scoreOn_partition`). No `sorry`, no
`native_decide`; the only axioms used are Lean's standard three.

`GoRules/Examples.lean` restates the positions `test.js` checks — captures, chains,
suicide, ko, superko, the 3×3 dame board, handicap layout distinctness — and proves
the two 5×5 scores structurally rather than by evaluation: the split board
(5–5 stones, 10/5/0 territory) and the lone wall (5 stones, 20 territory). Each
region of those boards is characterised as a set of columns, and only the final
cheap count is evaluated.

```
cd lean && lake build
```

## Files

| | |
| --- | --- |
| `go.html` | The game and the bot. No dependencies, no build. |
| `harness.js` | Loads `go.html` headlessly and exposes the engine to tests. |
| `test.js` | The test suite. |
| `lean/` | Lean 4 formalization of the rules engine (`lake build`). |

## Known limits

- The bot has no opening book, no endgame solver, and no knowledge beyond the table
  above. On 13×13 it will occasionally pass around move 3, which costs a tempo.
- It has no measured strength. Openings on 9×9 and 19×19 look like real Go — star
  point, 3-4, contact — but that is an inspection of the moves it plays, not a win rate
  against a human or another engine.
- Handicap games place the stones correctly but the bot does not play a different
  style for them.
- The board is not drawn for touch input beyond what a click gives you; there is no
  drag-to-stone gesture.
