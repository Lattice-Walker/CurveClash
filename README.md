CORRECTED VERSION

# Curve Clash

[Curve Clash](https://lattice-walker.github.io/CurveClash/) is a static, zero-build 2D equation battle game made with HTML, CSS, Canvas, and vanilla JavaScript. Math expressions are parsed by math.js and rendered with KaTeX. There is no Node runtime, application server, API, or backend.

## Equation input

- Type only the right-hand expression; the purple `f(x)` box and adjacent `=` are supplied by the interface.
- Accepted: `x^2 - x`, `0.5 * x`, `2 * sin(x / 1.5)`, `2 * ln(x + 1)`, `exp(x / 3) - 1`
- Rejected: functions that are not 0 at `x = 0` such as `x^2 + 1` or `x^2 - 1`, `min()`, `max()` or `abs()`, expressions using `y`, and implicit equations such as `x^2 + y^2 = 1`

`ln()` is accepted as an exact synonym for the natural logarithm, which math.js itself spells `log()`; `log10()`, `log2()`, `exp()`, and a constant base such as `2^x` are available too. Because every shot must pass through `y = 0` at `x = 0`, a bare exponential is refused: `exp(x)` is never zero, so subtract its value at the origin and fire `exp(x / 3) - 1` instead.

### Units

One unit on the local axes equals 50 canvas pixels, so the medium arena is about 24 by 14 units, and the roster lists every opponent in those same units. Because `f(x)` is evaluated against raw pixels, standard mathematical functions would be unusable at map scale: `ln(x)` climbs about seven pixels across an entire arena, and `exp(x)` turns vertical within seven pixels of the shooter, so both would draw as straight lines without scaling. On a 50-pixel unit, `x^2 - 1`, `sin(x)`, `ln(x)`, and `exp(x) - 1` all draw their familiar shapes at arena scale. Only the local mathematical frame is scaled; canvas, terrain, craters, hitboxes, and scoring remain in pixels throughout.

A curve does not have to start at the shooter. Walking outward along the graph in each direction, the first stretch that lies inside the arena is the shot, so a function with a vertical asymptote at the shooter (`ln(x)` is a typical case) enters from the map edge and traces normally.

Only `x` may vary, and the function must equal `y = 0` at `x = 0`, the firing player's position. Coordinates use the firing player's position as the local `(0,0)`, with positive `y` pointing upward and one unit spanning 50 pixels. In Live Visualizer mode, dashed curves are previews only; they cannot eliminate players or change terrain.

## Structure

- `index.html`: configuration, game HUD, and dialogs
- `styles.css`: responsive pastel/dark visual system
- `app.js`: game state, turns, bots, animation, and Canvas rendering
- `src/equation-engine.js`: strict function parsing, sampling, collision, and bot equations
- `src/bot-planner.js`: terrain-aware bot routing, smooth harmonic curves, exact hinge splines, and difficulty deformation
- `src/beam.js`: shared tapered-beam hit geometry and obstacle-occlusion checks
- `src/powerups.js`: buried shield/beam placement, exposure, and pickup detection
- `src/scoring.js`: obstacle-weighted kill values, multi-kill bonuses, and deterministic ranking
- `src/obstacle-field.js`: mutable pixel-grid terrain and circular craters

## Turn order

The human player always fires first, before any bot. Only the bot slots are shuffled, and that order stays fixed for the whole match. Every human curve resolves against the terrain exactly as it stood at the start of the turn, and the same order breaks final ranking ties after kills and survival.

## Bot behavior

Competitive bots each pick a random surviving opponent, human or bot, and plan a terrain-aware route to it at the configured accuracy.

Peaceful bots never fire at all. The human is the only player who shoots. Peaceful bots still occupy the arena, still block and absorb curves, and remain fully eliminable targets worth their normal score, so a peaceful match still requires the human to eliminate opponents rather than simply waiting out the round limit. They are listed in the turn order as "holds fire" and are omitted from the equation reveal and the submission count.

## Buried power-ups

Each match contains exactly one shield and one beam, visibly embedded deep inside obstacles. Their solid burial depth is greater than the largest possible single crater, and distinct-shot tracking prevents two impacts from the same equation from counting as two moves. A cache therefore requires at least two official shots to expose and collect. The shooter who completes that breach wins the item.

- The shield absorbs one official hit. It persists across turns and disappears only when it actually blocks a hit; that contact awards no kill or points.
- The beam persists for its owner and wraps future centerlines in a tapered cone. It begins narrow and widens with traveled distance. The centerline still stops at the first obstacle, and lateral beam contacts cannot pass through solid terrain.

## Replay

The final ranking screen includes a "View replay" option. Replay restores the starting arena and plays the official shots in their original order, including beam width, shield blocks, eliminations, pickups, and the exact crater radii that occurred. It uses an in-memory event log and remains entirely client-side; it does not recompute bot decisions or contact outcomes. Selecting "Back to results" can stop playback at any point and restores the exact final state.

## Scoring and ranking

A kill's base value is the straight-line distance from shooter to target plus the length of that same segment lying inside obstacles. Clear distance counts once, and blocked distance counts twice. The calculation walks the authoritative pixel grid before the current shot creates any craters.

For a multi-kill, base values are sorted from smallest to largest and receive increasing multipliers. Three values `x < y < z` therefore award `x × 1 + y × 2 + z × 3`.

Whoever is still standing when the match ends, whether player or bot, collects a survival bonus of 1000 × √R, where `R` is the number of rounds the match lasted. It is paid once, only when exactly one player is left, so a round that ends with everyone eliminated pays nobody.

| Rounds | 1 | 2 | 3 | 4 | 6 | 8 | 12 | 16 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Bonus | 1000 | 1414 | 1732 | 2000 | 2449 | 2828 | 3464 | 4000 |

The square root, rather than a linear payout, keeps the bonus comparable in magnitude to a handful of kills regardless of how long the match runs. A linear bonus would reach 10,000 points by round ten, reducing the incentive to shoot. The square-root formula also reduces the benefit of stalling: each additional round is worth `500 / √R`, so from the second round onward, waiting yields less value than landing a kill. This effect is most relevant against peaceful bots, where the match only ends when the human shoots.

The live roster is ordered by score, and the final winner is the top-ranked player, even if that player was eliminated, since the bonus is large but not unbeatable. Ties are resolved by kills, survival, then the fixed turn order.

## Terrain-aware bots

Bots do not aim as if the arena were empty. Every unperturbed shot is first traced through the authoritative obstacle grid. If the direct, parabolic, and cubic families are blocked, a monotone-x route search finds a free corridor, adds obstacle clearance, simplifies the route, and converts it into either a smooth harmonic function or an exact piecewise-linear hinge function. The result is accepted only after the normal production collision engine proves that it reaches the selected target.

Difficulty is applied after that verified equation has been selected, so changing accuracy never changes the bot's intended strategy. If no graph of an `f(x)` function can cross the terrain, such as a solid wall spanning the whole map, the bot deliberately strikes the best obstruction point. Its crater changes the collision grid, and the next turn replans against the opening.


