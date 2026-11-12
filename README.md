# shanten

Replaceable Go shanten calculator contract, version `aka37-shanten/v1`.
This module contains types, an interface, and error categories only.
There is no calculator, adapter, registry, dynamic loader, or validation algorithm.
It depends only on the Go standard library, not on the parent aka37 module.

The Lean4-first verification and Go implementation plan is documented in
[docs/SHANTEN_LEAN4_PLAN.md](docs/SHANTEN_LEAN4_PLAN.md).

## Input

`Calculator.Calculate(Input) (Result, error)` accepts standing tiles and fixed
melds. Each meld includes its kind and all its tiles, including all four tiles
of a kan. An ankan is a fixed meld even though it preserves menzen status.
Call source, called-tile position, discards, and visible tiles are not inputs.

`Counts37` is a fixed `[37]int`; invalid lengths are unrepresentable.
Its indices and capacities are:

| Indices | Tiles | Capacity per kind |
| --- | --- | --- |
| 0, 10, 20 | Red 5m, 5p, 5s | 1 |
| 1..9 | Normal 1m..9m | 3 for 5m, otherwise 4 |
| 11..19 | Normal 1p..9p | 3 for 5p, otherwise 4 |
| 21..29 | Normal 1s..9s | 3 for 5s, otherwise 4 |
| 30..36 | East, South, West, North, White, Green, Red | 4 |

Counts must be nonnegative and respect these capacities across standing tiles
and all melds combined. The adapter merges red fives into ordinary fives for
calculation; it must not change the source input or shanten meaning.

With `m = len(Melds)`, `0 <= m <= 4`, the standing tile count must be either
`13 - 3*m` or `14 - 3*m`. Each chi is three consecutive ranks in one numbered
suit; each pon is three identical kinds; each kan is four identical kinds,
after merging red fives. Each kan counts as one fixed set. Added kans replace
their original pon, rather than adding another meld. Pre-rinshan transient states
are not separately distinguished; only the supplied tile composition is evaluated.

## Result

Tenpai is `0`, completion is `-1`, and all applicable shanten values are at least
`-1`. `Standard` is always applicable.

`SevenPairs.Applicable` and `ThirteenOrphans.Applicable` are true exactly when
there are no fixed melds. If false, their `Shanten` field must be zero and must
not participate in the minimum. Thus ankan also disables both special shapes.
With no fixed melds, `Shanten` is the minimum of all three shapes; otherwise it
equals `Standard`. Inapplicability is not a backend capability failure.
An implementation unable to evaluate an applicable shape must return an error.

Shanten is structural: do not impose yaku, furiten, visible-tile availability,
or nagashi-mangan conditions.

## Errors and ownership

The calculator or adapter validates counts, meld structure, and hand size before
delegation, and checks backend results against this contract.
Return a zero `Result` with a non-nil error on failure; callers must ignore the
result whenever the error is non-nil. Do not normalize invalid inputs.

Wrap the exported sentinel errors with context using `%w`, preserving
`errors.Is`. Use `ErrInvalidCount` for negative counts or exceeded capacities,
`ErrInvalidHand` for inconsistent hand size or too many melds, `ErrInvalidMeld`
for unknown kinds or invalid meld composition, `ErrUnsupported` for missing
calculator capabilities, `ErrBackend` for execution failures, and
`ErrInvalidResult` for backend output that violates the result contract.
Error text must identify the offending field or backend operation when known.

Results must be deterministic. Do not mutate input or retain its slices for later
use. Callers must not mutate input during a call. Shared-instance concurrency
safety is not promised by v1; future parallel callers must use separate instances
unless the implementation explicitly guarantees concurrent use.

## Integration

The module is intended to be referenced from aka37 at `modules/shanten` as a Git
submodule. Clone/update it with `git submodule update --init --recursive`.
Git submodules pin source commits; they do not add Go `require` or `replace`
directives. Consumers can depend on `github.com/bgnori/shanten` at a chosen
module version. The parent does not import it until an adapter is implemented.
The source repository is public; no private-module Go configuration is required.

The host supplies a `Calculator` instance to its consumers. Backend-specific
types and errors remain behind the adapter. There is no Go `plugin` ABI or
general analysis registry in this contract. Future analysis modules can follow
this pattern with their own typed contracts.

Breaking changes to input meaning, result meaning, or interface signatures
require a new contract version and appropriate Go module versioning.

## Checks

```sh
go test ./...
go vet ./...
```

These compile/check the contract only; numerical conformance tests belong to a
future calculator or adapter implementation.
