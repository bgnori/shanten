// Package shanten defines the contract for replaceable shanten calculators.
// It does not provide a calculator implementation.
package shanten

import "errors"

const ContractVersion = "aka37-shanten/v2"

// Counts37 preserves aka-five identity in aka37 Int37 order.
type Counts37 [37]int

type MeldKind string

const (
	Chi       MeldKind = "chi"
	Pon       MeldKind = "pon"
	Ankan     MeldKind = "ankan"
	Daiminkan MeldKind = "daiminkan"
	Kakan     MeldKind = "kakan"
)

// Meld represents one fixed set. Kakan includes all four tiles, not a separate pon.
type Meld struct {
	Kind  MeldKind
	Tiles Counts37
}

type Input struct {
	// Standing excludes every tile in Melds, including concealed kans.
	Standing Counts37
	Melds    []Meld
}

// ShapeResult is inapplicable only when fixed melds prevent the hand shape.
// Shanten must be zero when Applicable is false and is otherwise at least -1.
type ShapeResult struct {
	Shanten    int
	Applicable bool
}

type Result struct {
	MentsuHand          int
	SevenPairs      ShapeResult
	ThirteenOrphans ShapeResult
	// Shanten is the minimum over MentsuHand and applicable special shapes.
	Shanten int
}

// Calculator must not mutate input. Callers must not mutate it during Calculate.
// Concurrent calls on one instance require an implementation-specific guarantee.
type Calculator interface {
	Calculate(Input) (Result, error)
}

// Implementations wrap these errors with input locations or backend context.
// Callers classify errors using errors.Is, never error message text.
var (
	ErrInvalidCount  = errors.New("shanten: invalid tile count")
	ErrInvalidHand   = errors.New("shanten: inconsistent hand size")
	ErrInvalidMeld   = errors.New("shanten: invalid meld")
	ErrUnsupported   = errors.New("shanten: unsupported capability")
	ErrBackend       = errors.New("shanten: backend failure")
	ErrInvalidResult = errors.New("shanten: invalid backend result")
)
