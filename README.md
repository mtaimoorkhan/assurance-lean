# CALIBRE pilot — quantifying specification completeness in Lean 4

A small, self-contained demonstration that **specification completeness can be
measured**, that the measurement separates specifications which proof success
cannot, and that a cleanly elaborating proof can establish nothing at all.

Everything here builds with `lake build` on a pinned toolchain and finishes in
a couple of seconds. There are no dependencies beyond Lean 4 core.

```
lake build
```

## What it measures

The running example is a sorted, duplicate-free list representing a finite set,
with set insertion as the operation under specification.

Two specifications are stated over the same reference implementation:

| | Requires |
|---|---|
| **Strong** | output sorted, no new elements, nothing lost, inserted value present |
| **Weak** | output sorted, and nothing else |

Both hold of the reference, and both proofs elaborate. Proof success cannot
distinguish them. The mutation score can.

### Results

A **declared mutation operator family** is applied to the reference: six
ordering tests × three equality tests × four post-processing steps × two value
perturbations = 144 combinations. Differential execution retains the 143 that
are observably distinct from the reference.

| Specification | Ĉ_beh | 95% Clopper–Pearson | Rejected |
|---|---|---|---|
| Strong | **1.000** | [0.975, 1.000] | 143 / 143 |
| Weak (sortedness only) | **0.853** | [0.784, 0.907] | 122 / 143 |

Against a smaller hand-written family of nine structural mutants — drop the
insertion, discard the list, drop the last element, insert the wrong value, and
so on — the strong specification scores **1.000** again while the weak one falls
to **0.556** [0.212, 0.863].

So the strong specification's score is stable across operator families and the
weak one's is not. That is why a score is meaningless without the family that
produced it, and why this pilot declares its family explicitly.

### Vacuity

`CalibrePilot/Structural.lean` contains a representation invariant that no
list satisfies. Under it:

```lean
theorem insert_returns_nil_vacuous (x : Nat) (l : List Nat) (h : InvBad l) :
    ins x l = [] := absurd h.2 (Nat.not_lt_zero _)
```

Insertion does not return the empty list. The theorem is nonetheless true,
because its precondition is unsatisfiable, and `#print axioms` reports that it
**depends on no axioms at all** — the cleanest possible footprint on a claim
that establishes nothing. Any pipeline that reports "verified" on proof success
reports this as verified.

## How it works — two stages

Rejection is established **by proof, not by test**. Execution locates the
counterexample; the kernel certifies it.

**Stage 1 — `CalibrePilot/Gen.lean`.** Declares the operator family, filters it
by differential execution against the reference, and searches a bounded domain
of 160 inputs for the first input at which each surviving mutant violates each
specification. Emits a witness table.

**Stage 2 — `CalibrePilot/Certified.lean`** (generated; do not edit by hand).
For each retained mutant, the witness becomes a machine-checked refutation:

```lean
theorem rej_000 : ¬ SpecStrong mut000 := fun h =>
  absurd (h 0 [] (by decide)) (by decide)
```

All 143 compile. `decide` is used rather than `native_decide`, so no additional
axiom enters any footprint — which matters in a project whose subject is axiom
footprints.

Regenerate stage 2 from stage 1's output with:

```
lake env lean CalibrePilot/Gen.lean > witnesses.txt
python3 tools/gen_certified.py witnesses.txt > CalibrePilot/Certified.lean
lake build
```

## Honest limits

- **Witness search is bounded.** It runs over 160 inputs, so a specification
  could in principle fail only outside that domain and be missed. The
  certification of each *located* failure is exact; it is the search that is
  incomplete, not the proof.
- **Scores are relative to the declared operator family**, as the two families
  above demonstrate rather than merely assert.
- **Equivalent-mutant detection is a sound but incomplete filter.** Differential
  execution discards mutants it can show to be equivalent; some survive and are
  counted as rejections they are not. The bias is therefore one-sided and
  conservative: it *under*-estimates completeness.
- **This is a pilot.** Replacing bounded search with incremental proof
  re-elaboration over whole corpora (mathlib4, Cedar, CompCert, seL4) is the
  work this is a pilot for.

## Layout

```
CalibrePilot/Structural.lean  hand-written structural family (n = 9) + vacuity demo
CalibrePilot/Gen.lean         stage 1: declared operator family, filter, witness search
CalibrePilot/Certified.lean   stage 2: 143 machine-checked refutations (generated)
tools/gen_certified.py        the generator for stage 2
lean-toolchain                pinned to v4.15.0 so results stay reproducible
```

## Licence

Apache 2.0.
