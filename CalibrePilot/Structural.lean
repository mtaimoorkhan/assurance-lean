/-
  CALIBRE pilot — the hand-written STRUCTURAL mutant family (n = 9), and the
  vacuity demonstration. Gen.lean holds the larger declared operator family;
  the contrast between the two is the point (see README).
  Three things are demonstrated:
    (1) a vacuous precondition lets a false conclusion be "proved", cleanly;
    (2) the specification mutation score separates a strong spec from a weak one
        on the SAME implementation, where proof success does not;
    (3) axiom footprints are machine-readable (the A coordinate).
-/

namespace CalibreStructural

/-! ## Representation: sorted, duplicate-free lists of naturals -/

def Sorted : List Nat → Bool
  | []          => true
  | [_]         => true
  | a :: b :: t => a < b && Sorted (b :: t)

/-- Reference implementation of set insertion over the sorted representation. -/
def ins (x : Nat) : List Nat → List Nat
  | []     => [x]
  | a :: t => if x < a then x :: a :: t
              else if x = a then a :: t
              else a :: ins x t

/-! ## Part 1 — vacuity: a clean proof of a false conclusion

`InvBad` is an invariant no list satisfies. Every obligation guarded by it is
vacuously true, so the theorem below elaborates and the kernel accepts it —
even though its conclusion is plainly wrong. A pipeline that reports
"verified" on proof success reports this as verified. -/

def InvBad (l : List Nat) : Prop := Sorted l = true ∧ l.length < 0

theorem insert_returns_nil_vacuous (x : Nat) (l : List Nat) (h : InvBad l) :
    ins x l = [] :=
  absurd h.2 (Nat.not_lt_zero _)

theorem insert_equals_its_own_reverse_vacuous (x : Nat) (l : List Nat)
    (h : InvBad l) : ins x l = (ins x l).reverse :=
  absurd h.2 (Nat.not_lt_zero _)

/-! ## Part 2 — the behavioural axis by mutation

Bounded domain: every sublist of `[0,1,2,3,4]` (all sorted) crossed with
`x ∈ {0,…,4}`. 160 cases. The pilot decides specifications by evaluation over
this domain; the funded work replaces evaluation with proof re-elaboration. -/

def sublists : List Nat → List (List Nat)
  | []     => [[]]
  | a :: t => let r := sublists t; r ++ r.map (a :: ·)

def testCases : List (Nat × List Nat) :=
  (List.range 5).flatMap fun x => (sublists [0,1,2,3,4]).map fun l => (x, l)

abbrev Impl := Nat → List Nat → List Nat

/-- Strong specification: preserves sortedness, and implements set insertion
    (no new elements, nothing lost, `x` present). -/
def SpecStrong (f : Impl) (x : Nat) (l : List Nat) : Bool :=
  !Sorted l ||
    (Sorted (f x l) &&
     (f x l).all (fun y => y == x || l.contains y) &&
     l.all (fun y => (f x l).contains y) &&
     (f x l).contains x)

/-- Weak specification: preserves sortedness, and nothing else. -/
def SpecWeak (f : Impl) (x : Nat) (l : List Nat) : Bool :=
  !Sorted l || Sorted (f x l)

def holds (S : Impl → Nat → List Nat → Bool) (f : Impl) : Bool :=
  testCases.all fun p => S f p.1 p.2

/-- Differential-execution filter: is this mutant observably distinct from the
    reference on the domain? Equivalent mutants are discarded, not guessed at. -/
def obsDistinct (f : Impl) : Bool :=
  testCases.any fun p => f p.1 p.2 ≠ ins p.1 p.2

/-! ### Mutants of the reference implementation -/

def m01 : Impl := fun _ l => l                                    -- drop the insert
def m02 : Impl := fun x l => x :: l                               -- prepend blindly
def m03 : Impl := fun x l => l ++ [x]                             -- append blindly
def m04 : Impl := fun x _l => [x]                                  -- discard the list
def m05 : Impl := fun _ l => l.reverse                            -- reverse
def m06 : Impl := fun x l => (ins x l).reverse                    -- insert then reverse
def m07 : Impl := fun x l => ins x (ins x l)                      -- insert twice
def m08 : Impl := fun x l => match l with                         -- off-by-one: ≤ for <
                             | []     => [x]
                             | a :: t => if x ≤ a then x :: a :: t else a :: ins x t
def m09 : Impl := fun x l => (ins x l).dropLast                    -- lose the last element
def m10 : Impl := fun x l => ins (x + 1) l                        -- insert the wrong value

def mutants : List Impl := [m01, m02, m03, m04, m05, m06, m07, m08, m09, m10]

def surviving : List Impl := mutants.filter obsDistinct

def rejectedBy (S : Impl → Nat → List Nat → Bool) : Nat :=
  (surviving.filter fun f => !holds S f).length

/-! ## Results -/

#eval s!"reference satisfies strong spec : {holds SpecStrong ins}"
#eval s!"reference satisfies weak spec   : {holds SpecWeak ins}"
#eval s!"mutants generated               : {mutants.length}"
#eval s!"observably distinct (retained)  : {surviving.length}"
#eval s!"rejected by STRONG spec         : {rejectedBy SpecStrong}"
#eval s!"rejected by WEAK spec           : {rejectedBy SpecWeak}"

/-! ## Part 3 — a genuinely proved property, and its axiom footprint -/

theorem ins_contains (x : Nat) (l : List Nat) : (ins x l).contains x = true := by
  induction l with
  | nil => simp [ins]
  | cons a t ih =>
    simp only [ins]
    by_cases h₁ : x < a
    · simp [h₁]
    · by_cases h₂ : x = a
      · simp [h₁, h₂]
      · simp only [if_neg h₁, if_neg h₂, List.contains_cons, Bool.or_eq_true]
        exact Or.inr ih

#print axioms ins_contains
#print axioms insert_returns_nil_vacuous

/-! ## Which mutants were filtered, and which survived each spec -/

def labelled : List (String × Impl) :=
  [("m01 drop insert", m01), ("m02 prepend", m02), ("m03 append", m03),
   ("m04 discard list", m04), ("m05 reverse", m05), ("m06 insert+reverse", m06),
   ("m07 insert twice", m07), ("m08 off-by-one ≤", m08), ("m09 drop last", m09),
   ("m10 wrong value", m10)]

#eval labelled.filter (fun p => !obsDistinct p.2) |>.map (·.1)
#eval (labelled.filter (fun p => obsDistinct p.2)).filter (fun p => holds SpecWeak p.2) |>.map (·.1)

end CalibreStructural

