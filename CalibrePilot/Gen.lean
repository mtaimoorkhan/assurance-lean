/-
  CALIBRE pilot, stage 1: a declared mutation operator family, the
  differential-execution filter, and witness search.

  Stage 2 (Certified.lean, generated from this file's output) certifies every
  rejection by a machine-checked refutation rather than by evaluation.
-/

namespace Calibre

def Sorted : List Nat → Bool
  | []          => true
  | [_]         => true
  | a :: b :: t => a < b && Sorted (b :: t)

abbrev Impl := Nat → List Nat → List Nat

/-! ## The reference implementation, in parameterised form.

Mutation operators act on the four marked positions: the ordering test, the
equality test, the inserted value, and a post-processing step. -/

def insG (cmp eqf : Nat → Nat → Bool) (dx : Nat → Nat) : Nat → List Nat → List Nat
  | x, []     => [dx x]
  | x, a :: t => if cmp (dx x) a then dx x :: a :: t
                 else if eqf (dx x) a then a :: t
                 else a :: insG cmp eqf dx x t

def mk (cmp eqf : Nat → Nat → Bool) (post : List Nat → List Nat) (dx : Nat → Nat) : Impl :=
  fun x l => post (insG cmp eqf dx x l)

def lt : Nat → Nat → Bool := fun a b => decide (a < b)
def eqN : Nat → Nat → Bool := fun a b => decide (a = b)

/-- The reference: strict ordering, equality dedup, no perturbation, no post-step. -/
def ins : Impl := mk lt eqN id id

/-! ## Declared operator family

Four operator classes. The score is relative to this family, and the family is
stated rather than left implicit. -/

def cmps : List (String × (Nat → Nat → Bool)) :=
  [("lt", lt),
   ("le", fun a b => decide (a ≤ b)),
   ("gt", fun a b => decide (a > b)),
   ("ge", fun a b => decide (a ≥ b)),
   ("eq", eqN),
   ("ne", fun a b => decide (a ≠ b))]

def eqs : List (String × (Nat → Nat → Bool)) :=
  [("eq", eqN),
   ("ne", fun a b => decide (a ≠ b)),
   ("false", fun _ _ => false)]

def posts : List (String × (List Nat → List Nat)) :=
  [("id", id), ("rev", List.reverse), ("dropLast", List.dropLast), ("tail", List.tail)]

def dxs : List (String × (Nat → Nat)) :=
  [("id", id), ("succ", fun n => n + 1)]

/-- Every combination, labelled by the operators applied. -/
def family : List (String × Impl) :=
  cmps.flatMap fun c => eqs.flatMap fun e => posts.flatMap fun p => dxs.map fun d =>
    (s!"cmp={c.1} eq={e.1} post={p.1} dx={d.1}", mk c.2 e.2 p.2 d.2)

/-! ## Specifications -/

def SpecStrongB (f : Impl) (x : Nat) (l : List Nat) : Bool :=
  !Sorted l ||
    (Sorted (f x l) &&
     (f x l).all (fun y => y == x || l.contains y) &&
     l.all (fun y => (f x l).contains y) &&
     (f x l).contains x)

def SpecWeakB (f : Impl) (x : Nat) (l : List Nat) : Bool :=
  !Sorted l || Sorted (f x l)

/-! ## Bounded domain, used only to FIND witnesses -/

def sublists : List Nat → List (List Nat)
  | []     => [[]]
  | a :: t => let r := sublists t; r ++ r.map (a :: ·)

def testCases : List (Nat × List Nat) :=
  (List.range 5).flatMap fun x => (sublists [0,1,2,3,4]).map fun l => (x, l)

/-- Differential-execution filter: observably distinct from the reference? -/
def distinct (f : Impl) : Bool :=
  testCases.any fun p => f p.1 p.2 ≠ ins p.1 p.2

/-- First input at which a specification fails for this implementation, if any.
    This is the witness that stage 2 turns into a machine-checked refutation. -/
def witness (S : Impl → Nat → List Nat → Bool) (f : Impl) : Option (Nat × List Nat) :=
  testCases.find? fun p => !S f p.1 p.2

def retained : List (String × Impl) :=
  (family.filter fun p => distinct p.2)

/-! ## Stage-1 report -/

#eval s!"family size (all operator combinations) : {family.length}"
#eval s!"observably distinct from reference      : {retained.length}"
#eval s!"reference satisfies strong spec         : {testCases.all fun p => SpecStrongB ins p.1 p.2}"
#eval s!"reference satisfies weak spec           : {testCases.all fun p => SpecWeakB ins p.1 p.2}"
#eval s!"retained rejected by STRONG             : {(retained.filter fun p => (witness SpecStrongB p.2).isSome).length}"
#eval s!"retained rejected by WEAK               : {(retained.filter fun p => (witness SpecWeakB p.2).isSome).length}"

/-- Emit the witness table that stage 2 is generated from. -/
def witnessTable : List (String × String × String) :=
  retained.map fun p =>
    (p.1,
     match witness SpecStrongB p.2 with
     | some (x, l) => s!"{x}|{l}"
     | none        => "none",
     match witness SpecWeakB p.2 with
     | some (x, l) => s!"{x}|{l}"
     | none        => "none")

/-- Machine-parseable dump: operator labels, strong-spec witness, weak-spec witness. -/
def dump : String :=
  String.intercalate "\n" (retained.map fun p =>
    let w (S : Impl → Nat → List Nat → Bool) : String :=
      match witness S p.2 with
      | some (x, l) => s!"{x};{l}"
      | none        => "NONE"
    s!"{p.1}@@{w SpecStrongB}@@{w SpecWeakB}")

#eval IO.println dump

end Calibre
