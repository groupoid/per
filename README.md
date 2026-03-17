Per Martin-Löf: Intuitionistic Type Theory
==========================================

<img src="https://per.groupoid.space/img/per.jpg?v=1" height=400>

## Abstract

**Per** is a theorem prover implemented in OCaml, constitutes a MLTT-80 core for a dependently-typed lambda calculus,
constrained to exclude pattern matching, let-bindings, implicit arguments.
It encompasses universes, dependent products `Pi`, dependent pairs `Sigma`, identity types `Id`,
and `0`, `1`, `2`, `W` types for well-founded definitions.
Its mathematical properties, focusing on correctness, soundness, totality, canonicity, decidability and related
attributes relevant to formal mathematics are being analyzed.

## Introduction

The type checker operates over a term syntax comprising:

* `Universe i`: Type universes with level `i ∈ ℕ`.
* `Pi (x, A, B)`: Dependent function, where `A : Universe i` and `B : Universe j` under `x : A`.
  `Lam (x, A, t)`: Lambda abstraction with totality enforced.
  `App (f, a)`: Function application.
* `Sigma (x, A, B)`: Dependent pair types.
  `Pair (a, b)`, `Fst p`, `Snd p` construction and projections.
* `Id (A, a, b)`: Identity type, with `Refl` a and `J` eliminator.

The typing judgment `Γ ⊢ t : T` is defined via `infer` and `check` functions,
with definitional equality `Γ ⊢ t = t'` implemented via `equal`.

## Syntax

```OCaml
type term =
  | Var of name | Universe of level
  | Pi of name * term * term | Lam of name * term * term | App of term * term
  | Sigma of name * term * term | Pair of term * term | Fst of term | Snd of term
  | Id of term * term * term | Refl of term
  | J of term * term * term * term * term * term  (* J A a b C d p *)
```

## Semantics

### Syntactic Equality `equal`

Structural equality of terms under an environment and context.

The function implements judgmental equality with substitution to handle bound variables,
avoiding explicit α-conversion by assuming fresh names (a simplification
over full de Bruijn indices [3]). The recursive descent ensures congruence,
but lacks normalization, making it weaker than CIC’s definitional equality,
which includes β-reduction.

* **Terminal Cases**: Variables `Var x` are equal if names match; universes `Universe i` if levels are identical.
* **Resursive Cases**: `App (f, arg)` requires equality of function and argument.
`Pi (x, a, b)` compares domains and codomains, adjusting for variable renaming via substitution.
`Inductive d` checks name, level, and parameters.
`Constr` and `Elim` compare indices, definitions, and arguments/cases.
* Default: Returns false for mismatched constructors.

**Theorem**. Equality is reflexive, symmetric, and transitive modulo
α-equivalence (cf. [1], Section 2). For `Pi (x, a, b)` and `Pi (y, a', b')`,
equality holds if `a = a'` and `b[x := Var x] = b'[y := Var x]`,
ensuring capture-avoiding substitution preserves meaning.

### Context Variables Lookup `lookup_var`

Retrieve a variable’s type from the context.
Context are the objects in the Substitutions categories.

* Searches `ctx` for `(x, ty)` using `List.assoc`.
* Returns `Some ty` if found, `None` otherwise.

**Theorem**: Context lookup is well-defined under uniqueness
of names (cf. [1], Section 3). If `ctx = Γ, x : A, Δ`,
then `lookup_var ctx x = Some A`.

### Substitution Calculus `subst`

Substitute term `s` for variable `x` in term `t`.
Substitutions are morphisms in Substitution categorties.

The capture-avoiding check `if x = y` prevents variable capture
but assumes distinct bound names, a simplification over full
renaming or de Bruijn indices. For Elim, substituting in the
motive and cases ensures recursive definitions remain sound,
aligning with CIC’s eliminator semantics.

* `Var`: Replaces `x` with `s`, leaves others unchanged.
* `Pi/Lam`: Skips substitution if bound variable shadows `x`, else recurses on domain and body.
* `App/Constr/Elim`: Recurses on subterms.

**Theorem**. Substitution preserves typing (cf. [13], Lemma 2.1).
If `Γ ⊢ t : T` and `Γ ⊢ s : A`, then `Γ ⊢ t[x := s] : T[x := s]`
under suitable conditions on x.

### Infer Equality Induction `infer_J`

Ensuring `J (ty, a, b, c, d, p)` has type `c a b p by` validating the motive,
base case, and path against CIC’s equality elimination rule.

The `infer_J` function implements the dependent elimination rule for identity
types in the Calculus of Inductive Constructions (CIC), enabling proofs and
computations over equality (e.g., `symmetry : Π a b : ty, Π p : Id (ty, a, b), Id(ty, b, a)`).
It type-checks the term `J (ty, a, b, c, d, p)` by ensuring 
`ty : Universe 0` is the underlying type, `a : ty` and `b : ty` are endpoints,
`c : Π (x:ty), Π (y:ty), Π (p: Id(ty, x, y)), Type0` is a motive over all paths,
`d : Π (x:ty), c x x (Refl x)` handles the reflexive case,
and `p : Id(ty, a, b)` is the path being eliminated.
The function constructs fresh variables to define the motive
and base case types, checks each component, and returns `c a b p` (normalized),
reflecting the result of applying the motive to the specific path. 

**Theorem**. For an environment `env` and context `ctx`, given a type `A : Type_i`,
terms `a : A`, `b : A`, a motive `C : Π (x:A), Π (y:A), Π(p:Id(A, x, y)),Type_j`,
a base case `d : Π(x:A), C x x (Refl x)`, and a path `p : Id(A, a, b)`, the
term `J (A, a, b, C, d, p)` is well-typed with type `C a b p`. (Reference:
CIC [1], Section 4.5; Identity Type Elimination Rule).

### Type Inference `infer`

Infer the type of term `t` in context `ctx` and environment `env`.

For `Pi` and `Lam`, universe levels ensure consistency
(e.g., `Type i : Type (i + 1)`), while `Elim` handles induction,
critical for dependent elimination. Note that lambda agrument should be typed
for easier type synthesis [13].

### Check Universes `check_universe`

Ensure `t` is a universe, returning its level.
Infers type of `t`, expects `Universe i`.

This auxiliary enforces universe hierarchy, preventing
paradoxes (e.g., Type : Type). It relies on infer,
assuming its correctness, and throws errors for
non-universe types, aligning with ITT’s stratification.

**Theorem**: Universe checking is decidable (cf. [13]).
If `ctx ⊢ t : Universe i`, then `check_universe env ctx t = i`.

### Check `check`

Check that `t` has type `ty`.

* `Lam`: Ensures the domain is a type, extends the context, and checks the body against the codomain.
* Default: Infers t’s type, normalizes ty, and checks equality.

The function leverages bidirectional typing: specific cases (e.g., `Lam`)
check directly, while the default case synthesizes via infer and compares
with a normalized ty, ensuring definitional equality (β-reduction).
Completeness hinges on normalize terminating (ITT’s strong normalization)
and equal capturing judgmental equality.

**Theorem**. Type checking is complete (cf. [1], Normalization).
If `ctx ⊢ t : T` in the type theory, then `check env ctx t T` succeeds,
assuming normalization and sound inference.

### One-step β-reductor `reduce`

Perform one-step β-reduction or inductive elimination.

The function implements a one-step reduction strategy combining ITT’s β-reduction 
with CIC’s ι-reduction for inductives. The `App (Lam, arg)` case directly applies
substitution, while `Elim (Constr)` uses `apply_case` to handle induction,
ensuring recursive calls preserve typing via the motive p. The `Pi` case,
though unconventional, supports type-level computation, consistent with CIC’s flexibility. 

* `App (Lam, arg)`: Substitutes arg into the lambda body (β-reduction).
* `App (Pi, arg)`: Substitutes arg into the codomain (type-level β-reduction).
* `App (f, arg)`: Reduces f, then arg if f is unchanged.
* Default: Returns unchanged.

**Theorem**. Reduction preserves typing (cf. [8], Normalization Lemma, Subject Reduction).
If `ctx ⊢ t : T` and `t → t'` via β-reduction or inductive elimination, then `ctx ⊢ t' : T`.

### Normalization `normalize`

This function fully reduces a term t to its normal form by iteratively
applying one-step reductions via reduce until no further changes occur,
ensuring termination for well-typed terms.

This function implements strong normalization, a cornerstone of MLTT [9]
and CIC [1], where all reduction sequences terminate. The fixpoint
iteration relies on reduce’s one-step reductions (β for lambdas, ι
for inductives), with equal acting as the termination oracle.
For `plus 2 2`, it steps to `succ succ succ succ zero`, terminating at a constructor form.

**Theorem**. Normalization terminates (cf. [1]. Strong Normalization via CIC).
Every well-typed term in the system has a ormal form under β- and ι-reductions.

## Conclusion

Per’s elegance rests on firm theoretical ground. Here, we reflect on key meta-theorems for Classical MLTT with General Inductive Types, drawing from CIC’s lineage:

* **Soundness and Completeness**: Per’s type checker is sound—every term it accepts has a type under MLTT’s rules [Paulin-Mohring, 1996].
  This ensures that every term accepted by Per is typable in the underlying theory.
  Relative to the bidirectional type checking algorithm, context is appropriately managed [Harper & Licata, 2007].
  The interplay of inference and checking modes guarantees this property.
* **Canonicity, Normalization, and Totality**: Canonicity guarantees that every closed term of type `Nat` normalizes
  to `zero` or `succ n` [Martin-Löf, 1984]. Per’s normalize achieves strong normalization—every term reduces to a
  unique normal form—thanks to CIC’s strict positivity [Coquand & Paulin-Mohring, 1990]. Totality follows: all
  well-typed functions terminate, as seen in list_length reducing to `succ (succ zero)`.
* **Consistency and Decidability**: Consistency ensures no proof of ⊥ exists, upheld by normalization and the
  absence of paradoxes like Girard’s [Girard, 1972]. Type checking is decidable in Per, as our algorithm
  terminates for well-formed inputs, leveraging CIC’s decidable equality [Asperti et al., 2009].
* **Conservativity and Initiality**: Per is conservative over simpler systems like System F, adding dependent
  types without altering propositional truths [Pfenning & Paulin-Mohring, 1989]. Inductive types like Nat satisfy
  initiality—every algebra morphism from Nat to another structure is uniquely defined—ensuring categorical universality [Dybjer, 1997].

### Soundness

* Definition: Type preservation and logical consistency hold.
* Formal Statement: 1) If `Γ ⊢ t : T` and `infer t = t'`, then `Γ ⊢ t' : T`;
  2) No `t` exists such that `Γ ⊢ t : Id (Universe 0, Universe 0, Universe 1)`.
* Proof: Preservation via terminating reduce; consistency via positivity and intensionality.
* Status: Sound, inforced by rejecting non-total lambdas.

### Completeness

* Definition: The type checker captures all well-typed terms of MLTT within its bidirectional framework.
* Formal Statement: If `Γ ⊢ 𝑡 : T`, then `infer Δ Γ 𝑡 = T` or `check Δ Γ 𝑡 T` holds under suitable `Δ`.
* Status: Complete relative to the implemented algorithm.

### Canonicity

* Definition: Reduction reaches a normal form; equality is decidable.
* Formal Statement: `equal Δ Γ t t'` terminates, reflecting normalize’s partial eta and beta reductions in `normnalize`.
* Status: Satisfied within the scope of implemented reductions.

### Totality

* Definition: All well-typed constructs terminate under reduction.
* Formal Statement: 1) For `Inductive d : Universe i`, each `Constr (j, d, args)` is total;
  2) For `t : T` with `Ind` or `J`, `reduce t` terminates;
  3) For `Lam (x, A, t) : Pi (x, A, B)`, `reduce (App (Lam (x, A, t), a))` terminates for all `a : A`;
  4) `normalize Δ Γ t` terminates.

### Consistency

The system is logically consistent, meaning no term `t` exists such that `Γ ⊢ t : ⊥`.
This is upheld by normalization and the absence of paradoxes such as Girard's [Girard, 1972].

### Decidability

* Definition: Type checking and equality are computable.
* Formal Statement: `infer` and `check` terminate with a type or `TypeError`.
* Status: Decidable, enhanced by termination checks on lambda expressions.

## Artefact

```
% mix per.repl
🧊 Per Programming Language version 0.4.0 [Lean Syntax]
Copyright (c) 2016-2026 Groupoid Infinity
https://groupoid.github.io/per/

per>
>
```

## MLTT

[9]. Martin-Löf, P. Intuitionistic Type Theory. 1980.<br>
[10]. Thierry Coquand. An Algorithm for Type-Checking Dependent Types. 1996. <br>

## PTS

[11]. N. G. de Bruijn. Lambda Calculus Notation with Nameless Dummies. 1972. <br>
[12]. J.-Y. Girard. Interprétation fonctionnelle et élimination des coupures. 1972. <br>
[13]. Thierry Coquand, Gerard Huet. <a href="https://core.ac.uk/download/pdf/82038778.pdf">The Calculus of Constructions</a>. 1988.<br>

## Author

Namdak Tonpa
