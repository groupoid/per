# Strong Normalization: Girard Reducibility Candidates

This document provides a sketch of the strong normalization technique used in the **Per** theorem prover, specifically focusing on the implementation of Girard's Reducibility Candidates in both the OCaml model and the Elixir production implementation.

## 1. Overview

Normalization in **Per** is based on **Normalization by Evaluation (NbE)**. The core idea is to evaluate terms into a domain of "values" (semantic domain) and then "read back" (reify) those values into normal forms (syntax).

Girard's Reducibility Candidates (CR) technique is the standard method for proving strong normalization for systems like System F and MLTT. In **Per**, this is practically manifested through the handling of **Neutral terms** and **Type-in-Type** (Girard's Paradox toggle).

## 2. Neutral Terms and Canonicity

Strong normalization relies on the distinction between **Canonical** forms (constructors like `Lam`, `Pair`, `Universe`) and **Neutral** terms (stuck computations).

### Neutral Terms

A term is neutral if it is a variable or a projection/application from a neutral term.

- OCaml: `Var`, `VApp`, `VFst`, `VSnd`, `VAppFormula`, etc.
- Elixir: `%AST.Neutral{term: term, type: type}`

Neutral terms allow the evaluator to proceed even when the exact value is unknown (e.g., inside a binder during readback).

## 3. Incremental Beta-Reduction

The normalization process is driven by an incremental `reduce` (or `app`) function that performs beta-reduction specifically when a redex is formed.

### Evaluation (`eval`)

The `eval` function maps syntax to the semantic domain.

- **OCaml**: `Check.eval`
- **Elixir**: `Per.Typechecker.eval`

### Application (`app`)

The `app` function (and `appFormula`, `vfst`, `vsnd`) performs the incremental reduction:

- If the function is a `Lam`, it applies the body (Beta-reduction).
- If the function is `Neutral`, it constructs a new `Neutral` term (accumulating the "stuck" operation).

```elixir
# lib/per/typechecker.ex
defp app(f, x) do
  case f do
    %AST.Lam{body: func} -> func.(x) # Beta-reduction
    %AST.Neutral{term: term, type: %AST.Pi{codomain: b}} ->
       %AST.Neutral{term: %AST.App{func: term, arg: x}, type: b.(x)} 
    _ -> %AST.App{func: f, arg: x}
  end
end
```

## 4. Girard's Flag: Type-in-Type

The `girard` flag in **Per** explicitly allows `Universe : Universe` (Type-in-Type), which is known to lead to Girard's Paradox (non-termination).

- **OCaml**: `let ieq u v = !girard || u = v`
- **Elixir**: `Process.get(:per_girard, false) or u == v`

When `girard` is `false`, the system enforces a strict universe hierarchy ($U_n : U_{n+1}$), ensuring strong normalization.

## 5. Elixir Implementation vs. OCaml Model

### Conformance and Differences

| Feature | OCaml (`check.ml`) | Elixir (`typechecker.ex`) |
| :--- | :--- | :--- |
| **Domain** | Higher-order (functions) | Higher-order (functions) |
| **Neutrality** | Implicit in `value` type | Explicit `%AST.Neutral` |
| **Partiality** | Full `VSystem` support | Simplified `Partial` |
| **Readback** | `rbV` recursive function | `readback` recursive function |

### Clarification on Non-Conformance

- **Partial Terms**: The Elixir implementation of `EPartial` is currently a skeletal version of the OCaml `VSystem` logic. In OCaml, `EPartial` creates a `VLam` that returns a `VPartialP` wrapping a system of faces. Elixir's `eval/2` for `%AST.Partial{}` simply returns the evaluated expression without the full face-solving logic found in `check.ml:112`.

## 6. Summary of the Technique

1. **Evaluation**: Syntax -> Semantic Values (using environment).
2. **Incremental Reduction**: `app(Lam f, x)` executes `f(x)`.
3. **Neutral Accumulation**: If `f` is neutral, `app(f, x)` is neutral.
4. **Readback**: Reify semantic values back to syntax by applying neutral variables to binders.
