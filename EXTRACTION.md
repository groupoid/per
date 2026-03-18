# Extraction from Homotopy Type System (HTS)

This document addresses the theoretical and practical feasibility of program extraction from **Per**, a type theory featuring a homotopical core (Cubical Type Theory) within a potentially homotopical framework.

## 1. HTS and Extraction Feasibility

In Homotopy Type System (HTS), the universe hierarchy is typically bifurcated into a **Strict** part (governed by Definitional Equality) and a **Homotopical** part (governed by Path Equality). 

Extraction is possible because the constructive core of the theory—expressed through the $\beta$-reduction of $\Pi$ and $\Sigma$ types—remains consistent across both parts. However, the presence of cubical primitives (e.g., `transport`, `hcomp`) introduces specific requirements for the target runtime.

## 2. Technical Limitations at Runtime

From an academic perspective, several limitations arise when calling extracted functions in a non-cubical runtime (such as the Erlang/Elixir BEAM):

### 2.1. Computational Erasure of Path Proofs

In traditional MLTT, identity proofs (e.g., `Refl`) are often non-computational and can be erased during extraction. However, in Cubical Type Theory, paths are functions from an interval $I$, and operations like `transport` and `composition` carry essential computational content. 

- **Limitation**: If the target runtime lacks a native representation of the cubical interval and face system, these operations must be fully reduced to canonical values before extraction, or mapped to complex runtime simulators.

### 2.2. The "Stuck Term" Problem

A defining characteristic of Cubical Type Theory (CCHM model) is that operations like `transport p phi u0` can become "stuck" if the path $p$ or the dimension $\phi$ is a variable (neutral term).

- **Limitation**: Extracted code must either:
    1. Only target **closed terms**, where all cubical operations can be fully normalized away.
    2. Incorporate a **Symbolic Evaluator** at runtime to handle potentially neutral terms, which significantly degrades performance.

### 2.3. Complexity of Runtime `transport`

Realizing `transport` as a runtime function requires recursive traversal of the data structures being transported. For complex inductive types (W-types), this is computationally expensive.

- **Limitation**: Without compiler-level optimization (such as specialization of `transport` for specific types), extracted code may exhibit $O(N)$ or even higher complexity for operations that are conceptually "identity" in a strict setting.

### 2.4. Definitional vs. Runtime Equality

HTS relies on a strict definitional equality. In the target runtime (Erlang/Elixir), this is mapped to term equality (`=:=` or `==`).

- **Limitation**: Structural equality at runtime might not perfectly align with the theory's internal equality, especially when dealing with erased types or higher-order functions (closures), leading to potential mismatches in behavior if the program expects strict witness-dependent identity.

### 2.5. Universe Level Erasure

Universe levels ($U_n$) are essential for the theory's consistency but have no runtime counterpart.

- **Limitation**: While safe to erase, this erasure means that runtime type introspection (if implemented) cannot distinguish between terms originating from different levels of the hierarchy, effectively collapsing the predicative levels.

## 3. Conslusion

Extraction from HTS is a viable path for verified software, provided that the **strictness** of the extraction targets only the computational subset. The primary challenge remains the runtime realization of cubical operations, which necessitates a trade-off between **Full Canonicity** (keeping the primitives alive at runtime) and **Erasure** (forcing normalization before extraction).
