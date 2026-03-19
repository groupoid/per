{- Natural Numbers: https://anders.groupoid.space/foundations/mltt/nat/
   - Nat.

   HoTT 2.13 Natural Numbers
   HoTT 5.3 W-Types
   HoTT 5.5 Homotopy-inductive types

   Copyright (c) Groupoid Infinity, 2014-2023. -}

module homotopical where
import foundations.inductive
import foundations.univalent

idfun (A : Set) : A → A = λ (x : A), x

ℕ-ctor = ind₂ (λ (f : 𝟐), Set) 𝟎 𝟏
ℕ = W (x : 𝟐), ℕ-ctor x
zero : ℕ = sup 𝟐 ℕ-ctor 0₂ (ind₀ ℕ)
succ (n : ℕ) : ℕ = sup 𝟐 ℕ-ctor 1₂ (λ (x : 𝟏), n)

𝟎⟶ℕ (C : ℕ → Set) (f : 𝟎 → ℕ) : C zero → C (sup 𝟐 ℕ-ctor 0₂ f)
 = transp (<i> C (sup 𝟐 ℕ-ctor 0₂ (λ (x : 𝟎), ind₀ (PathP (<_> ℕ) (ind₀ ℕ x) (f x)) x @ i))) 0

𝟏⟶ℕ (C : ℕ → Set) (f : 𝟏 → ℕ) : C (succ (f ★)) → C (sup 𝟐 ℕ-ctor 1₂ f)
 = transp (<i> C (sup 𝟐 ℕ-ctor 1₂ (λ (x : 𝟏), ind₁ (λ (y : 𝟏), PathP (<_> ℕ) (f ★) (f y)) (<_> f ★) x @ i))) 0

ℕ-ind (C : ℕ → Set) (z : C zero) (s : Π (n : ℕ), C n → C (succ n)) : Π (n : ℕ), C n
 = indᵂ 𝟐 ℕ-ctor C
    (ind₂ (λ (x : 𝟐), Π (f : ℕ-ctor x → ℕ), (Π (b : ℕ-ctor x), C (f b)) → C (sup 𝟐 ℕ-ctor x f))
          (λ (f : 𝟎 → ℕ) (g : Π (x : 𝟎), C (f x)), 𝟎⟶ℕ C f z)
          (λ (f : 𝟏 → ℕ) (g : Π (x : 𝟏), C (f x)), 𝟏⟶ℕ C f (s (f ★) (g ★))))

ℕ-rec (C : Set) (z : C) (s : ℕ → C → C) : ℕ → C = ℕ-ind (λ (_ : ℕ), C) z s
ℕ-iter (C : Set) (z : C) (s : C → C) : ℕ → C = ℕ-rec C z (λ (_ : ℕ), s)
ℕ-case (C : Set) (z s : C) : ℕ → C = ℕ-iter C z (λ (_ : C), s)
plus : ℕ → ℕ → ℕ = ℕ-iter (ℕ → ℕ) (idfun ℕ) (∘ ℕ ℕ ℕ succ)
mult : ℕ → ℕ → ℕ = ℕ-rec (ℕ → ℕ) (\(_: ℕ), zero) (\(_: ℕ) (x: ℕ → ℕ) (m: ℕ), plus m (x m))
one : ℕ = succ zero
two : ℕ = succ one
three : ℕ = succ two
four : ℕ = succ three
five : ℕ = succ four
six : ℕ = succ five
seven : ℕ = succ six
eight : ℕ = succ seven
nine : ℕ = succ eight
ten : ℕ = succ nine

5′ : ℕ = plus two three
10′ : ℕ = mult 5′ two
55′ : ℕ = plus (mult 5′ 10′) 5′
