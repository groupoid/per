module inductive where

option irrelevance true

Path (A : Set) (x y : A) : Set = PathP (<_> A) x y
idp (A : Set) (x : A) : Path A x x = <_> x
+ (A B: Set) : Set = Σ (x : 𝟐), ind₂ (λ (_ : 𝟐), Set) A B x

0-ind (C: 𝟎 → Set) (z: 𝟎) : C z = ind-empty (C z) z

1-rec (C: Set) (x: C) : 𝟏 → C = ind₁ (\(_:𝟏), C) x
1-ind (C: 𝟏 → Set) (x: C ★) : П (z: 𝟏), C z = ind₁ C x
--def 1-β (C: Set) (c: C): Path C (1-rec C c ★) c = idp C c
--def 1-η (z: 𝟏) : Path 𝟏 ★ z = idp 𝟏 ★

2-ind (C: 𝟐 → Set) (x: C 0₂) (y: C 1₂) : П (z: 𝟐), C z = ind₂ C x y
2-rec (C: Set) (x y: C) : П (z: bool), C = ind₂ (\(_:𝟐), C) x y

2-β₁ (C : 𝟐 → Set) (f : Π (x : 𝟐), C 0₂) (g : Π (y : 𝟐), C 1₂) : PathP (<_>C 0₂) (f 0₂) (ind₂ (λ (x : 𝟐), C x) (f 0₂) (g 1₂) 0₂) = <_> f 0₂
--def 2-β₂ (C : 𝟐 → Set) (f : Π (x : 𝟐), C 0₂) (g : Π (y : 𝟐), C 1₂) : PathP (<_>C 1₂) (g 1₂) (ind₂ (λ (x : 𝟐), C x) (f 0₂) (g 1₂) 1₂) = <_> g 1₂

--def 2-η (c : 𝟐) : + (PathP (<_> 𝟐) c 0₂) (PathP (<_> 𝟐) c 1₂) = ind₂ (λ (c : 𝟐), + (PathP (<_> 𝟐) c 0₂) (PathP (<_> 𝟐) c 1₂)) (0₂, <_> 0₂) (1₂, <_> 1₂) c

W′ (A : Set) (B : A → Set) : Set = W (x: A), B x
sup′ (A : Set) (B : A → Set) (x : A) (f : B x → W′ A B) : W′ A B = sup A B x f

W-ind (A : Set) (B : A → Set) (C : (W (x : A), B x) → Set)
    (g : Π (x : A) (f : B x → (W (x : A), B x)), (Π (b : B x), C (f b)) → C (sup A B x f))
    (w : W (x : A), B x)
  : C w = indᵂ A B C g w

W-rec (A : Set) (B : A → Set) (C : Set)
    (g : Π (x : A) (f : B x → (W (x : A), B x)), (B x → C) → C)
    (w : W (x : A), B x)
  : C = indᵂ A B (λ (_ : W (x : A), B x), C) g w

W-ind′ (A : Set) (B : A → Set) (C : (W (x : A), B x) → Set)
    (φ : Π (x : A) (f : B x → (W (x : A), B x)), C (sup A B x f))
  : Π (w : W (x : A), B x), C w
 = indᵂ A B C (λ (x : A) (f : B x → (W (x : A), B x)) (g : Π (b : B x), C (f b)), φ x f)

W-case (A : Set) (B : A → Set) (C : Set) (g : Π (x : A) (f : B x → (W (x : A), B x)), C)
  : (W (x : A), B x) → C
 = W-ind′ A B (λ (_ : W (x : A), B x), C) g

-- def indᵂ-β (A : Set) (B : A → Set) (C : (W (x : A), B x) → Set)
--     (g : Π (x : A) (f : B x → (W (x : A), B x)), (Π (b : B x), C (f b)) → C (sup A B x f))
--     (a : A) (f : B a → (W (x : A), B x))
--  : PathP (<_> C (sup A B a f)) (indᵂ A B C g (sup A B a f)) (g a f (λ (b : B a), indᵂ A B C g (f b)))
-- = <_> g a f (λ (b : B a), indᵂ A B C g (f b))

W-proj₁ (A : Set) (B : A → Set) : (W (x : A), B x) → A
 = W-case A B A (λ (x : A) (f : B x → (W (x : A), B x)), x)

--def W-proj₂ (A : Set) (B : A → Set) : Π (w : W (x : A), B x), B (W-proj₁ A B w) → (W (x : A), B x)
-- = W-ind′ A B (λ (w : W (x : A), B x), B (W-proj₁ A B w) → (W (x : A), B x))
--               (λ (x : A) (f : B x → (W (x : A), B x)), f)

--def W-η (A : Set) (B : A → Set)
--  : Π (w : W (x : A), B x), Path (W (x : A), B x) (sup A B (W-proj₁ A B w) (W-proj₂ A B w)) w
-- = W-ind′ A B (λ (w : W (x : A), B x), Path (W (x : A), B x) (sup A B (W-proj₁ A B w) (W-proj₂ A B w)) w)
--               (λ (x : A) (f : B x → (W (x : A), B x)), <_> sup A B x f)

--def trans-W (A : I → Set) (B : Π (i : I), A i → Set) (a : A 0) (f : B 0 a → (W (x : A 0), B 0 x)) : W (x : A 1), B 1 x
-- = sup (A 1) (B 1) (transp (<i> A i) 0 a) (transp (<i> B i (transFill (A 0) (A 1) (<j> A j) a @ i) → (W (x : A i), B i x)) 0 f)

