module mltt where

option girard true

Path (A : Set) (x y : A) : Set = PathP (<_> A) x y
idp (A : Set) (x : A) : Path A x x = <_> x
Pi (A : Set) (B : A → Set) : Set = Π (x : A), B x
Π-lambda (A : Set) (B : A → Set) (b : Pi A B) : Pi A B = λ (x : A), b x
Π-apply (A: Set) (B: A → Set) (f: Pi A B) (a: A) : B a = f a
Π-β (A : Set) (B : A → Set) (a : A) (f : Pi A B) : Path (B a) (Π-apply A B (Π-lambda A B f) a) (f a) = idp (B a) (f a)
Π-η (A : Set) (B : A → Set) (a : A) (f : Pi A B) : Path (Pi A B) f (λ (x : A), f x) = idp (Pi A B) f
Sigma (A : Set) (B : A → Set) : Set = summa (x: A), B x
pair (A: Set) (B: A → Set) (a: A) (b: B a) : Sigma A B = (a, b)
pr₁ (A: Set) (B: A → Set) (x: Sigma A B) : A = x.1
pr₂ (A: Set) (B: A → Set) (x: Sigma A B) : B (pr₁ A B x) = x.2
Σ-β₁ (A : Set) (B : A → Set) (a : A) (b : B a) : Path A a (pr₁ A B (a ,b)) = idp A a
Σ-β₂ (A : Set) (B : A → Set) (a : A) (b : B a) : Path (B a) b (pr₂ A B (a, b)) = idp (B a) b
Σ-η (A : Set) (B : A → Set) (p : Sigma A B) : Path (Sigma A B) p (pr₁ A B p, pr₂ A B p) = idp (Sigma A B) p

Path-1 (A : Set) (x y : A) : Set = PathP (<_> A) x y
idp-1 (A : Set) (x : A) : Path A x x = <_> x
transport (A B: Set) (p : PathP (<_> Set) A B) (a: A): B = transp p 0 a
singl (A: Set) (a: A): Set = Σ (x: A), Path A a x
eta (A: Set) (a: A): singl A a = (a, idp A a)
contr (A : Set) (a b : A) (p : Path A a b) : Path (singl A a) (eta A a) (b, p) = <i> (p @ i, <j> p @ i /\ j)
trans_comp (A : Set) (a : A) : Path A a (transport A A (<i> A) a) = <j> transp (<_> A) -j a
subst (A : Set) (P : A -> Set) (a b : A) (p : Path A a b) (e : P a) : P b = transp (<i> P (p @ i)) 0 e
subst-comp (A: Set) (P: A → Set) (a: A) (e: P a): Path (P a) e (subst A P a a (idp A a) e) = trans_comp (P a) e
D (A : Set) : Set₁ = Π (x y : A), Path A x y → Set

J (A: Set) (x: A) (C: D A) (d: C x x (idp A x)) (y: A) (p: Path A x y): C x y p
 = subst (singl A x) (\ (z: singl A x), C x (z.1) (z.2)) (eta A x) (y, p) (contr A x y p) d
J-1 (A : Set) (x : A) (C: D A) (d: C x x (idp A x)) (y: A) (p: Path A x y): C x y p
 = subst (singl A x) (\ (z: singl A x), C x (z.1) (z.2)) (eta A x) (y, p) (contr A x y p) d

J-β (A : Set) (a : A) (C : D A) (d: C a a (idp A a)) : Path (C a a (idp A a)) d (J A a C d a (idp A a))
 = subst-comp (singl A a) (\ (z: singl A a), C a (z.1) (z.2)) (eta A a) d

MLTT-73 : Set =
  Σ (Π-form  : Π (A : Set) (B : A → Set), Set)
    (Π-ctor₁ : Π (A : Set) (B : A → Set), Pi A B → Pi A B)
    (Π-elim₁ : Π (A : Set) (B : A → Set), Pi A B → Pi A B)
    (Π-comp₁ : Π (A : Set) (B : A → Set) (a : A) (f : Pi A B), Path (B a) (Π-elim₁ A B (Π-ctor₁ A B f) a) (f a))
    (Π-comp₂ : Π (A : Set) (B : A → Set) (a : A) (f : Pi A B), Path (Pi A B) f (λ (x : A), f x))
    (Σ-form  : Π (A : Set) (B : A → Set), Set)
    (Σ-ctor₁ : Π (A : Set) (B : A → Set) (a : A) (b : B a) , Sigma A B)
    (Σ-elim₁ : Π (A : Set) (B : A → Set) (p : Sigma A B), A)
    (Σ-elim₂ : Π (A : Set) (B : A → Set) (p : Sigma A B), B (pr₁ A B p))
    (Σ-comp₁ : Π (A : Set) (B : A → Set) (a : A) (b: B a), Path A a (Σ-elim₁ A B (Σ-ctor₁ A B a b)))
    (Σ-comp₂ : Π (A : Set) (B : A → Set) (a : A) (b: B a), Path (B a) b (Σ-elim₂ A B (a, b)))
    (Σ-comp₃ : Π (A : Set) (B : A → Set) (p : Sigma A B), Path (Sigma A B) p (pr₁ A B p, pr₂ A B p))
    (=-form  : Π (A : Set) (a : A), A → Set)
    (=-ctor₁ : Π (A : Set) (a : A), Path A a a)
    (=-elim₁ : Π (A : Set) (a : A) (C: D A) (d: C a a (=-ctor₁ A a)) (y: A) (p: Path A a y), C a y p)
    (=-comp₁ : Π (A : Set) (a : A) (C: D A) (d: C a a (=-ctor₁ A a)), Path (C a a (=-ctor₁ A a)) d (=-elim₁ A a C d a (=-ctor₁ A a))),
    𝟏

internalizing : MLTT-73
 = ( Pi, Π-lambda, Π-apply, Π-β, Π-η,
      Sigma, pair, pr₁, pr₂, Σ-β₁, Σ-β₂, Σ-η,
      Path-1, idp-1, J-1, J-β,
      ★
    )
