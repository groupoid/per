module univalent where

¬ (A : Set) = A → 𝟎
∘ᵀ (A B C: Set) : Set = (B → C) → (A → B) → (A → C)
∘ (A B C : Set) : ∘ᵀ A B C = λ (g : B → C) (f : A → B) (x : A), g (f x)
idᵀ (A : Set) : Set = A → A
id (A : Set) (a : A) : A = a
const (A B : Set) : A → B → A = λ (a : A) (b : B), a
const₁ (A : Set) : A → 𝟏 = const 𝟏 A ★
LineP (A : I → Set) : V = Π (i : I), A i

--- Path Space

Path (A : Set) (x y : A) : Set = PathP (<_> A) x y
idp (A : Set) (x : A) : Path A x x = <_> x
singl (A: Set) (a: A): Set = Σ (x: A), Path A a x
eta (A: Set) (a: A): singl A a = (a, idp A a)
sym (A: Set) (a b : A) (p : Path A a b) : Path A b a = <i> p @ -i
contr (A : Set) (a b : A) (p : Path A a b) : Path (singl A a) (eta A a) (b, p) = <i> (p @ i, <j> p @ i /\ j)
isContr (A: Set) : Set = Σ (x: A), Π (y: A), Path A x y
isContrSingl (A : Set) (a : A) : isContr (singl A a) = ((a,idp A a),(\ (z:singl A a), contr A a z.1 z.2))
cong (A B : Set) (f : A → B) (a b : A) (p : Path A a b) : Path B (f a) (f b) = <i> f (p @ i)
ap (A: Set) (a x: A) (B: A → Set) (f: A → B a) (b: B a) (p: Path A a x): Path (B a) (f a) (f x) = <i> f (p @ i)
mapOnPath (A: Set) (B: A → Set) (a: A) (f: A → B a) (b: B a) (x: A) (p: Path A a x): Path (B a) (f a) (f x) = <i> f (p @ i)
inv (A: Set) (a b: A) (p: Path A a b): Path A b a = <i> p @ -i
Path-η (A : Set) (x y : A) (p : Path A x y) : Path (Path A x y) p (<i> p @ i) = <_> p
idp-left (A : Set) (x y : A) (p : Path A x y) : Path (Path A x x) (<_> x) (<_> p @ 0) = <_ _> x
idp-right (A : Set) (x y : A) (p : Path A x y) : Path (Path A y y) (<_> y) (<_> p @ 1) = <_ _> y
sym-sym-eq-idp (A : Set) (x y : A) (p : Path A x y) : Path (Path A x y) p (sym A y x (sym A x y p)) = <_> p
isProp (A : Set) : Set = Π (a b : A), Path A a b
isSet (A : Set) : Set = Π (a b : A) (a0 b0 : Path A a b), Path (Path A a b) a0 b0
isGroupoid (A : Set) : Set = Π (a b : A) (x y : Path A a b) (i j : Path (Path A a b) x y), Path (Path (Path A a b) x y) i j
SET : Set₁ = Σ (X : Set), isSet X
Ω' : Set₁ = Σ (A : Set), isProp A
section (A B : Set) (f : A -> B) (g : B -> A) : Set = Π (b : B), Path B (f (g b)) b
retract (A B : Set) (f : A -> B) (g : B -> A) : Set = Π (a : A), Path A (g (f a)) a
hmtpy (A : Set) (x y : A) (p : Path A x y) : Path (Path A x x) (<_> x) (<i> p @ i /\ -i) = <j i> p @ j /\ i /\ -i
plam (A : Set) (f : I → A) : Path A (f 0) (f 1) = <i> f i
elim (A : Set) (a b : A) (p : Path A a b) : I → A = λ (i : I), p @ i
plam-elim (A : Set) (f : I → A) : Id (I → A) (elim A (f 0) (f 1) (plam A f)) f = ref f
elim-plam (A : Set) (a b : A) (p : Path A a b) : Path (Path A a b) (plam A (elim A a b p)) p = <_> p

--- Path as [Left] Identity System, Computational Properties

transport (A B: Set) (p : PathP (<_> Set) A B) (a: A): B = transp p 0 a
trans_comp (A : Set) (a : A) : Path A a (transport A A (<i> A) a) = <j> transp (<_> A) -j a
subst (A : Set) (P : A -> Set) (a b : A) (p : Path A a b) (e : P a) : P b = transp (<i> P (p @ i)) 0 e
D (A : Set) : Set₁ ≔ Π (x y : A), Path A x y → Set
J (A: Set) (x: A) (C: D A) (d: C x x (idp A x)) (y: A) (p: Path A x y): C x y p
 = subst (singl A x) (\ (z: singl A x), C x (z.1) (z.2)) (eta A x) (y, p) (contr A x y p) d
subst-comp (A: Set) (P: A → Set) (a: A) (e: P a): Path (P a) e (subst A P a a (idp A a) e) = trans_comp (P a) e
J-β (A : Set) (a : A) (C : D A) (d: C a a (idp A a)) : Path (C a a (idp A a)) d (J A a C d a (idp A a))
 = subst-comp (singl A a) (\ (z: singl A a), C a (z.1) (z.2)) (eta A a) d

--- DNF solver

∂ (i : I) = i ∨ -i
∂-eq-neg-∂ (i : I) : Id I (∂ i) (∂ -i) = ref (∂ i)
min (i j : I) = i ∧ j
max (i j : I) = i ∨ j
⊕ (i j : I) : I = (i ∧ -j) ∨ (-i ∧ j)
⊕-comm (i j : I) : Id I (⊕ i j) (⊕ j i) = ref (⊕ i j)
∧-comm (i j : I) : Id I (i ∧ j) (j ∧ i) = ref (i ∧ j)
∨-comm (i j : I) : Id I (i ∨ j) (j ∨ i) = ref (i ∨ j)
¬-of-∧ (i j : I) : Id I -(i ∧ j) (-i ∨ -j) = ref -(i ∧ j)
¬-of-∨ (i j : I) : Id I -(i ∨ j) (-i ∧ -j) = ref -(i ∨ j)
∧-distrib-∨ (i j k : I) : Id I ((i ∨ j) ∧ k) ((i ∧ k) ∨ (j ∧ k)) = ref ((i ∨ j) ∧ k)
∨-distrib-∧ (i j k : I) : Id I ((i ∧ j) ∨ k) ((i ∨ k) ∧ (j ∨ k)) = ref ((i ∧ j) ∨ k)
∧-assoc (i j k : I) : Id I (i ∧ (j ∧ k)) ((i ∧ j) ∧ k) = ref (i ∧ (j ∧ k))
