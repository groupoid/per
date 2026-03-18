module mltt where

option girard true

def Path (A : Set) (x y : A) : Set := PathP (<_> A) x y
def idp (A : Set) (x : A) : Path A x x := <_> x
def Pi (O : 𝟏) (A : Set) (B : A → Set) : Set := Π (x : A), B x
def Π-lambda (O : 𝟏) (A : Set) (B : A → Set) (b : Pi ★ A B) : Pi ★ A B := λ (x : A), b x
def Π-apply (O : 𝟏) (A: Set) (B: A → Set) (f: Pi ★ A B) (a: A) : B a := f a
def Π-β (O : 𝟏) (A : Set) (B : A → Set) (a : A) (f : Pi ★ A B) : Path (B a) (Π-apply ★ A B (Π-lambda ★ A B f) a) (f a) := idp (B a) (f a)
def Π-η (O : 𝟏) (A : Set) (B : A → Set) (a : A) (f : Pi ★ A B) : Path (Pi ★ A B) f (λ (x : A), f x) := idp (Pi ★ A B) f
def Sigma (O : 𝟏) (A : Set) (B : A → Set) : Set := summa (x: A), B x
def pair (O : 𝟏) (A: Set) (B: A → Set) (a: A) (b: B a) : Sigma ★ A B := (a, b)
def pr₁ (O : 𝟏) (A: Set) (B: A → Set) (x: Sigma ★ A B) : A := x.1
def pr₂ (O : 𝟏) (A: Set) (B: A → Set) (x: Sigma ★ A B) : B (pr₁ ★ A B x) := x.2
def Σ-β₁ (O : 𝟏) (A : Set) (B : A → Set) (a : A) (b : B a) : Path A a (pr₁ ★ A B (a ,b)) := idp A a
def Σ-β₂ (O : 𝟏) (A : Set) (B : A → Set) (a : A) (b : B a) : Path (B a) b (pr₂ ★ A B (a, b)) := idp (B a) b
def Σ-η (O : 𝟏) (A : Set) (B : A → Set) (p : Sigma ★ A B) : Path (Sigma ★ A B) p (pr₁ ★ A B p, pr₂ ★ A B p) := idp (Sigma ★ A B) p

def Path-1 (O : 𝟏) (A : Set) (x y : A) : Set := PathP (<_> A) x y
def idp-1 (O : 𝟏) (A : Set) (x : A) : Path A x x := <_> x
def transport (A B: Set) (p : PathP (<_> Set) A B) (a: A): B := transp p 0 a
def singl (A: Set) (a: A): Set := Σ (x: A), Path A a x
def eta (A: Set) (a: A): singl A a := (a, idp A a)
def contr (A : Set) (a b : A) (p : Path A a b) : Path (singl A a) (eta A a) (b, p) := <i> (p @ i, <j> p @ i /\ j)
def trans_comp (A : Set) (a : A) : Path A a (transport A A (<i> A) a) := <j> transp (<_> A) -j a
def subst (A : Set) (P : A -> Set) (a b : A) (p : Path A a b) (e : P a) : P b := transp (<i> P (p @ i)) 0 e
def subst-comp (A: Set) (P: A → Set) (a: A) (e: P a): Path (P a) e (subst A P a a (idp A a) e) := trans_comp (P a) e
def D (A : Set) : Set₁ := Π (x y : A), Path A x y → Set

def J (A: Set) (x: A) (C: D A) (d: C x x (idp A x)) (y: A) (p: Path A x y): C x y p
 := subst (singl A x) (\ (z: singl A x), C x (z.1) (z.2)) (eta A x) (y, p) (contr A x y p) d
def J-1 (O : 𝟏) (A : Set) (x : A) (C: D A) (d: C x x (idp A x)) (y: A) (p: Path A x y): C x y p
 := subst (singl A x) (\ (z: singl A x), C x (z.1) (z.2)) (eta A x) (y, p) (contr A x y p) d

def J-β (O : 𝟏) (A : Set) (a : A) (C : D A) (d: C a a (idp A a)) : Path (C a a (idp A a)) d (J A a C d a (idp A a))
 := subst-comp (singl A a) (\ (z: singl A a), C a (z.1) (z.2)) (eta A a) d

def MLTT-73 : Set :=
  Σ (Π-form  : Π (A : Set) (B : A → Set), Set)
    (Π-ctor₁ : Π (A : Set) (B : A → Set), Pi ★ A B → Pi ★ A B)
    (Π-elim₁ : Π (A : Set) (B : A → Set), Pi ★ A B → Pi ★ A B)
    (Π-comp₁ : Π (A : Set) (B : A → Set) (a : A) (f : Pi ★ A B), Path (B a) (Π-elim₁ A B (Π-ctor₁ A B f) a) (f a))
    (Π-comp₂ : Π (A : Set) (B : A → Set) (a : A) (f : Pi ★ A B), Path (Pi ★ A B) f (λ (x : A), f x))
    (Σ-form  : Π (A : Set) (B : A → Set), Set)
    (Σ-ctor₁ : Π (A : Set) (B : A → Set) (a : A) (b : B a) , Sigma ★ A B)
    (Σ-elim₁ : Π (A : Set) (B : A → Set) (p : Sigma ★ A B), A)
    (Σ-elim₂ : Π (A : Set) (B : A → Set) (p : Sigma ★ A B), B (pr₁ ★ A B p))
    (Σ-comp₁ : Π (A : Set) (B : A → Set) (a : A) (b: B a), Path A a (Σ-elim₁ A B (Σ-ctor₁ A B a b)))
    (Σ-comp₂ : Π (A : Set) (B : A → Set) (a : A) (b: B a), Path (B a) b (Σ-elim₂ A B (a, b)))
    (Σ-comp₃ : Π (A : Set) (B : A → Set) (p : Sigma ★ A B), Path (Sigma ★ A B) p (pr₁ ★ A B p, pr₂ ★ A B p))
    (=-form  : Π (A : Set) (a : A), A → Set)
    (=-ctor₁ : Π (A : Set) (a : A), Path A a a)
    (=-elim₁ : Π (A : Set) (a : A) (C: D A) (d: C a a (=-ctor₁ A a)) (y: A) (p: Path A a y), C a y p)
    (=-comp₁ : Π (A : Set) (a : A) (C: D A) (d: C a a (=-ctor₁ A a)), Path (C a a (=-ctor₁ A a)) d (=-elim₁ A a C d a (=-ctor₁ A a))),
    𝟏

def internalizing : MLTT-73
 := ( Pi ★, Π-lambda ★, Π-apply ★, Π-β ★, Π-η ★,
      Sigma ★, pair ★, pr₁ ★, pr₂ ★, Σ-β₁ ★, Σ-β₂ ★, Σ-η ★,
      Path-1 ★, idp-1 ★, J-1 ★, J-β ★,
      ★
    )
