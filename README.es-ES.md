Per Martin-Löf: Intuitionistic Type Theory
==========================================

<img src="https://per.groupoid.space/img/per.jpg" height=400>

## Resumen

**Per** es un probador de teoremas táctico de MLTT-73 implementado en OCaml, que constituye un núcleo mínimo para un lambda cálculo dependientemente tipado, restringido para excluir el emparejamiento de patrones (pattern matching), las ligaduras let (let-bindings), los argumentos implícitos, los módulos, los espacios de nombres y la extensionalidad de funciones. Abarca universos, productos dependientes `Pi`, pares dependientes `Sigma` y tipos de identidad `Id`. Las refinaciones aseguran la totalidadd para los términos lambda definidos por el usuario mediante una comprobación de ocurrencia positiva. Se están analizando sus propiedades matemáticas, centrándose en la corrección, solidez, totalidad, canonicidad, decidibilidad y atributos relacionados relevantes para las matemáticas formales.

## Introducción

El comprobador de tipos opera sobre una sintaxis de términos que comprende:

* `Universe i`: Universos de tipos con nivel `i ∈ ℕ`.
* `Pi (x, A, B)`: Función dependiente, donde `A : Universe i` y `B : Universe j` bajo `x : A`.
  `Lam (x, A, t)`: Abstracción lambda con totalidad impuesta.
  `App (f, a)`: Aplicación de función.
* `Sigma (x, A, B)`: Tipos de pares dependientes.
  `Pair (a, b)`, `Fst p`, `Snd p` construcción y proyecciones.
* `Id (A, a, b)`: Tipo de identidad, con `Refl` a y eliminador `J`.

El juicio de tipado `Γ ⊢ t : T` se define a través de las funciones `infer` y `check`, con la igualdad definicional `Γ ⊢ t = t'` implementada mediante `equal`.

## Sintaxis

```OCaml
type term =
  | Var of name | Universe of level
  | Pi of name * term * term | Lam of name * term * term | App of term * term
  | Sigma of name * term * term | Pair of term * term | Fst of term | Snd of term
  | Id of term * term * term | Refl of term | J of term * term * term * term * term * term  (* J A a b C d p *)
```

## Semántica

### Igualdad Sintáctica `equal`

Igualdad estructural de términos bajo un entorno y contexto.

La función implementa la igualdad judgmental con sustitución para manejar variables ligadas, evitando la α-conversión explícita al asumir nombres frescos (una simplificación sobre los índices de de Bruijn completos [3]). El descenso recursivo asegura la congruencia, pero carece de normalización, lo que la hace más débil que la igualdad definicional de CIC, que incluye la β-reducción.

* **Casos Terminales**: Las variables `Var x` son iguales si los nombres coinciden; los universos `Universe i` si los niveles son idénticos.
* **Casos Recursivos**: `App (f, arg)` requiere la igualdad de la función y el argumento. `Pi (x, a, b)` compara dominios y codominios, ajustando el renombrado de variables mediante sustitución. `Inductive d` comprueba el nombre, el nivel y los parámetros. `Constr` y `Elim` comparan índices, definiciones y argumentos/casos.
* Por defecto: Devuelve falso para constructores que no coincidan.

**Teorema**. La igualdad es reflexiva, simétrica y transitiva módulo la α-equivalencia (cf. [1], Sección 2). Para `Pi (x, a, b)` y `Pi (y, a', b')`, la igualdad se mantiene si `a = a'` y `b[x := Var x] = b'[y := Var x]`, asegurando que la sustitución que evita la captura preserve el significado.

### Búsqueda de Variables de Contexto `lookup_var`

Recupera el tipo de una variable desde el contexto. Los contextos son los objetos en las categorías de Sustituciones.

* Busca en `ctx` el par `(x, ty)` usando `List.assoc`.
* Devuelve `Some ty` si se encuentra, `None` en caso contrario.

**Teorema**: La búsqueda de contexto está bien definida bajo la unicidad de los nombres (cf. [1], Sección 3). Si `ctx = Γ, x : A, Δ`, entonces `lookup_var ctx x = Some A`.

### Cálculo de Sustitución `subst`

Sustituye el término `s` por la variable `x` en el término `t`. Las sustituciones son morfismos en las categorías de Sustitución.

La comprobación de evitación de captura `if x = y` previene la captura de variables pero asume nombres ligados distintos, una simplificación sobre el renombrado completo o los índices de de Bruijn. Para Elim, la sustitución en el motivo y los casos asegura que las definiciones recursivas sigan siendo sólidas, alineándose con la semántica del eliminador de CIC.

* `Var`: Reemplaza `x` por `s`, deja los demás sin cambios.
* `Pi/Lam`: Omite la sustitución si la variable ligada hace sombra a `x`, de lo contrario recursa sobre el dominio y el cuerpo.
* `App/Constr/Elim`: Recursa sobre los subtérminos.

**Teorema**. La sustitución preserva el tipado (cf. [13], Lema 2.1). Si `Γ ⊢ t : T` y `Γ ⊢ s : A`, entonces `Γ ⊢ t[x := s] : T[x := s]` bajo condiciones adecuadas sobre x.

### Inducción de Igualdad Inferida `infer_J`

Asegura que `J (ty, a, b, c, d, p)` tenga tipo `c a b p` validando el motivo, el caso base y la ruta frente a la regla de eliminación de igualdad de CIC.

La función `infer_J` implementa la regla de eliminación dependiente para tipos de identidad en el Cálculo de Construcciones Inductivas (CIC), permitiendo pruebas y computaciones sobre la igualdad (por ejemplo, `symmetry : Π a b : ty, Π p : Id (ty, a, b), Id(ty, b, a)`). Verifica el tipo del término `J (ty, a, b, c, d, p)` asegurando que `ty : Universe 0` sea el tipo subyacente, `a : ty` y `b : ty` sean los extremos, `c : Π (x:ty), Π (y:ty), Π (p: Id(ty, x, y)), Type0` sea un motivo sobre todas las rutas, `d : Π (x:ty), c x x (Refl x)` maneje el caso reflexivo, y `p : Id(ty, a, b)` sea la ruta que se está eliminando. La función construye variables frescas para definir los tipos del motivo y del caso base, verifica cada componente y devuelve `c a b p` (normalizado), reflejando el resultado de aplicar el motivo a la ruta específica.

**Teorema**. Para un entorno `env` y un contexto `ctx`, dado un tipo `A : Type_i`, términos `a : A`, `b : A`, un motivo `C : Π (x:A), Π (y:A), Π(p:Id(A, x, y)),Type_j`, un caso base `d : Π(x:A), C x x (Refl x)`, y una ruta `p : Id(A, a, b)`, el término `J (A, a, b, C, d, p)` está bien tipado con tipo `C a b p`. (Referencia: CIC [1], Sección 4.5; Regla de Eliminación del Tipo de Identidad).

### Inferencia de Tipos `infer`

Infiere el tipo del término `t` en el contexto `ctx` y el entorno `env`.

Para `Pi` y `Lam`, los niveles de universo aseguran la consistencia (por ejemplo, `Type i : Type (i + 1)`), mientras que `Elim` maneja la inducción, crítica para la eliminación dependiente. Tenga en cuenta que el argumento lambda debe estar tipado para facilitar la síntesis de tipos [13].

### Comprobación de Universos `check_universe`

Asegura que `t` sea un universo, devolviendo su nivel. Infiere el tipo de `t`, esperando `Universe i`.

Esta función auxiliar impone la jerarquía de universos, evitando paradojas (por ejemplo, Tipo : Tipo). Se apoya en `infer`, asumiendo su corrección, y lanza errores para tipos que no sean universos, alineándose con la estratificación de ITT.

**Teorema**: La comprobación de universos es decidible (cf. [13]). Si `ctx ⊢ t : Universe i`, entonces `check_universe env ctx t = i`.

### Comprobación `check`

Comprueba que `t` tenga el tipo `ty`.

* `Lam`: Asegura que el dominio sea un tipo, extiende el contexto y comprueba el cuerpo frente al codominio.
* Por defecto: Infiere el tipo de t, normaliza ty y comprueba la igualdad.

La función aprovecha el tipado bidireccional: casos específicos (por ejemplo, `Lam`) comprueban directamente, mientras que el caso por defecto sintetiza vía `infer` y compara con un ty normalizado, asegurando la igualdad definicional (β-reducción). La completitud depende de que `normalize` termine (normalización fuerte de ITT) y que `equal` capture la igualdad judgmental.

**Teorema**. La comprobación de tipos es completa (cf. [1], Normalización). Si `ctx ⊢ t : T` en la teoría de tipos, entonces `check env ctx t T` tiene éxito, asumiendo la normalización y una inferencia sólida.

### Reductor β de un paso `reduce`

Realiza una β-reducción de un paso o una eliminación inductiva.

La función implementa una estrategia de reducción de un paso que combina la β-reducción de ITT con la ι-reducción de CIC para inductivos. El caso `App (Lam, arg)` aplica directamente la sustitución, mientras que `Elim (Constr)` utiliza `apply_case` para manejar la inducción, asegurando que las llamadas recursivas preserven el tipado a través del motivo p. El caso `Pi`, aunque poco convencional, soporta la computación a nivel de tipos, consistente con la flexibilidad de CIC.

* `App (Lam, arg)`: Sustituye el argumento en el cuerpo lambda (β-reducción).
* `App (Pi, arg)`: Sustituye el argumento en el codominio (β-reducción a nivel de tipos).
* `App (f, arg)`: Reduce f, luego arg si f no ha cambiado.
* Por defecto: Devuelve el término sin cambios.

**Teorema**. La reducción preserva el tipado (cf. [8], Lema de Normalización, Reducción del Sujeto). Si `ctx ⊢ t : T` y `t → t'` vía β-reducción o eliminación inductiva, entonces `ctx ⊢ t' : T`.

### Normalización `normalize`

Esta función reduce completamente un término t a su forma normal aplicando iterativamente reducciones de un paso vía `reduce` hasta que no ocurran más cambios, asegurando la terminación para términos bien tipados.

Esta función implementa la normalización fuerte, una piedra angular de MLTT [9] y CIC [1], donde todas las secuencias de reducción terminan. La iteración de punto fijo se basa en las reducciones de un paso de `reduce` (β para lambdas, ι para inductivos), con `equal` actuando como el oráculo de terminación. Para `plus 2 2`, avanza hacia `succ succ succ succ zero`, terminando en una forma de constructor.

**Teorema**. La normalización termina (cf. [1]. Normalización Fuerte vía CIC). Todo término bien tipado en el sistema tiene una forma normal bajo reducciones β e ι.

## Conclusión

La elegancia de Per descansa sobre una base teórica firme. Aquí, reflexionamos sobre meta-teoremas clave para MLTT Clásico con Tipos Inductivos Generales, basándonos en el linaje de CIC:

* **Solidez y Completitud**: El comprobador de tipos de Per es sólido: cada término que acepta tiene un tipo bajo las reglas de MLTT [Paulin-Mohring, 1996]. Esto asegura que cada término aceptado por Per sea tipable en la teoría subyacente. Respecto al algoritmo de comprobación de tipos bidireccional, el contexto se gestiona adecuadamente [Harper & Licata, 2007]. La interacción de los modos de inferencia y comprobación garantiza esta propiedad.
* **Canonicidad, Normalización y Totalidad**: La canonicidad garantiza que cada término cerrado de tipo `Nat` se normalice a `zero` o `succ n` [Martin-Löf, 1984]. El `normalize` de Per logra la normalización fuerte —cada término se reduce a una forma normal única— gracias a la positividad estricta de CIC [Coquand & Paulin-Mohring, 1990]. La totalidad es consecuencia: todas las funciones bien tipadas terminan, como se ve en `list_length` reduciéndose a `succ (succ zero)`.
* **Consistencia y Decidibilidad**: La consistencia asegura que no exista una prueba de ⊥, mantenida por la normalización y la ausencia de paradojas como la de Girard [Girard, 1972]. La comprobación de tipos es decidible en Per, ya que nuestro algoritmo termina para entradas bien formadas, aprovechando la igualdad decidible de CIC [Asperti et al., 2009].
* **Conservatividad e Inicialidad**: Per es conservador sobre sistemas más simples como el Sistema F, añadiendo tipos dependientes sin alterar las verdades proposicionales [Pfenning & Paulin-Mohring, 1989]. Los tipos inductivos como Nat satisfacen la inicialidad —cada morfismo de álgebra desde Nat hacia otra estructura está definido unívocamente— asegurando la universalidad categórica [Dybjer, 1997].

### Solidez

* Definición: Se mantienen la preservación del tipo y la consistencia lógica.
* Declaración Formal: 1) Si `Γ ⊢ t : T` e `infer t = t'`, entonces `Γ ⊢ t' : T`; 2) No existe `t` tal que `Γ ⊢ t : Id (Universe 0, Universe 0, Universe 1)`.
* Prueba: Preservación vía `reduce` terminante; consistencia vía positividad e intensionalidad.
* Estado: Sólido, impuesto al rechazar lambdas no totales.

### Completitud

* Definición: El comprobador de tipos captura todos los términos bien tipados de MLTT dentro de su marco bidireccional.
* Declaración Formal: Si `Γ ⊢ 𝑡 : T`, entonces `infer Δ Γ 𝑡 = T` o `check Δ Γ 𝑡 T` se cumple bajo un `Δ` adecuado.
* Estado: Completo relativo al algoritmo implementado.

### Canonicidad

* Definición: La reducción alcanza una forma normal; la igualdad es decidible.
* Declaración Formal: `equal Δ Γ t t'` termina, reflejando las reducciones beta y eta parciales de `normalize` en `normalize`.
* Estado: Satisfecha dentro del alcance de las reducciones implementadas.

### Totalidad

* Definición: Todas las construcciones bien tipadas terminan bajo reducción.
* Declaración Formal: 1) Para `Inductive d : Universe i`, cada `Constr (j, d, args)` es total; 2) Para `t : T` con `Ind` o `J`, `reduce t` termina; 3) Para `Lam (x, A, t) : Pi (x, A, B)`, `reduce (App (Lam (x, A, t), a))` termina para todo `a : A`; 4) `normalize Δ Γ t` termina.

### Consistencia

El sistema es lógicamente consistente, lo que significa que no existe ningún término `t` tal que `Γ ⊢ t : ⊥`. Esto se mantiene mediante la normalización y la ausencia de paradojas como la de Girard [Girard, 1972].

### Decidibilidad

* Definición: La comprobación de tipos y la igualdad son computables.
* Declaración Formal: `infer` y `check` terminan con un tipo o un `TypeError`.
* Estado: Decidible, mejorado por comprobaciones de terminación en expresiones lambda.

## Artefacto

```
https://per.groupoid.space/

  🧊 MLTT Theorem Prover version 0.5 (c) 2025 Groupoїd Infinity

For help type `help`.

Starting proof for: Π(n : Nat).Nat
Goal 1:
Context: []
⊢ Π(n : Nat).Nat

1 goals remaining
>
```

## MLTT

[9]. Martin-Löf, P. Intuitionistic Type Theory. 1980.<br>
[10]. Thierry Coquand. An Algorithm for Type-Checking Dependent Types. 1996. <br>

## PTS

[11]. N. G. de Bruijn. Lambda Calculus Notation with Nameless Dummies. 1972. <br>
[12]. J.-Y. Girard. Interprétation fonctionnelle et élimination des coupures. 1972. <br>
[13]. Thierry Coquand, Gerard Huet. <a href="https://core.ac.uk/download/pdf/82038778.pdf">The Calculus of Constructions</a>. 1988.<br>

## Autor

Namdak Tonpa
