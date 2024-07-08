# caddie [![CI](https://github.com/diku-dk/caddie/workflows/CI/badge.svg)](https://github.com/diku-dk/caddie/actions)

Combinatory Automatic Differentiation. Much of the code for Caddie is 
based on the paper [Combinatory Adjoints and Differentiation](https://elsman.com/pdf/msfp22.pdf) [1].

## Combinatory AD

This implementation of combinatory AD is a standalone tool, which
provides for both forward-mode AD (FAD) and reverse-mode AD (RAD). The
ultimate aim is for the implementation to generate efficient gradient
code (in different languages; e.g., [Futhark](https://futhark-lang.org)) for code specified in a
high-level (domain-specific) functional language. The implementation
first turns source code into combinatory form, which can then be
differentiated, resulting in (1) code for evaluating the zero-order
representation of the program and (2) a linear-map representation of
the derivative. The linear-map is an abstract structure, which can be
interpreted in a forward-mode setting (for generating code according
to a forward-mode AD strategy) or be transposed (forming an adjoint)
before being interpreted, which will generate code according to a
reverse-mode AD strategy.

The implementation takes care of avoiding expression swell by
differentiating and interpreting linear maps in a statement monad.

## An Introductory Example

We first give a simple introductory example before we describe the
implementation.

Consider the function

    let f (x1,x2) = ln (x1 * cos x2)

This function is turned into the following definition in point-free
notation format:

    let f = ln ○ ((*) ○ ((π 1 × (cos ○ π 2)) ○ Δ))

The combinatory AD framework defines a _differentiation operator_ `D`
of the following type:

    D : (V → W) ⇒ V ⇒ (W × (V ↦ W)) M

Here `⇒` denotes a function at the meta level, whereas `→` denotes a
function at the expression level. Further, we use `↦` to indicate that
a function is a linear map.  The type constructor `M` denotes a
`let`-binding context monad, which is used for avoiding expression
swell (the monad keeps track of a series of `let`-bindings).

The result of differentiating `f` is thus a pair of a term representing the
expression `f(x1,x2)` and a linear map, both appearing inside a
`let`-binding context:

    D f (x1,x2) =
       let v9 = cos x2
       in ( ln(x1*v9)
          , pow(~1.0)(x1*v9)*) •
            (+) •
            ((*v9) ⊕ (x1*)) •
            (π 1 ⊕ (~(sin x2)*) • π 2) •
            Δ
          )

Notice how the `let`-binding context ensures that the term `cos x2` is
evaluated only once.

For reverse-mode AD, the linear map is transposed into the following
linear map:

    let f^ (x1,x2) =
      let v9 = cos x2
      in (+) •
         ((Id ⊕ zero) • Δ ⊕ (zero ⊕ id) • Δ • (~(sin(x2)) *)) •
         ((*v9) ⊕ (x1*)) •
         Δ •
         (pow(~1.0)(x1*v9)*)

Notice that `v9` appears twice in the linear map definition. If `D f`
has type `V ⇒ (W × (V ↦ W)) M`, `f^` has type `V ⇒ (W ↦ V) M`.
For the concrete case, `f^ (x1,x2)` has type `(ℝ ↦ ℝ×ℝ) M`.

By "applying" the linear map to the value `1.0`, we get the following
term (in a `let`-binding context):

    let f^ (x1,x2) 1.0 =
       let v9 = cos x2
       let v10 = pow(~1.0)(x1*v9)
       let v11 = v10*v9
       let v12 = ~(sin(x2)) * (x1*v10)
       in (v11, v12)

## Expressions

We use `r` to range over reals (ℝ). Unary operators (⍴) and binary
operators (◇) are the following:

    ⍴ ::= ln | sin | cos | exp | pow r | ~
    ◇ ::= + | * | -

Expressions take the following forms:

    e ::= r | x | ⍴ e | e ◇ e | (e,e) | π i e | (e)
        | let x = e in e

## Point-Free Notation

Point-free notation is defined according to the following grammar:

    p ::= p ○ p | π i | K e | p × p | Δ | Id | ⍴ | ◇ | (p)

Here is an overview of the semantics of the main point-free
combinators:

    ⟦Δ⟧   : V → V × V
          = λx.(x,x)
    ⟦π 1⟧ : A × B → A
          = λ(x,y).x
    ⟦π 2⟧ : A × B → B
          = λ(x,y).y
    ⟦K e⟧ : A → B
          = λ_.e
    ⟦Id⟧  : V → V
          = λx.x
    ⟦×⟧   : (A → B) × (C → D) → (A × C) → (B × D)
          = λ(f,g).λ(x,y).(f x,g y)
    ⟦○⟧   : (B → C) × (A → B) → A → C
          = λ(f,g).λx.f(g x)

Expressions can be translated into point-free expressions by explicit
environment-passing, which also supports `let`-bindings. In the
following, we use `δ` to range over _variable assignments_, written
`x1:p1,...,xn:pn`, which are used to map variables to compositions of
projections. When `δ = x1:p1,...,xn:pn`, we write `δ ○ p` to mean
`x1:(p1 ○ p),...,xn:(pn ○ p)`. When `e` is an expression and `δ` is a
variable assignment, we define the _point-free translation_ of `e`,
written `|e|δ`, as follows:

                   |x|δ   =   δ(x)
                   |r|δ   =   K r
                 |⍴ e|δ   =   ⍴ ○ |e|δ
             |e₁ ◇ e₂|δ   =   ◇ ○ (|e₁|δ × |e₂|δ) ○ Δ
    |let x = e₁ in e₂|δ   =   |e₂|(δ ○ π 2, x:π 1) ○ (|e₁|δ × Id) ○ Δ
            |(e₁, e₂)|δ   =   (|e₁|δ × |e₂|δ) ○ Δ
               |π i e|δ   =   π i ○ |e|δ
                 |(e)|δ   =   |e|δ

The result of the translation is a point-free expression. We shall not
here provide type systems for expressions and point-free
expressions. Notice, however, that the point-free translation of an
expression `e` assumes that the provided variable assignment gives
definitions (e.g., projections from the main argument tuple) for all
the free identifiers of `e`.

## Linear maps

Let `V` and `W` be vector spaces over a field `K`. Semantically then,
a function `f` from `V` to `W` is a _linear map_, written `f: V ↦ W`,
if the following two properties hold:

    1. f (x + y) = f(x) + f(y)     ∀x,y ∈ V
    2. f (c * x) = c * f(x)        ∀c ∈ K, ∀x ∈ V

In the following, we shall define a language for composing linear maps
from simpler linear maps. The composed maps are then linear by
construction.

We define linear maps according to the following grammar:

    m ::= Δ | (+) | ~ | π i | 0 | Id | m ⊕ m
        | m • m | (e◇) | (◇e) | (m)

Here `◇` represents bi-linear functions and `⊕` represents the
linear-map counterpart of the point-free `×` operator. Similar to how
we define the semantics of point-free expressions, we define
the semantics of linear-map representations as follows:

    ⟦Δ⟧  : V ↦ V × V
         = λx.(x,x)

    ⟦(+)⟧  : V × V ↦ V
         = λ(x,x).x+x

    ...

    ⟦⊕⟧  : (A ↦ B) × (C ↦ D) → (A × C) ↦ (B × D)
         = λ(f,g).λ(x,y).(f x,g y)

    ⟦•⟧  : (B ↦ C) × (A ↦ B) → A ↦ C
         = λ(f,g).λx.f(g x)

    ⟦(e◇)⟧  : V ↦ V
         = λx.⟦e⟧◇x

    ⟦(◇e)⟧  : V ↦ V
         = λx.x◇⟦e⟧

By giving a grammar for linear maps, and by treating them as separate
semantic objects, we an later choose different representations for
them, such as a combination of composition of dense and sparse
matrices.

## Differentiation

Differentiation is defined on point-free expressions. Here we give a
non-monadic version of differentiation. Notice again that `A ⇒ B`
denotes a function from `A` to `B` at the meta-level. We use `V → W`
to denote expressions that represent functions taking a value of type
`V` as input and returns a value of type `W` as a result. We use the
notation `A ⊠ B` to denote the type of meta pairs and we allow
ourselves to use `Let`-notation to deconstruct such meta pairs. We
also assume a function `D⍴ : V ⇒ W ⊠ (V ↦ W)` that specifies how
primitives are differentiated. For instance, `Dcos : ℝ ⇒ ℝ ⊠ (ℝ ↦ ℝ)`
is defined by `Dcos (x) = (cos x, ((~sin x)*))`. Here is the
definition of differentiation:

    D : (V → W) ⇒ V ⇒ W ⊠ (V ↦ W)

    D (g ○ f) x =
	  Let (fx, f'x) = D f x
	  Let (gfx,g'fx) = D g fx
	  In (gfx, g'fx • f'x)

    D (K y) x = (y, 0)

    D (π i) x = (π i x, π i)

	D (f × g) x =
	  Let (fx, f'x) = D f (π 1 x)
	  Let (gy, g'y) = D g (π 2 x)
	  In ((fx,gy), f'x ⊕ g'y)

	D (Δ) x = ((x,x), Δ)

	D (Id) x = (x, Id)

    D (⍴) x = D⍴ x

    D (◇) x = (◇ x, (+) • ((◇ π 2) ⊕ (π 1 ◇)))

	D (+) x = ((+)x, (+))

Now, _forward-mode automatic-differentiation_ of a point-free
expression `p` with respect to an argument `x`, written `p'(x)`, is
defined by the equation

    p' : V ⇒ V ↦ W
    p' (x) = Let (_, m) = D p x
	         In m

To give a definition for reverse-mode automatic-differentiation, we
first need to give a definition for what it means to take the adjoint
of a linear map.

## The Adjoint of a Linear Map

When `m : V ↦ W` is a linear map expression, the _adjoint_ of `m`,
written `Adj(m)`, is a linear map of type `W ↦ V`, defined according to
the following rules:

    Adj : (V ↦ W) ⇒ (W ↦ V)

	Adj (0) = 0

	Adj (Id) = Id

	Adj (Δ) = (+)

	Adj ((+)) = Δ

	Adj (~) = ~

    Adj (π 1) = (Id ⊕ 0) • Δ

    Adj (π 2) = (0 ⊕ Id) • Δ

    Adj (m₁ • m₂) = Adj (m₂) • Adj (m₁)

	Adj (m₁ ⊕ m₂) = Adj (m₁) ⊕ Adj (m₂)

	Adj ((e*)) = (e*)     if * : ℝ × ℝ → ℝ           (multiplication)
	Adj ((*e)) = (*e)     if * : ℝ × ℝ → ℝ           (multiplication)

	Adj ((e·)) = (*e)     if · : ℝⁿ × ℝⁿ → ℝ            (dot product)
	Adj ((·e)) = (*e)     if · : ℝⁿ × ℝⁿ → ℝ            (dot product)

	Adj ((e×)) = (e×)     if × : ℝ × ℝⁿ → ℝⁿ         (scalar product)
	Adj ((×e)) = (·e)     if × : ℝ × ℝⁿ → ℝⁿ         (scalar product)

Notice that taking the adjoint of a linear map defined as a section operator is inherently dependent on the
particular binary operator. For instance, we see that the adjoint of a
right-section `(×e) : ℝ → ℝⁿ` of a partially applied scalar product is defined in
terms of a dot product `(·e) : ℝⁿ → ℝ`.

It holds that if `m : V ↦ W` and `Adj m` is defined, then `Adj (Adj m) = m`.

As an example, we see that `Adj (Adj (π 1))` = `Adj((Id ⊕ 0) • Δ)` =
`Adj(Δ) • Adj(Id ⊕ 0)` = `(+) • (Adj(Id) ⊕ Adj(0))` = `(+) • (Id ⊕ 0)`
= `((+) • (Id ⊕ 0)) • (π 1 ⊕ π 2)` = `(+) • ((Id ⊕ 0) • (π 1 ⊕ π 2))`
= `(+) • ((Id • π 1) ⊕ (0 • π 2))` = `(+) • (π 1 ⊕ 0)` = `π 1`.

## Reverse-mode Automatic Differentiation

We can now define _reverse-mode automatic-differentiation_ of a
point-free expression `p` with respect to an argument `x`, written
`p^(x)`, by the equation

    p^ : V ⇒ W ↦ V
    p^ (x) = Let (_, m) = D p x
	         In Adj m

## Value Domains

We have not yet said anything about how value domains (e.g., the `V`
in the type for `p^` above) are implemented. In fact, the
implementation is parametric in the choice of the value domain. In
other words, the implementation, which is written in Standard ML, can
choose to use the underlying ML value domain for representing
values. Another representation is to use a term representation, which
allows for term inspection and for emitting residual code in a
suitable language of choice (e.g., Futhark).

## Running the Examples

Try run the examples using `make`. The example definitions are located
in the `src/tests` directory (see for instance
[ad_ex0.sml](src/tests/ad_ex0.sml), [rad_ex1.sml](src/tests/rad_ex1.sml), and
[ba.sml](src/tests/ba.sml)). The implementation does not yet feature a
parser, which means that new examples are required to be embedded in
SML source code.

Here is an overview over the examples:

 | Source                           | Output                              |
 |----------------------------------|-------------------------------------|
 | [ad_ex0.sml](src/tests/ad_ex0.sml)   | [ad_ex0.out](src/tests/ad_ex0.out.ok)   |
 | [ad_ex1.sml](src/tests/ad_ex1.sml)   | [ad_ex1.out](src/tests/ad_ex1.out.ok)   |
 | [ba.sml](src/tests/ba.sml)           | [ba.out](src/tests/ba.out.ok)           |
 | [rad_ex0.sml](src/tests/rad_ex0.sml) | [rad_ex0.out](src/tests/rad_ex0.out.ok) |
 | [rad_ex1.sml](src/tests/rad_ex1.sml) | [rad_ex1.out](src/tests/rad_ex1.out.ok) |

## Conditionals

Conditional expressions and point-free notation for conditionals are
added as follows:

    e ::= ... | if e then e else e

    p ::= ... | if e then p else p

The semantics of the point-free conditional expression syntax is
defined, straightforwardly, as follows:

    ⟦if e then p1 else p2⟧ : V → W
      = if ⟦e⟧ then ⟦p1⟧ else ⟦p2⟧

Similarly, linear-map support for conditionals can be provided as
follows.

    m ::= ... | if e then m M else m M

Notice that a linear-map expression results in a linear map when
evaluated. The semantics of the linear-map conditional construct is
defined as follows:

    ⟦if e then m1 else m2⟧ : V ↦ W
      = if ⟦e⟧ then ⟦m1⟧ else ⟦m2⟧

We can now extend the definition of the `D` function to work for
conditional point-free notation:

    D (if e then p1 else p2) v =
      = Let M1 = D p1 v
        Let M2 = D p2 v
        Let (e1M,m1M) = Split M1
        Let (e2M,m2M) = Split M2
        ret ( if e then e1M else e2M,
              if e then m1M else m2M)
        ))

    D (if e then p1 else p2) v =
      = Let (C1,e1,m1) = run(D p1 v) In
        Let (C2,e2,m2) = run(D p2 v) In
        ret ( if e then C1 e1 else C2 e2,
              if e then m1 else m2)
        ))

## Array Combinators

    e ::= ... | map (λx.e) e | repl e e

    p ::= ... | map p | repl

    m ::= ... | repl e

Translation to point-free notation:

    |map (λx.e₁) e₂|δ   =   map (|e₁|(δ ○ π₂, x: π₁)) ○ (|e₂|δ × Id) ○ Δ

How do we differentiate `map p`?

# References

[1] Martin Elsman, Fritz Henglein, Robin Kaarsgaard, Mikkel K. Mathiesen, and Robert Schenck. Combinatory Adjoints and Differentiation. In Ninth Workshop on Mathematically Structured Functional Programming (MSFP 2022). Munich, Germany. April, 2022. [PDF](https://elsman.com/pdf/msfp22.pdf).
