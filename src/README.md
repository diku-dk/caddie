# Notes on Combinatory AD

This implementation of combinatory AD (CAD) is a library, written in
Standard ML, that provides for both forward-mode AD (FAD) and
reverse-mode AD (RAD). The ultimate aim is for the implementation to
generate efficient gradient code (in different languages; e.g.,
Futhark) for code specified in a high-level (domain-specific)
functional language. The implementation first turns source code into
combinatory form, which can then be differentiated, resulting in (1)
code for evaluating the zero-order representation of the program and
(2) a linear-map representation of the derivative. The linear-map is
an abstract structure, which can be interpreted in a forward-mode
setting (for generating code according to a forward-mode AD strategy)
or be transposed (forming an adjoint) before being interpreted, which
will generate code according to a reverse-mode AD strategy.

The implementation takes care of avoiding expression swell by
differentiating and interpreting linear maps in a statement monad.

## Example 1

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

Expressions take the following form:

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
            |e1 ◇ e2|δ   =   ◇ ○ (|e1|δ × |e2|δ) ○ Δ
    |let x = e in e'|δ   =   |e'|(δ ○ π 2, x:π 1) ○ (|e|δ × Id) ○ Δ
           |(e1, e2)|δ   =   (|e1|δ × |e2|δ) ○ Δ
              |π i e|δ   =   π i ○ |e|δ
                |(e)|δ   =   |e|δ

The result of the translation is a point-free expression. We shall not
here provide type systems for expressions and point-free
expressions. Notice, however, that the point-free translation of an
expression `e` assumes that the provided variable assignment gives
projection definitions for all the free identifiers of `e`.

## Linear maps

Linear maps are defined according to the following grammar:

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

## Differentiation

Differentiation is defined on point-free expressions

## Other Examples

Try run the examples using `make`.

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
