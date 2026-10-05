# The Cube documentation

Cube runs on a cubical reconstruction of extensional type theory that enjoys a judgmental version of the unicity of identity proofs principle (UIP), meaning that any two elements of the same path type are the same up to judgmental identity. Below you will find a short reference manual on the basics of Cube. Here we assume that the user is relatively familiar with cubical type theory. See [[1](#BEN21)] for a friendly introduction. 

## The type theory of Cube

To be more precise, Cube implements a version of XTT [[2](#SAG19), [3](#SAG19)]. Currently, the main difference between the type theory of Cube and XTT is that the latter is essentially formulated with structural dimensions and built-in dependent function types, dependent pair types, dependent path types, booleans, and closed notion of universe that rests on a type-case operator [[2](#SAG19), appx. A]. In XTT, type-case allows pattern-matching on type formers, and, as a consequence, universes cannot remain open-ended. By contrast, the type theory of Cube supports user-defined inductive type families and is committed to an open-ended notion of universe, meaning that it does not have a type-case operator. It runs on built-in type formers for dependent functions, dependent pairs, dependent path, the empty type, the interval, a cumulative hierarchy of universes à la Russell, and inductively defined type families. Thus, the type theory of Cube is less extensional than that of XTT [[3](#SAG19), §2.3.4].

## Usage

There are a number of commands for inductively defining type families, entering the proof environment, type inference, term evaluation, importing files for the modularizion of proofs, declaring universe levels, and extracting and priting terms from definitions and theorems:

### Inductive environment

The syntax for defining an indexed inductive type is:

```inductive foo : type l
| constructor1 : ... → foo
| constructor2 : ... → foo
...
| constructorn : ... → foo
```

Recursors are automatically generated under the name `foorec`. 

### Proof environment

The proof environment is the main command where definitions are stated and theorems and lemmas are proven. Syntactically speaking, there is no difference between defintitions and theorems and lemmas. Users can use `def`, `definition`, `thm`, `theorem`, `lem`, and `lemma` interchangeably.

```
  def [name-of-theorem] [context] :
   [type] := [term]
```

Contexts are lists of variable declarations. Explicit variables are enclosed with `(` and `)` and must be passed as parameters when the definition or theorem is reused later. Implicit variables are enclosed with curly braces `{` and `}` and can be inferred by the elaborator. Multiple variables of the same type can be declared at the same time.

Types and their terms are determined by Cube's raw language, which is based on a Curry-style syntax. Currently, it contains the following built-in type-formers, constructors, and eliminators for the dependent function type, dependent path type, empty type, interval, and universe types, where M, N arbitrary terms:

Primitive types | Notation | Constructors | Eliminators
------------ | ------------- | ------------- | -------------
Dependent function type	| Π (x : M), N | λ x , M | M N
Dependent path type | pathd K M N | < x > M | M @ N
Interval | I or 𝕀 | i0 and i1 | 
Empty type | void | | abort M
Universe type | type n | 

In addition, the user can also have `_` and `?` as placeholders in any expression. The former is used to synthesize an implicit assumption or fail after a number of steps, evaluating and displaying the type of the current goal. The latter is used to display the type of current goal directly without evaluation.

Moreover, the language also contains two primitive functions known as Kan operations:

- Coercion. This is a cubical generalization of Leibniz's indiscernibility of identicals. Essentially, coercion states that, given any line type I → A and any term M : A i, where i j : I, we have a term of the type A j, called the coercion of M in A, and denoted by `coe i j A M`.

- Composition. Simply put, composition states that any open box has a lid. More precisely, given any three lines M N N' : I → A such that (i) the initial point of M is judgmentally equal to the initial point of N and (ii) the terminal point of M is judgmentally equal to the initial point of N', the composition also asserts the existence of square I → I → A whose top face is M, left face is N, right face is N'. The composition is written `hcom i j M | i0 → N0 | i1 → N1`.

Because the unicity of identity proofs holds judgmentally, Cube rests on a simplified version of composition in which, unlike other cubical type theories, there are no higher-dimensional composition scenarios. 

### Type inference

The syntax for type inference is:

```
  infer [context] : foo
```

### Evaluation

Cube does not rely on normalization-by-evaluation. Instead, evaluation is untyped due to philosophical reasons having to do with closer adherence to the meaning explanations of type theory. The syntax for term evaluation is:

```
  eval foo
```

### File import

This command imports a specified file into the current file. The syntax is 

`import [filename]`

### Universe declaration 

This declares a universe level variable according to the syntax 

`universe [id]`

Note that if you are using the VS Code Extension you may type the small script ell `ℓ` with `\ell`.

### Term extraction 

This extracts and prints the term corresponding to a definition or theorem with the syntax 

`print [name]`


### Examples

For a few simple examples, note that nondependent function application and function extensionality can be proven as:

````
def ap {A B : type ℓ} (f : A → B) {a b : A} :
  path A a b → path B (f a) (f b) :=
λp, <i> f (p @ i)

def funext {A : type ℓ} {B : A → type ℓ} (f g : Π (x : A), B x) :
  (Π (x : A), path (B x) (f x) (g x)) → path (Π (x : A), B x) f g :=
λh, <i> (λ x, (h x) @ i)

````

More examples can be found in the [library](https://github.com/bbentzen/cube/blob/master/lib/).

## References

<a name="BEN19">[1]</a>
Bruno Bentzen. Naive cubical type theory. 
Mathematical Structures in Computer Science, 31, pp. 1205–1231, 2021.
[doi:10.1017/S096012952200007X](https://doi.org/10.1017/S096012952200007X), [arXiv:1911.05844](https://arxiv.org/abs/1911.05844).

<a name="SAG19">[2]</a>
Jonathan Sterling, Carlo Angiuli, Daniel Gratzer. 
Cubical syntax for reflection-free extensional equality. 
In Herman Geuvers (ed.), 4th International Conference on Formal Structures for Computation and Deduction (FSCD 2019), volume 131 of Leibniz International Proceedings in Informatics (LIPIcs), pages 31:1-31:25.
[doi:10.4230/LIPIcs.FSCD.2019.31](https://doi.org/10.4230/LIPIcs.FSCD.2019.31), [arXiv:1904.08562](https://arxiv.org/abs/1904.08562).

<a name="SAG22">[3]</a>
Jonathan Sterling, Carlo Angiuli, Daniel Gratzer. 
A Cubical Language for Bishop Sets. 
Logical Methods in Computer Science, 18 (1), 2022.
[doi:10.46298/lmcs-18(1:43)2022](https://doi.org/10.46298/lmcs-18(1:43)2022), [arXiv:2003.01491](https://arxiv.org/abs/2003.01491).