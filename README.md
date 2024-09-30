# LMLC2
LambdaMLCompiler is a transpiler of a pure subset of Caml toward the λ-calculus.

# Type inference
Thanks to OCaml, this transpiler has a type checker, which the version coded in C cruelly lacks.

# Proof
This compiler will (hopefully) be proven in Coq, the actual version (in the folder LMLCv2) isn't proved but is meant to resemble the output of the code extraction of the version actually in the Coq code.

## Languages

### Source : Subset of Caml
```
M, N,... ::= let x = M in N | M N | fun x -> M | (M, N) | M :: N | [M1;M2;...;Mn]
     | M @ N | M + N | M - N | M * N | M && N | (M || N)
     | M < N | M <= N | M > N | M >= N | M <> N | M = N | if C then M else N
     | n | true | false | (M)
```
For now, $n \in \mathbb N$.

### Object : Untyped λ-Calculus
```
M, N, ... ::= x | (M)N | λ x. M
```

We will often write `λ x1, x2, ..., xn. M` to denote `λ x1. λ x2. ... λ xn. M` and `(M) N_1 .. N_k` to denote `((...((M) N_1) ... ) N_k)`.

#### Caml objects representations :
- Naturals, booleans and couples : Church representation, respectively $n$, `true`, `false`, and `⟨a, b⟩`, are represented by `λ s, z. s^n z`, `λ t, e. t`, `λ t, e. e` et `λ z. z a b`.
- Integers : A couple of naturals `⟨n, m⟩` which stands for $n - m$ (⚠️ not implemented yet ⚠️)
- Lists : A list is defined as its `Fold_left` function : `[x1; x2; ...; xn]` is written `λ op init. op (xn op (xn-1 op (... (op x1 init)) ...)`

#### Possible extensions
- Change Church representation to a binary representation, to produce λ-terms of reasonable sizes.
- Integers : The main problem is that we then need a normalization function, mapping `⟨n, m⟩` to `⟨max n-m 0,max m-n 0⟩` and this could make the proof harder, especially if we want to minimize the use of such a function via some optimizations.
- Float/Double : Firstly because of the representation, secondly because the proof could impossible, we cannot consider float, we can instead consider rational numbers, with `⟨⟨n, m⟩, q⟩` standing for $\frac{n-m}{q}$.
