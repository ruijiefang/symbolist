# symbolist
Symbolist is a simple engine for manipulating symbolic 
mathematics in Lisp-style S-expressions in OCaml. 
It is a work in progress).

## Build instructions

To build, type
```
make all
```

To clean a previous build, type
```
make clean
```

## Sample Usage: `grad` and `simplify`

The "grad" function takes in a variable name and an expression
and computes the derivative w.r.t. that variable. It supports
nested gradients:

d/dx ( d/dy ( f ) ) will be properly evaluated inside-out, first
expanding upon d/dy f, and then substituting the resultant expression
into d/dx.

The "simplify" function takes in a single expression and can
simplify elementary fractions: Below is a usage example.
```
=: ( simplify ( / 6 3 ) )
input string: ( simplify ( / 6 3 ) )
parsed expression: (simplify (/, Int 6, Int 3))
repl: simplify = (/, Int 2, Int 1)
=: ( simplify ( / ( * x 6 ) ( * x 3 ) ) )
input string: ( simplify ( / ( * x 6 ) ( * x 3 ) ) )
parsed expression: (simplify (/, (*, Var x, Int 6), (*, Var x, Int 3)))
repl: simplify = (/, (*, Int 2, Var x), (*, Int 1, Var x))
```
As we can see, 6*x / 3*x got simplified into 2*x / 1*x.

## Author

Ruijie Fang

## License

Open sourced under the MIT license.

