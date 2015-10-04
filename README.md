# What is this

Just fooling around with binary representations of lambda calculus.

In particular Lambda.hs defines encodings for *simple* lambda terms:

A **list-binding** lambda term is a lambda term where lambdas can bind one or more variables instead of just one. A **simple** lambda term is then a **closed** list-binding lambda term where each nested lambda is also simple.

For example the Y combinator ```\f. (\x. f (x x)) (\x. f (x x))``` is not simple because the nested lambdas capture ```f```. This can be remedied by explicitly capturing: ```\f. (\f' x. f' (x x)) f ((\f' x. f' (x x)) f)```.

Lambda.hs contains three variants of essentially the same encoding, the only difference is what the bits mean when deciding whether we are parsing a **v**ariable, **b**ranch(application) or a nested **l**ambda. The three variables therefore are vbl bvl and lbv.

The encoding is
- Complete: every simple lambda term has an encoding
- Context free
- Correct by construction: the parse is either successful with some leftover input or is waiting for more input
- Not redundant: there is a bijection between alpha-equivalence classes and their encodings. Of course it's impossible to do this for beta-equivalence.

I'm interested in simple lambda terms because they force captures to be explicit, making it easier to write compilers for. They also have the neat property that the representation of nested lambdas are valid lambda terms themselves. For example the vbl encoding of the above simplified Y combinator is 

011011**010010010010**001011**010010010010**00

where the highlighted parts encode ```(\f' x. f' (x x))```.

Improvements could be made to the natural number encoding part, currently the encoding is literally a list of bits. However care must be taken not to become redundant. For example if we want to chain bit-blocks we need to make sure that e.g. [0000] does not encode the same number [0000, 0000] does.

# How do I run it

```runhaskell Lambda.hs```

For each variant(vbl, bvl, lbv) it prints ```n: p``` where ```p``` is the precentage of complete lambda encodings of ```n``` bits. If the percentage is higher the representation is "denser". Spoiler alert vbl wins.
