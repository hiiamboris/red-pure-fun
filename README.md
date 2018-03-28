# red-pure-fun
## Purely functional DSL for Red

This is an experiment in building a dialect that will:
- allow computing pure expressions in the middle of Red code

  point is: when one sees a pure invocation, one is 100% sure it didn't shoot his ducks
- do so in a declarative, orderless manner

  point is: tell the parser how X and Y and so and so can be computed and let it decide for itself if it needs to compute them and in what order
- allow using recursive expressions, leveraging tail-call optimization when possible

  point is: get rid of loops to achieve better conciseness and readability of the code
- be very simple, no sophisticated type inference (as a result, no laziness), just the bare minimum

## quick start

download, run pure-fun-test.red, the test is the best explanation ;)

some more info is in the file headers too

## status

early alpha, very very early

proves the concept, fun to play with, but slow as hell: can't handle a map() over 100 items

suspended for now until I find a way to speed it up, like 100 times or so

might have lots of bugs yet

syntax is a subject to change at any time

## syntax

best shown by the examples in pure-fun-test.red

but here's some short one:
```
paren-join: func [x y] [ as paren! append (copy to-block x) y ]

rules: [
	head b: => [ :first b ]
	rest b: => [ :next b ]
	x: ~ y: => [ :paren-join x y ]			;-- (thing ~ thing) concatenates 2 paren expressions into one
	x: + y: => [ :add x y ]
	impure-join b: x: => [:append/only b x]
	map _ [] => [[]]
	map f: b: => [map-tco (:copy []) f b]
	map-tco c: _ [] => [c]
	map-tco c: f: b: => [
		map-tco (impure-join c (f ~ head b)) f (rest b)
	]
]
eval/using [
  map (1 +) [1 2 3]
] rules
```
should return: `[2 3 4]`

`eval` is given an expression that is matched against a set of patterns specified by `rules`

#### in the pattern:

words are matched as is (incl. ~ and +)

anything except words is matched as is (1, 2, [], "string", you name it)

set-words (x: y: ...) are catch-all patterns that match anything but words and use it as a named argument

a repeated set-word (f: x: y: x:) only matches it's first bound value

_ is a catch-all pattern that matches anything but words, without binding it

#### in the expression:

get-words are used to call normal Red functions from the global context

## evaluation order

is similar to Red/Rebol: subexpressions come first

suppose I have an expression `a b c d`, then it is evaluated in the following order:
```
 a
   b
 a b
     c
   b c
 a b c
       d
     c d
   b c d
 a b c d
```

if at some point, a pattern matches, say, at `b c`,
the subpattern gets replaced with the result of the subexpression specified by the rule
and it becomes `a rslt d` and continues with `a rslt`, `d`, `rslt d`, `a rslt d`...

an expression is being evaluated until either:
- it's a singular value like 1 or [block]
- it's end is hit and there are no matches

in the latter case if expr consists of more than 1 token, it is enclosed into parens
- as in the example above with (1 +): there's no pattern that can match `1 +` so it's passed as a value

then `map` function uses `~` to glue the two paren-expressions `1 +` and `2` into `1 + 2` that triggers a summing pattern












