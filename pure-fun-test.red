Red [
	title: "Tests for pure-fun.red"
	file: %pure-fun-test.red
	author: hiiamboris@gmail.com
	tabs: 2
	license: 'MIT
	purpose: {To kill the idea with the results}
]


#include %pure-fun.red

;-- HERE BE TESTS

test: func [tree expr rslt /local got] [
	log-test ["testing" mold/flat expr "vs" mold/flat rslt]
	unless rslt = got: pure/eval/using expr tree [
		print ["FAILED: test" mold/flat expr "resulted in" mold/flat got "instead of" mold/flat rslt]
	]
]


;-- primitive the arithmetic is based upon
mathop: func [op [word!] x [number! pair! date! time!] y [number! pair! date! time!] /local buf] [
	buf: [x op y]
	buf/2: op
	do buf
]

join: func [a [block!] b [block!]] [append copy a b]
paren-join: func [x y] [ as paren! append (forge to-block x) y ]		; COPY HERE (to-block)
;append-into: func [a [block!] x] [append/only a x]
;fold: func [c ]


arith: [
	x: + y: => [ :mathop/3 '+ x y ]
	x: - y: => [ :mathop/3 '- x y ]
	x: * y: => [ :mathop/3 '* x y ]
	x: / y: => [ :mathop/3 '/ x y ]
	x: ** y: => [ :power/2 x y ]
	negate x: => [ :negate/1 x ]
]

test arith [0] 0
test arith [1] 1
test arith [1 + 1] 2
test arith [1 + 2 * 3] 9
test arith [1 + (2 * 3)] 7
test arith [2 ** 10] 1024
test arith [1.0 / 2 ** 2.0] 0.25
test arith [50% / 2] 25%
test arith [3x3 * 3] 9x9
test arith [3x2 * 2x4] 6x8
test arith [3x2 * 2x4] 6x8
test arith [10:00 * 2] 20:00
test arith [16 ** (3.0 / (2 * (1 + (1) + (1)) + 6))] 2.0
test arith [:add :max 1 2 3] 5
test arith [negate 10] -10


matching: [
	f 1 => [1]
	f _ => [0]
	g x: => [x]
]

test matching [f 1] 1
test matching [f 2] 0
test matching [g 3] 3

serial: [
	head b: => [ :first b ]
	rest b: => [ :next b ]
	x: ~ y: => [ :paren-join x y ]			;-- (thing ~ thing) concatenates 2 paren expressions into one
	impure-join b: x: => [:append/only b x]

	replicate-tco c: [] => [c]
	replicate-tco c: b: => [
		replicate-tco (impure-join c (head b)) (rest b)
	]

	map _ [] => [[]]
	map f: b: => [map-tco (:block-magic/conjure/0) f b]
	map-tco c: _ [] => [c]
	map-tco c: f: b: => [
		;map-tco impure-join c (f ~ head b)  f rest b 		;-- this works too, just looks creepy ;)
		map-tco (impure-join c (f ~ head b)) f (rest b)
	]
	loop 0 => [0]
	loop n: => [loop (n - 1)]
]

test serial [[]] []
test serial [head [1]] 1
test serial [head [1 2 3]] 1
test serial [head [[1] [2] [3]]] [1]
test serial [head head [[1] [2] [3]]] 1
test serial [z x c] to-paren [z x c]
test serial [(1 2) ~ (3)] to-paren [1 2 3]
test serial [(1 2) ~ 3] to-paren [1 2 3]
test serial [(1 2) ~ (3 4)] to-paren [1 2 3 4]
test serial [1 ~ 2] to-paren [1 2]
test serial [(1 (2)) ~ ((3))] to-paren [1 2 3]
test serial [(1 (2 3)) ~ ((4 5) 6)] to-paren [1 (2 3) (4 5) 6]

hybrid: append copy arith serial
;log-eval: :print
test hybrid [map-tco (:copy []) [negate] [1 2 3]] [-1 -2 -3]
test hybrid [map-tco (:copy []) (1 +) [1 2 3]] [2 3 4]
test hybrid [map-tco (:copy []) [1 +] [1 2 3]] [2 3 4]
test hybrid [map [negate] [1 2 3]] [-1 -2 -3]
test hybrid [map (1 +) [1 2 3]] [2 3 4]
test hybrid [map [1 +] [1 2 3]] [2 3 4]

big-block-1: does [append/dup conjure -1 100]
big-block1: does [append/dup conjure 1 100]
big-block2: does [append/dup conjure 2 100]
;test hybrid [loop 100] 0
;test hybrid [replicate-tco (:copy []) :big-block1] big-block1
test hybrid [map [negate] :big-block1] big-block-1


profiler/show

