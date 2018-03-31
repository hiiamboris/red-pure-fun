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
	log-test ["testing" mold/flat expr "vs" mold/flat/part rslt 128]
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

;join: func [a [block!] b [block!]] [append copy a b]
impure-join: func [a b] [append forge to-block a to-block b]
paren-join: func [x y] [ as paren! append (forge to-block x) y ]		; COPY HERE (to-block)
;append-into: func [a [block!] x] [append/only a x]
;fold: func [c ]


impure-map: function [scope [map!] f [block! paren!] b [block!]] [
	r: forge b
	expr: conjure
	forall r [
		expr: head change/only change expr :f :r/1
		change r pure/eval-full expr with scope
	]
	dispel expr
	head r
]

;-- like this: f (f (f c b/1) b/2) b/3
impure-foldl: function [scope [map!] f [block! paren!] c b [block!]] [
	expr: conjure
	forall b [
		expr: head change/only change/only change expr :f :c :b/1
		c: pure/eval-full expr with scope
	]
	dispel expr
	c
]

;-- like this: f b/1 (f b/2 (f b/3 c))
impure-foldr: function [scope [map!] f [block! paren!] c b [block!]] [
	expr: conjure
	limit: index? b
	b: tail b
	while [limit < index? b] [
		b: back b
		expr: head change/only change/only change expr :f :b/1 :c
		c: pure/eval-full expr with scope
	]
	dispel expr
	c
]


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
	s => [[1 2 3]]
	head b: => [ :first b ]
	rest b: => [ :next b ]
	x: ~ y: => [ :paren-join x y ]			;-- (thing ~ thing) concatenates 2 paren expressions into one
	join x: y: => [:impure-join x y]
	impure-join b: x: => [:append/only b x]

	replicate-tco c: [] => [c]
	replicate-tco c: b: => [
		replicate-tco (impure-join c (head b)) (rest b)
	]

	map' _ [] => [[]]
	map' f: b: => [map-tco (:block-magic/conjure/0) f b]
	map-tco c: _ [] => [c]
	map-tco c: f: b: => [ map-tco (impure-join c (f ~ head b)) f (rest b) ]

	map f: b: => [:impure-map _scope_ f b]

	foldl' _  c: [] => [c]
	foldl' f: c: b: => [
		foldl' f (f ~ (c head b)) (rest b)
	]

	foldl f: c: b: => [ :impure-foldl _scope_ f c b ]
	foldr f: c: b: => [ :impure-foldr _scope_ f c b ]

	sum x: y: => [x + y]
	
	loop 0 => [0]
	loop n: => [loop (n - 1)]
	
	f => [1 +]
	dup 0 b: => [b]
	dup n: b: => [dup (head b) (rest b)]
]

test serial [[]] []
test serial [head [1]] 1
test serial [head [1 2 3]] 1
test serial [head [[1] [2] [3]]] [1]
test serial [head head [[1] [2] [3]]] 1
test serial [z x c] to-paren [z x c]
test serial [(1 2) ~ (3)] to-paren [1 2 3]
test serial [(1 2) ~ 3] to-paren [1 2 3]
test serial [(1 2) ~ 3 ~ 4] to-paren [1 2 3 4]
test serial [(1 2) ~ (3 4)] to-paren [1 2 3 4]
test serial [1 ~ 2] to-paren [1 2]
test serial [(1 (2)) ~ ((3))] to-paren [1 2 3]
test serial [(1 (2 3)) ~ ((4 5) 6)] to-paren [1 (2 3) (4 5) 6]
test serial [(head s) ~ (rest s)] to-paren [1 2 3]
test serial [join [1 2 3] 4] [1 2 3 4]

hybrid: append copy arith serial
;log-eval: :print
;test hybrid [loop 10] 0
;print "   --------- ---------------------- ------------------  "
;test hybrid [dup 2 (:copy [3 2 1 0])] []
test hybrid [map-tco (:copy []) [negate] [1 2 3]] [-1 -2 -3]
test hybrid [map-tco (:copy []) (1 +) [1 2 3]] [2 3 4]
test hybrid [map-tco (:copy []) [1 +] [1 2 3]] [2 3 4]
test hybrid [map [negate] [1 2 3]] [-1 -2 -3]
test hybrid [map (1 +) [1 2 3]] [2 3 4]
test hybrid [map [1 +] [1 2 3]] [2 3 4]
test hybrid [foldl' [sum] 0 [1 2 3]] 6
test hybrid [foldl [sum] 0 [1 2 3]] 6
test hybrid [foldr [sum] 0 [1 2 3]] 6
test hybrid [foldl [sum] 0 [1 2 3]] 6
test hybrid [foldl [join] [] [1 2 3]] [1 2 3]
test hybrid [foldr [join] [] [1 2 3]] [1 2 3]

big-block-1: does [append/dup conjure -1 500]
big-block1: does [append/dup conjure 1 500]
;test hybrid [loop 100] 0
;test hybrid [replicate-tco (:copy []) :big-block1] big-block1
test hybrid [map [negate] :big-block1] big-block-1
test hybrid [map (2 +) :big-block-1] big-block1
test hybrid [foldl [sum] 0 :big-block1] length? big-block1


profiler/show


