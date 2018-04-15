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

eval-in-subscope: func [scope [map!] subscope [map!] expr [block!] /local backup] [
	backup: pattern/scope-merge scope subscope
	also
		pure/eval/with expr scope
		(pattern/scope-swap scope backup
		dispel backup)
]



arith: [
	x: + y: => [ :mathop/3 '+ x y ]
	x: - y: => [ :mathop/3 '- x y ]
	x: * y: => [ :mathop/3 '* x y ]
	x: / y: => [ :mathop/3 '/ x y ]
	x: ** y: => [ :mathop/3 '** x y ]
	x: or y: => [ :mathop/3 'or x y ]
	x: and y: => [ :mathop/3 'and x y ]
	x: xor y: => [ :mathop/3 'xor x y ]
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
	head b: => [ :first/1 b ]
	rest b: => [ :next/1 b ]
	x: ~ y: => [ :paren-join/2 x y ]			;-- (thing ~ thing) concatenates 2 paren expressions into one
	join x: y: => [:impure-join/2 x y]
	impure-join b: x: => [:append/only/2 b x]

	replicate-tco c: [] => [c]
	replicate-tco c: b: => [
		replicate-tco (impure-join c (head b)) (rest b)
	]

	map' _ [] => [[]]
	map' f: b: => [map-tco (:block-magic/conjure/0) f b]
	map-tco c: _ [] => [c]
	map-tco c: f: b: => [ map-tco (impure-join c (f ~ head b)) f (rest b) ]

	map f: b: => [:impure-map/3 _scope_ f b]

	foldl' _  c: [] => [c]
	foldl' f: c: b: => [
		foldl' f (f ~ (c head b)) (rest b)
	]

	foldl f: c: b: => [ :impure-foldl/4 _scope_ f c b ]
	foldr f: c: b: => [ :impure-foldr/4 _scope_ f c b ]

	; wow, a fork!
	if false then _ else y: => [y]
	if 0 then _  else y: => [y]
	if _ then x: else _  => [x]

	; or like this
	either false _ y: => [y]
	either true x: _ => [x]
	either 0 _ y: => [y]
	either _ x: _ => [x]

	x: = x: => [true]
	x: = _ => [false]

	true? 0 => [false]
	true? false => [false]
	true? true => [true]
	true? _ => [true]

	odd? x: => [0 = (x and 1)]
	even? x: => [1 = (x and 1)]

	; takes a block, evaluates as an expr
	eval x: => [:to-paren/1 x]

	split even: odd: [] => [ even odd ]
	split even: odd: xs: => [
		eval either (1 and (head xs))
			[ split even (join odd head xs) (rest xs) ]
			[ split (join even head xs) odd (rest xs) ]
	]

	split' even: odd: [] => [ even odd ]
	split' even: odd: xs: => [
		eval either (even? (head xs))
			[ split' even (join odd head xs) (rest xs) ]
			[ split' (join even head xs) odd (rest xs) ]
	]

	split'' even: odd: xs: => [	[	sp even odd xs ] 
		using [
			sp even: odd: [] => [even odd]
			sp even: odd: xs: => [sp even2 odd2 r]
			even2 => [eval either even? h [even][join even h]]
			odd2  => [eval either even? h [join odd h][odd]]
			h => [head xs]
			r => [rest xs]
		]
	]

	; it's faster to precompile a set of patterns once than upon every call
	rules def: => [:pattern/compile/1 def]

	expr: using def: => [
		:eval-in-subscope/3 _scope_ (rules def) expr
	]

	; short-circuits: expr1 | [expr2 | [expr3 ...]]
	true | _ => [true]
	false | b: => [eval b]

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
test serial [join 1 (2 3)] [1 2 3]

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

subst: does [[
	x: + y: => [:mathop/3 '* x y]
	sum 0 1 => [1]
	sum 1 0 => [10]
	sum _ _ => [100]
]]

test hybrid [ either true 1 2 ] 1
test hybrid [ either false 1 2 ] 2
test hybrid [ eval either true [1][2] ] 1
test hybrid [ eval either false [1][2] ] 2
test hybrid [ either (1 = 1) 1 2 ] 1
test hybrid [ either (1 = 2) 1 2 ] 2
test hybrid [eval [1 + 2]] 3
test hybrid [1 and (head [1 2 3])] 1
test hybrid [split  [] [] [1 2 3 4 5 6 7 8 9]] to-paren [[2 4 6 8] [1 3 5 7 9]]
test hybrid [split' [] [] [1 2 3 4 5 6 7 8 9]] to-paren [[2 4 6 8] [1 3 5 7 9]]
test hybrid [split'' [] [] [1 2 3 4 5 6 7 8 9]] to-paren [[2 4 6 8] [1 3 5 7 9]]
test hybrid [3 + 4] 7
test hybrid [ [3 + 4] using (:subst/0) ] 12
test hybrid [ [sum 1 0] using (:subst/0) ] 10
test hybrid [ [map [sum 1] [0 1 2]] using (:subst/0) ] [10 100 100]

big-block-1: does [append/dup conjure -1 500]
big-block1: does [append/dup conjure 1 500]
big-block-n: has [r i] [also  r: conjure  repeat i 100 [append r i]]
;test hybrid [loop 100] 0
;test hybrid [replicate-tco (:copy []) :big-block1] big-block1
test hybrid [map [negate] :big-block1] big-block-1
test hybrid [map (2 +) :big-block-1] big-block1
test hybrid [foldl [sum] 0 :big-block1] length? big-block1

even-the-odds: as paren! [
[2 4 6 8 10 12 14 16 18 20 22 24 26 28 30 32 34 36 38 40 42 44 46 48 50 52 54 56 58 60 62 64 66 68 70 72 74 76 78 80 82 84 86 88 90 92 94 96 98 100]
[1 3 5 7 9 11 13 15 17 19 21 23 25 27 29 31 33 35 37 39 41 43 45 47 49 51 53 55 57 59 61 63 65 67 69 71 73 75 77 79 81 83 85 87 89 91 93 95 97 99]
]

clock [test hybrid [split [][] :big-block-n] even-the-odds]
clock [test hybrid [split' [][] :big-block-n] even-the-odds]
clock [test hybrid [split'' [][] :big-block-n] even-the-odds]


profiler/show


