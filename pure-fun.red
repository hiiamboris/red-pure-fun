Red [
	title: "Purely functional dialect for Red"
	file: %pure-fun.red
	author: hiiamboris@gmail.com
	tabs: 2
	license: 'MIT
	purpose: {
		This is an experiment in building a dialect that will:
		- allow computing pure expressions in the middle of Red code
			point is: when one sees a pure invocation, one is 100% sure it didn't shoot his ducks
		- do so in a declarative, orderless manner
			point is: tell the parser how X and Y and so and so can be computed and let it decide for itself if it needs to compute them and in what order
		- allow using recursive expressions, leveraging tail-call optimization when possible
			point is: get rid of loops to achieve better conciseness and readability of the code
		- be very simple, no sophisticated type inference (as a result, no laziness), just the bare minimum
	}
	status: {
		early alpha, very very early
		proves the concept, but slow as hell: can't handle a map() over 100 items
	}
]


#include %block-magic.red
#include %assert.red
#include %profiler.red
#include %iterator.red


;------------- logging
log-test: log-eval: log-pattern: log-loop:	:print
;-- comment these to show the appropriate info:
;log-test:
log-eval:
log-pattern:
log-loop:
	func [b][]



;-- ensure the behavior of paths/words is correct
assert [get-word?     first [:x]    'get-word?]
assert [not get-word? first [:x/y]  'get-word?]
assert [not get-word? first [:x/3]  'get-word?]
assert [not get-path? first [:x]  	'get-path?]
assert [get-path?     first [:x/y]  'get-path?]
assert [get-path?     first [:x/3]  'get-path?]

;-- typeset for path+word, doesn't work with the compiler :D
impure-path!: make typeset! [get-word! get-path!]
impure-path?: func [v][find impure-path! type? :v]

;-- gets the arity for a given impure-path! call
;impure-arity?: func [p [impure-path!]] [
impure-arity?: func [p [get-word! get-path!]] [
	assert [any [get-word? p  not empty? p]	'p]
	either get-word? p [
		preprocessor/func-arity? spec-of get (bind  to-word p  'system)
	][
		assert [get-path? p]
		either integer? last p [last p][
			;-- func-arity? doesn't handle objects well...
			;-- simplest workaround is to append arity manually as /0 /1 etc
			assert [not object? get/any p/1]
			preprocessor/func-arity?/with  (spec-of get (bind  first p  'system))  to-path p
		]
	]
]

;-- prepares impure-path for a call with `reduce`
;purify-path: func [p [impure-path!] /local r][
purify-path: func [p [get-word! get-path!] /local r][
	r: as path! block-magic/conjure
	either get-word? p [append r to-word p][
		assert [get-path? p]
		append r as path! p
		if integer? last r [take/last r]
	]
	r
]

assert [impure-path?	first [:x]  	'impure-path?]
assert [impure-path?	first [:x/3]  'impure-path?]
assert [impure-path?	first [:x/y]  'impure-path?]
assert [to-path 'x = purify-path	first [:x]  	'purify-path]
assert [to-path 'x = purify-path	first [:x/3]  'purify-path]
assert ['x/y       = purify-path	first [:x/y]  'purify-path]
assert [3         = impure-arity?	first [:x/3]  'impure-arity?]
;assert ['block-magic/conjure	= purify-path	first [:block-magic/conjure]  'purify-path]
;assert [0 = impure-arity? first [:block-magic/conjure]  'impure-arity?]



; TODO: special handling of true, false, none words -> into values?
; primitives (unevaluated) that are permitted in patterns declaration
pattern-symbol!: make typeset! [word! set-word! number! any-string! any-list! char! pair! binary! date! time!]
pattern-symbol?: func [v][find pattern-symbol! type? :v]



pattern: context [
	; import symbols from block magic
	foreach w [conjure dispel transmute forge] [set w get in block-magic w]

	; naming convention:
	; pl is for pattern list
	; pt is for pattern tree

	valid-list?: func [pl [block!]] [ even? length? pl ]
	valid-tree?: func [pt [block!]] [ true ]		; no way to check currently: [] and [[]] and [[] [[patt exp]]] are all valid

	empty-list: does [ conjure ]
	empty-tree: does [ conjure ]

	uplift-tree: func [pt [block!]] [
		assert [valid-tree? pt]
		assert [not empty? pt   "cannot uplift from an empty tree"]
		pt/1
	]
	nest-tree: func [pt [block!]] [
		assert [valid-tree? pt]
		transmute [pt]
	]

	; append a pair of [pat exp] into a pattern-list or a pattern-tree (at it's current (inner) level)
	list-attach: func [pl [block!] pat [block!] exp [block!]] [
		list-attach-pair pl transmute [pat exp]
	]
	tree-attach: func [pt [block!] pat [block!] exp [block!]] [
		tree-attach-pair pt transmute [pat exp]
	]
	list-attach-pair: func [pl [block!] pair [block!] /local i len] [
		assert [all [block? pair/1  block? pair/2]		'pair]
		assert [2 <= length? pair]
		assert [valid-list? pl]
		append/part pl pair 2
		pl
	]
	tree-attach-pair: func [pt [block!] pair [block!] /local i len tgt] [
		assert [all [block? pair/1  block? pair/2]		'pair]
		assert [all [2 <= length? pair  1 <= min (length? pair/1) (length? pair/2)] 	'pair]
		assert [valid-tree? pt]
		; in a tree the insert goes into a specific index
		i: 1 + (length? pair/1)
		if i > len: length? pt [loop (i - len) [append/only pt empty-list]]
		tgt: pt/:i
		assert [block? tgt]			; can't attach to a context, or will have to copy it
		append/part tgt pair 2
		pt
	]
	; pt2 to pt1, pt1 is modified in place (nest if needed)
	; pt2 should be unparented
	tree-attach-tree: function [pt1 [block!] pt2 [block!]] [
		assert [empty? uplift-tree pt2]
		pt2: next pt2
		forall pt2 [
			pl: pt2/1
			either object? pl [
				foreach [name list] body-of pl [
					assert [set-word? name]
					assert [valid-list? list]
					unless tail? list [
						rollin' 'pair over-list list [tree-attach-pair pt1 pair]
					]
				]
			][
				assert [valid-list? pl]
				unless tail? pl [
					rollin' 'pair over-list pl [tree-attach-pair pt1 pair]
				]
			]
		]
		pt1
	]


	;free-list: stacks...

	; simple & fast iterator version
	list-iterator: has [it] [
		it: iterator/forward
		it/needs-a-kick?: does bind [empty? subject/1] it
		it/data: does bind [
			assert [not empty? subject/1]
			subject/1
		] it
		it/advance: does bind [
			assert [none? subject/3]
			assert [none? subject/4]
			if not tail? subject/1 [
				subject/1: skip subject/1 2
				return not tail? subject/1
			]
			false
		] it
		it
	]

	; check if value matches the token
	; set-word (value) and get-word (token) is prohibited
	; word (value) matches only same word (token)
	; not-word (value) matches: same not-word, set-word, '_' (token)
	token-match?: func [token value] [
		assert [not set-word? value]
		assert [not get-word? token]
		any [
			value = token
			all [
				not word? value
				any [set-word? token  token = '_]
			]
		]
	]

	assert [token-match? 1 1]
	assert [token-match? [] []]
	assert [token-match? '_ 1]
	assert [token-match? '_ []]
	assert [token-match? to-set-word 'x 1]
	assert [token-match? to-set-word 'x []]
	assert [not token-match? 1 2]
	assert [not token-match? 1 []]
	assert [not token-match? 'x 'y]
	assert [not token-match? '_ 'y]
	assert [not token-match? to-set-word 'x 'y]

	; returns a symbol suitable for context lookup
	; word -> word
	; anything else (values, set-words) -> _  (further selection is done incrementally by token-match?)
	symbol-for-value: func [value] [
		either word? value [value]['_]
	]

	list-in-context: func [ct [object!] cue [word!] /local pos] [
		pos: in ct symbol-for-value cue
		either pos [get pos][[]]
	]

	; full-featured tree iterator
	; requires all the fields set - tree, size, token (otherwise how to kickstart it and how to navigate in subcontexts?)
	; since cue is matched against each pattern, it should a value occurred in expr (as is, even none!)
	tree-iterator: has [it] [
		it: iterator/forward
		; subject is: [pos-in-plist size outer-tree|none 1st-token|none]
		; initially not on the data, but will go with a kick
		; have to recreate all the funcs because each iterator is bound to it's own context
		it/needs-a-kick?: does bind [empty? subject/1] it
		it/data: does bind [
			assert [not empty? subject/1]
			assert [not empty? subject/1/1		"pattern can't be empty"]
			assert [token-match? subject/1/1/1 cue		"cue/pattern mismatch detected, oops"]
			subject/1
		] it
		profiler/count
		advance: function [] bind [
			set [pos size tree cue] subject
			assert [valid-tree? tree	'subject]
			assert [integer? size		'subject]

			log-loop ["^/advancing in a tree" mold/flat subject]

			; linear advancement until cue is met (or the end)
			while [not all [tail? pos  empty? tree]] [
				pos: skip pos 2
				log-loop ["+2 to pos -- now at" mold/flat pos]

				; when empty, try going upwards
				while [all [
					tail? pos 					; no need to ascend unless pos is empty
					not empty? tree			; important to skip none! too
				]] [
					log-loop ["list is empty, going up..."]
					; try to find a pattern list in the uptree
					if size < length? tree [			; tree has patterns of this size?
						log-loop ["upper tree has got the patterns of required size" size]
						pos: pick tree (size + 1)
						if object? pos [		; get a block if it's a context
							log-loop ["got a context, converting..."]
							pos: list-in-context pos symbol-for-value cue
						]
						log-loop ["now working in the list:" mold/flat pos]
					]
					subject/3: tree: uplift-tree tree		; upwards...
				]
				; upon exit, either pos is unempty, or it is and there's nowhere more to go up
				log-loop ["finished ascension"]

				; check the cue, esp. if symbol is _ or there's no context - will have to match patterns one by one
				unless tail? pos [
					log-loop ["there's a pattern to check, at" mold/flat pos]
					log-loop ["matching" mold/flat cue "against" mold/flat pos/1/1 "..."]
					assert [not empty? pos/1		"pattern can't be empty"]
					if token-match? pos/1/1 cue [		; finally found our new position
						log-loop ["got a match! setting list to" mold/flat pos]
						subject/1: pos
						return true
					]
				]
			]

			log-loop ["finished.. at" mold/flat pos "^/"]

			subject/1: pos
			false
		] it
		it/advance: :advance
		it
	]

	; simplistic iterator over a flat pattern list
	over-list: func [pl [block!] /skip n [integer!] /local it] [
		assert [valid-list? pl]
		it: list-iterator
		it/subject: transmute [either n [skip pl n * 2][pl]  none none none]
		it
	]

	assert [123  = rollin' 'x over-list [[p][x]] [0 break/return 123]		"rollin's broken"]
	assert [123  = rollin' 'x over-list [[p][x]] [123]	"rollin's broken"]
	assert [none = rollin' 'x over-list [] [123]	"rollin's broken"]

	; takes a tree and pattern size, and a cue
	over-tree: func [pt [block!] size [integer!] cue /local it] [
		assert [valid-tree? pt]
		it: tree-iterator
		it/subject: transmute [[] size pt cue]
		it
	]

	; takes a pattern-list and makes a context out of it
	; (context is only meaningful for a specific pattern size and cue)
	promote-to-context: function [pl [block!]] [
		assert [valid-list? pl]
		def: empty-list
		rollin' 'pair over-list pl [
			set [pat exp] pair
			w: either word? pat/1 [pat/1]['_]
			unless sel: select def symbol-for-value pat/1 [
				append def transmute [to-set-word w  sel: empty-list]
			]
			list-attach-pair sel pair
		]
		context def
	]

	assert [
		(promote-to-context [
			[a b c] [1]
			[a c c] [2]
			[b c d] [3]
			[c] [4]
			[d] [5]
			[1] [6]
		]) = context [
			a: [ [a b c] [1] [a c c] [2] ]
			b: [ [b c d] [3] ]
			c: [ [c] [4] ]
			d: [ [d] [5] ]
			_: [ [1] [6] ]
		]
		'promote-to-context
	]

	count?: func [pl [block!]] [
		assert [valid-list? pl]
		(length? pl) / 2
	]



	; compiled pattern format (outer [] can be empty):
	[ [outer patterns] pattern expr pattern expr ...]
	; TODO: make contexts
	compile: function [spec [block!] /into outer [block!]] [
		cpat: nest-tree any [outer empty-tree]
		assert [valid-tree? cpat]
		unless parse spec [
			any [
				end:
				collect set pat any [
					not '=> keep set w skip
					if (pattern-symbol? :w)
				]
				ahead '=> skip		;-- "=>"
				set exp skip
				if (block? :exp)
				(tree-attach cpat :pat :exp)
			]
		] [print ["can't parse" mold spec "at" mold end]  throw "pattern error"]
		assert [valid-tree? cpat]
		pl: next cpat
		forall pl [ change pl promote-to-context pl/1 ]
		cpat
	]

	;catchall?: func [item] [any [item = '_  set-word? item]]

	; detects similar patterns, but not enough to clash them
	profiler/count
	similar?: function [pat1 [block!] pat2 [block!]] [
		assert [(length? pat1) = length? pat2]
		
		setwords: empty-list
		forall pat1 [
			a: pat1/1  b: pat2/1	pat2: next pat2

			; determine which word is new and check that they are either equal or one is known already
			new-word: none
			switch (either set-word? a [1][0]) + (either set-word? b [2][0]) [
				3 [		; both are set-words
					unless find setwords a [new-word: a]
					if a <> b [
						unless find setwords b [		; b is unknown and different
							; then a should not be unknown
							if new-word [return false]
							new-word: b
						]
					]
				]
				2 [unless find setwords b [new-word: b]]
				1 [unless find setwords a [new-word: a]]
			]

			if new-word [append setwords a]

			; set-words were accounted for, now should only consider that
			; if one of items is a word, another pattern should also have (the same) word there
			; except if any word is _ - it is similar to anything
			if all [ a <> b   a <> '_   b <> '_   any [word? a  word? b] ][ return false ]
		]
		true
	]

	assert [similar? [f x:] [f 1]]
	assert [similar? [f _] [f 1]]
	assert [similar? [f 1] [f 2]]
	assert [not similar? [f 1] [g 1]]

	all-similar?: function [pl [block!]] [
		assert [valid-list? pl]
		assert [1 <= count? pl]
		either 1 = count? pl [true][
			; there's another way: go item by item, but that's probably slower
			it: over-list pl
			; extract 1st pair
			rollin' [refpat refexp] it [break]
			; compare to all others
			rollin' [pat exp] it [
				unless similar? refpat pat [break/return false]
				true
			]
		]
	]

	; calc's pattern's score based on given values list
	; => none if no match, >= 0 if a match
	profiler/count
	score?: function [pat [block!] values [block!]] [
		assert [1 < length? pat]		; pointless for singular patterns
		assert [(length? pat) <= length? values]

		r: 0	v: values
		log-pattern ["score: trying" mold/flat pat "with" mold/flat values]
		forall pat [
			w: pat/1
			unless token-match? w v/1 [ return none ]
			; only increase score if w is a value or repeated set-words
			case [
				set-word? w [
					if prev-idx: find/reverse pat w [		; none or pat at the previous occurrence of w
						prev-v: pick values index? prev-idx
						if v/1 <> prev-v [return none]		; drop the pattern - previous occurrence doesn't match
						r: r + 1			; incr score for the value matched that of a repeated set-word
					]
				]
				not word? w [		; w is a value matched exactly
					r: r + 1				; incr score for the value matched one directly specified in the pattern
				]
			]
			v: next v
		]
		log-pattern ["score of" pat "=" r]
		r
	]
		
	; clashes similar patterns using a list of scores
	; => selected [pattern expr]
	clash: function [pl [block!] scores [block!]] [
		assert [valid-list? pl]
		assert [2 <= count? pl]
		assert [all-similar? pl]
		assert [(count? pl) = length? scores]
		
		winner: none
		best-score: -1
		rollin' 'pair over-list pl [
			set [pat exp] pair
			if best-score <= scores/1 [
				;assert [sc <> best-score		"ambiguous pattern match in clash"]
				best-score: scores/1
				winner: pair
			]
			scores: next scores
		]
		assert [winner]
		winner: forge/part winner 2	; pair didn't have to copy
		winner
	]

	; transform a list of values (of pattern's length) into a list of pairs for set-words
	; => a list of pairs of `name value` form, composed only from named set-words
	; i.e. assign [f x: y: x: _ 5] [f 1 2 1 4 5] => [[x] [1] [y] [2]]
	assign: function [pat [block!] values [block!]] [
		assert [not empty? pat]
		assert [(length? pat) <= length? values]

		paired: empty-list
		forall pat [
			if set-word? w: pat/1 [
				unless old?: find/reverse pat w [
					append paired transmute [
						transmute [to-word w]
						transmute [values/1]
					]
				]
			]
			values: next values
		]
		paired
	]

	
]



pure: context [
	; import symbols from block magic
	foreach w [conjure dispel transmute forge] [set w get in block-magic w]

	; evaluation of a single-token pattern
	; if token is a parens, forks with eval-full
	; => none if no match (and expr is unchanged), otherwise:
	;   if /deferred then
	;     may return => [same-tree [subexpr]], expr is unchanged yet
	;     but if value is immediately available w/o any changes, => 1
	;   if not then => 1 and expr is changed in place with the result of eval-full
	profiler/count
	eval-single: function [expr [block!] 'with [word!] pt [block! none!] /deferred] [
		log-eval ["eval-single" mold/flat expr "with" mold/flat pt "/" deferred]

		assert ['with = with	"syntax of eval-single is wrong"]
		assert [1 <= length? expr]

		; variants:
		;  word => should match exactly
		;  set-word or _ => forbidden
		;  any other value => returned as is (no matching, as single-token catchalls are forbidden)

		; return values as is, and words too if tree is unspecified
		r: 1
		value: expr/1
		if pt [
			found?: false
			case [
				paren? value [subex: as block! value  found?: true]	
				word? value [
					rollin' [pat subex] (pattern/over-tree pt 1 value) [
						assert [1 = length? pat]
						if value = pat/1 [ found?: true  break ]		; found a match
					]
				]
			]
			if found? [		; unless it's a word that never matched or a normal (not parens value)
				assert [block? subex]
				r: either deferred [
					transmute [pt subex]
				][
					subex: forge subex 	; for eval-full to change it in place
					; eval-full always returns a singular value, parens if needed
					subresult: eval-full subex with pt
					change/only expr subresult
					;dispel subex
					1
				]
			]
		]
		log-eval ["eval-single =>" mold/flat expr/1]
		r
	]

	; eval an expr of fixed size (expr block itself can be longer)
	; => none if no match (and expr is unchanged), otherwise:
	;   if /deferred then => [new-tree [subexpr]], expr is unchanged yet
	;   if not then => the new size (which is 1 ofc) and then the expr is changed in place with eval-full
	profiler/count
	eval-fixed: function [expr [block!] 'of [word!] size [integer!] 'with [word!] pt [block! none!] /deferred] [
		log-eval ["eval-fixed" mold/flat expr "of" size "with" mold/flat pt "/" deferred]

		assert [[of with] = transmute [of with]	"syntax of eval-fixed is wrong"]
		assert [size <= length? expr]
		assert [1 < size]		; otherwise should use eval-single
		assert [not impure-path? expr/1]

		matches: pattern/empty-list
		scores: pattern/empty-list

		rollin' 'pair (pattern/over-tree pt size expr/1) [
			set [pat subex] pair
			log-eval ["expr is" mold/flat expr]
			log-eval ["-- got" mold/flat pat mold/flat subex]
			if sc: pattern/score? pat expr [		; not none if a match
				pattern/list-attach-pair matches pair
				append scores sc
			]
		]
		log-eval ["matches:" mold/flat matches "scores:" mold/flat scores]
		r: none
		unless tail? matches [
			assert [(pattern/count? matches) = length? scores]
			
			; select a match
			match: none
			either 1 = pattern/count? matches [		; there's only one?
				match: matches
			][
				; got a couple of matches
				; they should be all similar to be of use
				if pattern/all-similar? matches [ match: pattern/clash matches scores ]
			]

			if match [
				set [pat subex] match

				; populate the context with arguments
				extra-args: pattern/assign pat expr
				; modify the tree pt
				unless empty? extra-args [
					pt: pattern/nest-tree pt
					rollin' 'pair pattern/over-list extra-args [
						pattern/tree-attach-pair pt pair
					]
				]

				r: either deferred [
					transmute [pt subex]
				][
					subex: forge subex 	; for eval-full to change it in place
					; eval-full always returns a singular value, parens if needed
					subresult: eval-full subex with pt
					change/part/only expr subresult size
					;dispel subex
					1
				]

			]
		]
		; if r = none then no (unambiguous) match => should return none
		log-eval ["eval-fixed =>" mold/flat r]
		r  
	]

	; eval all subpatterns of expr (starting with 2nd token), but not the whole pattern
	; all single tokens should be final
	; expr is modified in place, returns it's new size so the caller can adjust
	; => new size (= size means unmodified, since it maps multiple items into one)
	; always true: 2 <= new size <= size
	profiler/count
	eval-subpatterns: function [expr [block!] 'of [word!] size [integer!] 'with [word!] pt [block! none!]] [
		assert [[of with] = transmute [of with]	"syntax of eval-subpatterns is wrong"]
		assert [size <= length? expr]
		assert [2 < size]			; pointless with 2 tokens

		subsize: 2
		while [subsize < size] [
			subex: skip expr (size - subsize)
			if newsize: eval-fixed subex of subsize with pt [
				assert [1 = newsize]
				size: size - subsize + newsize
				subsize: newsize
			]
			subsize: subsize + 1
		]
		; might as well reduce expr to 2 tokens...
		size
	]

	; evaluates expr starting with 1 token, and continuing until either
	;   expr becomes as long as /size/ and doesn't match any patterns (doesn't extend it past the /size/)
	;     => size then
	;   tail of expr is met
	;     => length? expr then
	; expr is modified in place
	; => never none! (is there even a need?)
	; expr is expected to be totally unevaluated
	; size can be set to length? expr for unrestricted evaluation
	profiler/count
	eval-limited: function [expr [block!] 'until [word!] size [integer!] 'with [word!] pt [block! none!]] [
		assert [[until with] = transmute [until with]	"syntax of eval-limited is wrong"]
		assert [1 <= size]
		assert [size <= length? expr]

		done: 0
		while [all [done < size  done < length? expr]] [

			; eval the next token - expand the pattern
			; if it's a call to an impure func, call it
			rest: skip expr done
			either impure-path? rest/1 [
				unless eval-impure rest with pt [
					; there's an impure call that can't be done
					; so there's no more need to try to match this expr, as it won't
					break
				]
			][
				; normal token
				eval-single rest with pt
			]
			done: done + 1

			; eval any subexpressions
			if 3 <= done [ done: any [(eval-subpatterns expr of done with pt) done] ]

			; try to eval the whole piece
			if 2 <= done [ done: any [(eval-fixed expr of done with pt) done] ]
		]

		done
	]	; eval-limited

	; expr should start with an impure-path!
	; it'll discover the arity and call eval-subpatterns until the arity is fulfilled
	; then calls the impure function and modifies expr
	; => 1 on successful match (and thus call)
	; => none otherwise (expr is unmodified)
	profiler/count
	eval-impure: function [expr [block!] 'with [word!] pt [block! none!]] [
		log-eval ["^/eval-impure" mold/flat expr "with" mold/flat pt]

		assert ['with = with	"syntax of eval-impure is wrong"]
		assert [1 <= length? expr]
		assert [impure-path? expr/1]

		arity: impure-arity? expr/1
		log-eval ["arity is:" arity]

		; prepare the arguments
		if all [
			1 <= arity 							; requires arguments?
			arity < length? expr		; is there a chance we can have them?
		][ eval-limited (next expr) until arity with pt ]
		
		; invoke if there are enough args in the expr
		if arity < length? expr [
			log-eval ["ready to invoke" mold/flat expr]
			; make a valid red-expression
			subexp: forge/part expr (arity + 1)
			change/only subexp ppath: purify-path expr/1
			repeat i arity [
				; pass any paren! as a block! otherwise it'll be reduced
				; (could also pass as `first [(x)]` but that's super slow)
				pos: skip subexp i
				if paren? pos/1 [change/only pos to-block pos/1]
			]
			log-eval ["made as subexp" mold/flat subexp]
			result: do bind subexp 'system
			log-eval ["call result:" mold/flat result]
			dispel subexp
			dispel as block! ppath
			assert [not any-word? result]		; should return a value, I guess...
			change/only/part expr result (arity + 1)
			return 1
		]

		none
	]

	; => always a singular value:
	;    either normal, or
	;    a `to-paren expr` if the expr contains > 1 tokens
	; expr is modified in place before returning, or to-paren-ing
	; always works on the whole expr (no limits)
	; TCO-enabled
	profiler/count
	eval-full: function [expr [block!] 'with [word!] pt [block! none!]] [
		assert ['with = with	"syntax of eval-full is wrong"]
		assert [1 <= length? expr]

		log-eval ["^/eval-full" mold/flat expr "with" mold/flat pt]

		until [
			replaced?: false		; becomes true if TCO occurs
			log-eval ["EXPR:" mold/flat expr]
			case [

				; simplest 1-token expr
				1 = length? expr [
					; if it's a call to an impure func, call it
					either impure-path? expr/1 [
						eval-impure expr with pt
						break		; can't let impure calls to return expressions... it's too much
					][
						; normal token + TCO is possible here immediately
						if result: eval-single/deferred expr with pt [
							if block? result [		; deferred can return 1 in case result was obvious
								dispel expr
								set [pt expr] result
								expr: forge expr
								replaced?: true
							]
						]
					]
				]

				; 2+ tokens...
				true [
					size: 0
					while [size < length? expr] [

						rest: skip expr size
						log-eval ["REST:" mold/flat rest]

						; if it's a call to an impure func, call it
						either impure-path? rest/1 [
							unless (eval-impure rest with pt) [
								; there's an impure call that can't be done
								; so there's no more need to try to match this expr, as it won't
								break
							]
						][
							; otherwise eval the next token - expand the pattern
							eval-single rest with pt
						]
						size: size + 1

						; when size >= 3 eval subexpressions
						if 3 <= size [
							size: any [(eval-subpatterns expr of size with pt)  size]
						]

						; try to eval the fully-sized subexpr
						if 2 <= size [
							either size = length? expr [
								; TCO is possible when size = expr length
								if result: eval-fixed/deferred expr of size with pt [
									dispel expr
									set [pt expr] result
									expr: forge expr
									replaced?: true
									break		; start afresh from the 1st token
								]
							][
								; otherwise must fork
								size: any [(eval-fixed expr of size with pt)  size]
							]
						]

					]	; while []
				]	; 'true' case

			]	; case []

			not replaced?
		]	; until..

		; should return paren if contains >1 token
		r: either 1 < length? expr [
			;to-paren expr
			as paren! expr
		][
			expr/1
		]
		r
	]	; eval-full


	eval: function [
		"Evaluate a pure expression"
		expr [block!] "<- yep, this one"
		/using patterns [block!] "a set of patterns (rules) to match against"
	] [
		pt: either using [pattern/compile patterns][empty-tree]
		eval-full (forge expr) with pt
	]
	
]



;-- this is the whole of API ;)
eval: :pure/eval


