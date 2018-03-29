Red [
	title: "General purpose forward iterator"
	file: %iterator.red
	author: hiiamboris@gmail.com
	tabs: 2
	license: 'MIT
	purpose: "Iterate over arbitrary data, hide the format of that data and the iterator implementation details from the code using it"
	usage: {
		rollin' [x y z] over-stuff [... your code here ...]
			or, when decoupling is undesirable
		rollin' 'word over-stuff [
			set [x y z] word
			... your code here ...
		]
		The contents of 'word or [x y z] is up to the iterator.
		To prepare it, make a generator that builds over `iterator/forward`.

		Example:

			over-even-items: func [b [series!]] [
				make (iterator/forward) [
					;-- subject field will be set by 
					subject: b
		
					;-- should return true if `advance` is needed upon the first entry to `rollin'`
					needs-a-kick?: does [false]
		
					;-- reads & returns the data to the user
					data: does [subject/2]

					;-- moves the iterator on, returns false when out of items
					advance: does [
						if 3 >= length? subject [return false]
						subject: skip subject 2
						true
					]
				]
			]
			
			>> rollin' 'x over-even-items [1 2 3 4 5] [print [x "HERE!"]]
			2 HERE!
			4 HERE!		
	}
]


#include %assert.red
#include %profiler.red

if unset? :iterator [

; general forward iterator format:
iterator: context [

	free-list: []
	release: func [it [object!]] [append free-list it]

	; TODO: a free list of iterators, until GC is there
	forward: func ["Constructs a new iterator"] [
		any [
			take/last free-list
			context [
				advance: does [false]				; advances the iterator to the next position, in place, returns true on success, false if empty
				data: does []								; reads the current item and returns, doesn't advance
				needs-a-kick?: does [true]	; checks if there's no more items to return - for the initial advance() call
				subject: none								; the stuff that's being iterated over, any format
			]
		]
	]

	iterator!: :object!		; just a type, can't do a better check in func specs

	;-- better check
	iterator?: func [x][
		all [
			object? x
			in x 'advance
			in x 'data
			in x 'needs-a-kick?
		]
	]

	; rollin' 'x over stuff [...]
	; rollin' [x y z] over stuff [...]
	; BUG: 'return' from inside the body will only terminate the loop, but the workaround is slower
	profiler/count/*
;	rollin': func [parts [block! word!] it [iterator!] code [block!] /local r] [
	rollin': func [
		"Iterate over arbitrary data"
		parts [block! word!] "data receiver"
		it [object!] "iterator"
		code [block!] "what to do"
		/keep "don't call release on the iterator"
		/local r C4
	] [
		C4: [unless keep [release it]]
		assert [iterator? it]
		if it/needs-a-kick? [ unless it/advance [do C4  return* none] ]		; kick-start if need be
		set/any 'r forever [
			set parts it/data
			profiler/stop rollin'
			set/any 'r do code
			profiler/start rollin'
			unless it/advance [do C4  return* :r]
		]		; in case of break/return it's value is propagated up
		do C4
		:r
	]

	assert [none = rollin' 'x forward []]
]

iterator?: :iterator/iterator?
rollin': :iterator/rollin'


]