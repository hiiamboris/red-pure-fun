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
		
					;-- reads & returns the data to the user, or unset! if no data
					;-- hint: do [] returns unset!
					;-- hint2: it is the iterator-self (to avoid rebinding the func body, which is slow)
					retrieve: func [it] [
						also
							either 2 <= length? it/subject [it/subject/2][do []]
							it/subject: skip it/subject 2
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

	; since bind is super slow, I decided to pass the iterator as a parameter to retrieve
	; this way any new iterator can be created without a 'bind' invocation
	forward: func ["Constructs a new iterator"] [
		any [
			take/last free-list
			context [
				retrieve: func [it][]		; reads the current item and advances the iterator, returns unset! when no data
				subject: none						; the stuff that's being iterated over, any format
			]
		]
	]

	iterator!: :object!		; just a type, can't do a better check in func specs

	;-- better check
	iterator?: func [x][
		all [
			object? x
			in x 'retrieve
			in x 'subject
		]
	]

	; rollin' 'x over stuff [...]
	; rollin' [x y z] over stuff [...]
	; BUG: 'return' from inside the body will only terminate the loop, but the workaround is slower
	profiler/count/*
	rollin': func [
		"Iterate over arbitrary data"
		parts [block! word!] "data receiver"
		it [object!] "iterator"
		code [block!] "what to do"
		/keep "don't call release on the iterator"
		/local r
	] [
		assert [iterator? it]
		set/any 'r forever [
			if unset? set/any parts (it/retrieve it) [break/return :r]
;			profiler/stop rollin'
			set/any 'r do code
;			profiler/start rollin'
		]		; in case of break/return it's value is propagated up
		unless keep [release it]
		:r
	]

	assert [none? rollin' 'x forward []]
]

iterator?: :iterator/iterator?
rollin': :iterator/rollin'


]