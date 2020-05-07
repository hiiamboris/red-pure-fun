Red [
	title: "Free list of blocks/strings + simplest GC"
	file: %block-magic.red
	author: hiiamboris@gmail.com
	tabs: 2
	license: 'MIT
	purpose: "Avoid allocations when necessary"
	usage: {
		`conjure` instead of `copy []`
		`dispel` frees the block and inserts into a free list
		`transmute` instead of `reduce`
		`forge` instead of `copy` (supports /part refinement)
	}
]


unless value? 'block-magic [

;-- this here magic is to avoid allocations in absence of the GC --
; I intentionally avoid make/free/reduce names,
; otherwise it's so easy to run into weirdest bugs possible
; plus compiler complains, and does so rightfully

do reduce [has [type type! title] [
	foreach type [block string] [
		type!: to-word append form type "!"
		title: to-word append form type "-magic"
		do compose/deep [
			(to-set-word title) context [
				mana: []				; free to use blocks/strings
				garbage: []			; blocks/strings that should not live long
				prototype: (either type = 'block [[[]]][[""]])		; for cloning

				conjure: does [ any [ take/last mana  copy prototype ] ]									;-- allocate
				dispel: func [srs [(type!)]] [ append/only mana clear head srs ]					;-- free
				(either type = 'block [compose/deep [																			;-- reduce, for block only
					transmute: func [srs [(type!)]] [ head reduce/into srs conjure ] 
				]] [])
				forge: func [srs [(type!)] /part size [integer! (type!)]] [								;-- copy
					append/part conjure srs any [size -1]
				]
				
				to-garbage: func [srs [(type!)]] [
					; the cost of now/time is ~1us or 4x block picks
					append/only append garbage now/precise/time srs
					srs
				]
				sweep: function [][
					t0: now/precise/time - 0:0:10		; allow 10 secs of roam around
					gr: garbage
					while [all [gr/1  gr/1 < t0]] [dispel gr/2  gr: skip gr 2]
					remove/part garbage gr
				]

				methods: collect [foreach w keys-of self [if function? get/any :w [keep :w]]]

				; only works for 'system or when set-words are already defined
				import: func [/into c /local w] [
					c: any [c system/words]
					foreach w get bind 'methods (title) [ set bind :w :c get bind :w (title) ]
				]

				; for: make object! append list-imports [ .. ]
				list-imports: has [w] [
					collect [ foreach w methods [keep to-set-word :w  keep compose [get in (title) ([(to-lit-word :w)])]] ]
				]
			]
		]
	]
]]

]
