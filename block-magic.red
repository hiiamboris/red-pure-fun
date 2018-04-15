Red [
	title: "Free list of blocks"
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


if unset? :block-magic [

;-- this here magic is to avoid allocations in absence of the GC --
; I intentionally avoid make/free/reduce names,
; otherwise it's so easy to run into weirdest bugs possible
; plus compiler complains, and does so rightfully
block-magic: context [
	mana: []		; free to use blocks

	conjure: does [ any [ take/last mana  copy [] ] ]									;-- allocate
	dispel: func [blk [block!]] [ append/only mana clear head blk ]		;-- free
	transmute: func [blk [block!]] [ head reduce/into blk conjure ]		;-- reduce
	forge: func [blk [block!] /part size [integer!]] [								;-- copy
		append/part conjure blk any [size -1]
	]

	import: does bind [foreach w [conjure dispel transmute forge] [ set :w get in block-magic :w ] ] 'system
]


]
