Red [
	title: "Assert function for contract programming"
	file: %assert.red
	author: hiiamboris@gmail.com
	tabs: 2
	license: 'MIT
	usage: {
		`? assert` should help
		uncomment the line at the end to disable assertions
	}
]



#include %block-magic.red

unless attempt [get in system/words 'assert] [

assert: function [
	"Yer typical assertion"
	contract [block!]	"contract"
	/comment	{
	contract can have one the of 3 formats:
		[condition  "error message"]
		[condition  'word-to-blame]
		[condition]		<- in this case last word of condition is blamed}
  /local tmp
][
	set [cond msg] tmp: block-magic/transmute contract			;-- TODO: replace this with `reduce contract` when GC is available
	unless cond [
		print ["ASSERTION FAILURE:" mold contract]
		either string? msg [
			cause-error 'script 'invalid-arg [msg]
		][
			if none? msg [msg: last contract]
			cause-error 'script 'invalid-refine-arg [msg  mold/part/flat get msg 1024]
		]
	]
	block-magic/dispel tmp
]

assert: :comment		;-- uncomment to disable assertions


]