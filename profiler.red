Red [
	title: "Basic runtime profiler"
	file: %profiler.red
	author: hiiamboris@gmail.com
	tabs: 2
	license: 'MIT
	purpose: "Time the execution of individual (selected) scopes, display the results"
	usage: {
		Higher-level wrapper. Prefix any function with a `profiler/count`:
			profiler/count f: func [x y z] [g [x y z]]
			profiler/count g: func [x] [print x]
			loop 1000 [f 1 2 3]
			profiler/show

		On /* refinementof profiler/count:
		With /* the profiled function should use `return* value` instead of `return value`.
		Without /* it can use `return` but should not define (and call) any inner functions that use `return`,
		otherwise those inner functions will terminate the profiled function instead.

		Lower-level:
		f: does [
			profiler/start 'f-func
			...some weird code...
			g
			...more badass code...
			profiler/stop 'f-func
		]
		g: does [
			profiler/start 'g-func
			...wow another magic...
			profiler/stop 'g-func
		]
		profiler/show

		Do as many (recursive, nested) calls to f or g, their *individual* execution times will be counted.
	}
]


#include %assert.red


if unset? :profiler [

profiler: context [
	times: context []

	t0: 0:0
	stack: copy []

	mark: func [/out /local name t b] [
		t: now/time/precise
		if name: last stack [
			unless in times :name [times: make times reduce [to-set-word name  reduce [0:0 0]] ]
			b: times/:name
			b/1: b/1 + t - t0
			if out [b/2: b/2 + 1]		; don't count exit from an inner call as a call to this func
		]
	]

	start: func ['name] [
		mark
		append/only stack name
		t0: now/time/precise
	]

	stop: func ['name /local lastname] [
		mark/out
		lastname: take/last stack
		assert [lastname = name]
		t0: now/time/precise
	]

	count: func [
		"Prefix any func with me to profile it"
		'name [set-word!] "gotta have a name to account and display"
		func-def [function!] "func definition"
		/* {redefine return* instead of return:
		With /* the profiled function should use `return* value` instead of `return value`.
		Without /* it can use `return` but should not define (and call) any inner functions that use `return`,
		otherwise those inner functions will terminate the profiling function instead}
		/local return-name
	] [
		return-name: either * ['return*]['return]
		do compose [set (to-lit-word name)
			func  append union spec-of :func-def [/local _stackdepth] return-name  compose/only [
				profiler/start (to-word name)
				_stackdepth: length? profiler/stack
				(to-set-word return-name) func [x][throw/name x 'return]
				set/any 'r catch/name (body-of :func-def) 'return
				if _stackdepth = length? profiler/stack (compose [profiler/stop (to-word name)])
				:r
			]
		]
	]

	show: function [] [
		print "^/PROFILING STATS:"
		total: 0:0
		foreach blk values-of times [total: total + blk/1]
		total: max 0:0.001 total 		; no zero division
		lines: copy []
		foreach [name blk] body-of times [
			set [time calls] blk
			percall: round/to  1e6 * (to-float time) / max 1 calls  0.1
			append/only lines reduce [
				round/to (to-percent (time / total)) 0.1 "^-"
				pad name 24
				time "^-in" calls "calls^-"
				pad/left percall 7 "us/call" lf]
		]
		append/only lines reduce [100% "^-" pad "* TOTAL *" 24 total "^/"]
		sort lines
		print lines
	]

]

;-- this one is totally independent
clock: func [
	"Evaluate some code and display the time it took"
	code /local t1 t2
] [
	t1: now/precise/time
	do code
	t2: now/precise/time
	print [(t2 - t1) mold/flat code]
]

]

