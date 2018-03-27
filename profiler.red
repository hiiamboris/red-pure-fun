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
		It is imperative to use `return*` instead of `return` inside of this profiled function body.

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

	mark: has [name t] [
		t: now/time/precise
		if name: last stack [
			unless in times :name [times: make times compose [(to-set-word name) 0:0]]
			times/:name: times/:name + t - t0
		]
	]

	start: func ['name] [
		mark
		append/only stack name
		t0: now/time/precise
	]

	stop: func ['name] [
		mark
		assert [(take/last stack) = name]
		t0: now/time/precise
	]

	count: func ['name [set-word!] func-def [function!]] [
		do compose [set (to-lit-word name)
			func spec-of :func-def compose/only [
				profiler/start (to-word name)
				; if I just redefined "return:", any inner (unprofiled) function call would've jumped here immediately
				return*: func [x][throw/name x 'return]
				set/any 'r catch/name (body-of :func-def) 'return
				profiler/stop (to-word name)
				:r
			]
		]
	]

	show: has [lines total] [
		print "^/PROFILING STATS:"
		total: 0:0
		foreach [name time] body-of times [total: total + time]
		total: max 0:0.001 total 		; no zero division
		lines: copy []
		foreach [name time] body-of times [
			append/only lines reduce [round/to (to-percent (time / total)) 0.1 "^-" name "^-" time "^/"]
		]
		sort lines
		print lines
	]

]



]

