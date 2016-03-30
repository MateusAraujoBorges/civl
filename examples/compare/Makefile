all: sumN add diff1d maxN output outputF queueT simpleT svector

sumN: sum/Makefile
	cd sum && make

add: adder/Makefile
	cd adder && make

diff1d: diffusion1d/Makefile
	cd diffusion1d && make

dotP: dot/Makefile
	cd dot && make

maxN: max/Makefile
	cd max && make

output:	outputTest/Makefile
	cd outputTest && make

outputF: outputfile/Makefile
	cd outputfile && make

queueT: queue/Makefile
	cd queue && make

simpleT: simple/Makefile
	cd simple && make

svector: sliced_vector/Makefile
	cd sliced_vector && make

clean: 
	rm -f *~
	rm -f -r CIVLREP
