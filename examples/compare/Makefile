CIVL = civl
COMPARE = $(CIVL) compare
ADDER_PATH = ./adder/
DIFFUSION_PATH = ./diffusion1d/
MAX_PATH = ./max/

all: sumN add diff1d maxN

sumN: sum/Makefile
	cd sum && make

add: adder/Makefile
	cd adder && make

diff1d: diffusion1d/Makefile
	cd diffusion1d && make

maxN: $(MAX_PATH)max.cvl $(MAX_PATH)max_seq.cvl $(MAX_PATH)max_par.cvl
	$(COMPARE) -inputB=4 -spec $(MAX_PATH)max.cvl $(MAX_PATH)max_seq.cvl \
	-impl -inputNPROCS=2 -inputBLOCK_SIZE=2 $(MAX_PATH)max.cvl $(MAX_PATH)max_par.cvl

clean: 
	rm -f *~
	rm -f -r CIVLREP
