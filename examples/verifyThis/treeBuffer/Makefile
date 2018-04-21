CIVL=civl
VERIFY=$(CIVL) verify
COMPARE=$(CIVL) compare

all: compare1 compare2 compare3

## naive v.s. real time
compare1: driver.cvl treebuffer_naive.cvl treebuffer.cvl treebuffer.h
	$(COMPARE) -checkMemoryLeak=false -spec driver.cvl treebuffer_naive.cvl -impl driver.cvl treebuffer.c

## naive v.s. caterpillar
compare2: driver.cvl treebuffer_naive.cvl treebuffer_caterpillar.cvl treebuffer.h
	$(COMPARE) -checkMemoryLeak=false -spec driver.cvl treebuffer_naive.cvl -impl driver.cvl treebuffer_caterpillar.cvl

## caterpillar v.s. real time (with memory leak check)
compare3: driver.cvl treebuffer_caterpillar.cvl treebuffer.cvl treebuffer.h
	$(COMPARE) -spec driver.cvl treebuffer_caterpillar.cvl -impl driver.cvl treebuffer.c

bound: driver_heap_bound.cvl treebuffer.cvl
	$(VERIFY) driver_heap_bound.cvl treebuffer.cvl

clean:
	rm -rf CIVLREP SARL_Why3 *~