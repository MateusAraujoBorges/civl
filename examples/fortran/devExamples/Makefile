
CIVL=civl
VERIFY=$(CIVL) verify

all: computedGoto_doLoop_Sample inclusionSample

computedGoto_doLoop_Sample: computedGoto_doLoop_Sample.f
	$(VERIFY) computedGoto_doLoop_Sample.f

inclusionSample: inclusionSample.f
	$(VERIFY) inclusionSample.f TESTINCLUDE

clean:
	rm -rf CIVLREP *~



