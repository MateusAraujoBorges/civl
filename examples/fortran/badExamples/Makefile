
CIVL=civl
VERIFY=$(CIVL) verify

all: badDivideZero badIndex

badDivideZero: badDivideZero.f
	$(VERIFY) badDivideZero.f

badIndex: badIndex.f
	$(VERIFY) badIndex.f

clean:
	rm -rf CIVLREP *~



