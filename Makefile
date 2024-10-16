all: Everything.agda
	agda -i . Everything.agda

Everything.agda:
	echo "{-# OPTIONS --guardedness #-}\n--The guardedness option is only necessary for the guarded recursion application.\n\nmodule Everything where\n" > Everything.agda
	find -name '*.agda' ! -name 'Everything.agda' -printf '%p\n' | sed 's/\.\//import /' | sed 's/.agda//; s/\//\./g' >> Everything.agda

.PHONY: clean
clean:
	rm -r _build/
	rm Everything.agda
