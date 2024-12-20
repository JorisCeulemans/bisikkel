all: Everything.agda
	agda -i . Everything.agda
.PHONY: all

Everything.agda:
	echo "{-# OPTIONS --guardedness #-}\n--The guardedness option is only necessary for the guarded recursion application.\n\nmodule Everything where\n" > Everything.agda
	find -name '*.agda' ! -name 'Everything.agda' -printf '%p\n' | sed 's/\.\//import /' | sed 's/.agda//; s/\//\./g' >> Everything.agda

.PHONY: clean
clean:
	rm -rf _build/
	rm -f Everything.agda
