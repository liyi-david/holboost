.DEFAULT_GOAL=plugin

MAKEFILE_COQ=Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $(MAKEFILE_COQ)

plugin: Makefile.coq Makefile.coq.local
	make -f $(MAKEFILE_COQ)

install: plugin
	make -f $(MAKEFILE_COQ) install

clean:
	make -f $(MAKEFILE_COQ) clean
	rm -f $(MAKEFILE_COQ)

test: clean install
	@for file in $(shell ls $(CURDIR)/tests/*.v); do \
		printf "testing $$file ... "; \
		echo "" | coqtop -init-file $$file > .test.stdout 2>.test.stderr || { \
			printf "failed !\n"; \
			printf "=== STDOUT ===\n" && cat .test.stdout; \
			printf "=== STDERR ===\n" && cat .test.stderr; \
		}; \
		printf "done.\n"; \
	done
	@rm -f .test.stdout .test.stderr

.merlin: Makefile.coq
	make -f $(MAKEFILE_COQ) .merlin
	echo "PKG yojson" >> .merlin
