.DEFAULT_GOAL=plugin

MAKEFILE_COQ=Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $(MAKEFILE_COQ)

plugin: Makefile.coq
	make -f $(MAKEFILE_COQ)

install: plugin
	make -f $(MAKEFILE_COQ) install

clean:
	make -f $(MAKEFILE_COQ) clean
	rm -f $(MAKEFILE_COQ)

.merlin: Makefile.coq
	make -f $(MAKEFILE_COQ) .merlin
