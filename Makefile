
all: coq.mk
	$(MAKE) -f coq.mk


coq.mk: _CoqProject coq-src/*.v
	coq_makefile -f _CoqProject -o $@ coq-src/*.v


clean: coq.mk
	$(MAKE) -f coq.mk clean
	rm -f coq.mk


.PHONY: all clean

