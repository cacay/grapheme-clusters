
all: coq.mk
	$(MAKE) -f coq.mk


coq.mk: _CoqProject *.v
	coq_makefile -o $@ -f _CoqProject *.v


clean: coq.mk
	$(MAKE) -f coq.mk clean
	rm -f coq.mk


.PHONY: all clean

