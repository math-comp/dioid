# Makefile for dioid

COQ_PROJ := _CoqProject
COQ_MAKEFILE := Makefile.coq
COQ_MAKE := +$(MAKE) -f $(COQ_MAKEFILE)

ifneq "$(COQBIN)" ""
	COQBIN := $(COQBIN)/
else
	COQBIN := $(dir $(shell which coqc))
endif
export COQBIN

all install html gallinahtml: $(COQ_MAKEFILE) Makefile
	$(COQ_MAKE) $@

%.vo: %.v
	$(COQ_MAKE) $@

$(COQ_MAKEFILE): $(COQ_PROJ)
	$(COQBIN)coq_makefile -f $< -o $@

clean:
	-$(COQ_MAKE) clean

distclean: clean
	$(RM) $(COQ_MAKEFILE) $(COQ_MAKEFILE).conf
	$(RM) *~ .*.aux .lia.cache


-include $(COQ_MAKEFILE).conf

.PHONY: all install html gallinahtml clean distclean
