# Makefile for dioid

COQ_PROJ := _CoqProject
ROCQ_MAKEFILE := Makefile.rocq
ROCQ_MAKE := +$(MAKE) -f $(ROCQ_MAKEFILE)

ifneq "$(ROCQBIN)" ""
	ROCQBIN := $(ROCQBIN)/
else
	ROCQBIN := $(dir $(shell which coqc))
endif
export ROCQBIN

all install html gallinahtml: $(ROCQ_MAKEFILE) Makefile
	$(ROCQ_MAKE) $@

%.vo: %.v
	$(ROCQ_MAKE) $@

$(ROCQ_MAKEFILE): $(COQ_PROJ)
	$(ROCQBIN)rocq makefile -f $< -o $@

clean:
	-$(ROCQ_MAKE) clean

distclean: clean
	$(RM) $(ROCQ_MAKEFILE) $(ROCQ_MAKEFILE).conf
	$(RM) *~ .*.aux .lia.cache


-include $(ROCQ_MAKEFILE).conf

.PHONY: all install html gallinahtml clean distclean
