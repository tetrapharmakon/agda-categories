.PHONY: check clean

AGDA    := agda -i src --warning=noUserWarning --warning=noUnsupportedIndexedMatch --warning=noUselessPrivate
AGDA_OUT:= agda-check.log
SOURCES := $(shell find . -name '*.agda' -not -path './Incoherent/*')
SOURCES += $(shell find ./Incoherent -name '*.agda')
ALL     := $(sort $(SOURCES))

check:
	@ok=true; count=0; fail=0; log=$(AGDA_OUT); \
	rm -f $$log; \
	for f in $(ALL); do \
	  count=$$((count+1)); \
	  printf "  %-50s " "$$f"; \
	  if $(AGDA) "$$f" >>$$log 2>&1; then \
	    printf "\033[32m\xE2\x9C\x93\033[0m\n"; \
	  else \
	    printf "\033[31m\xE2\x9C\x97\033[0m\n"; \
	    ok=false; fail=$$((fail+1)); \
	  fi; \
	done; \
	echo ""; \
	if $$ok; then \
	  rm -f $$log; \
	  echo "All $$count files passed."; \
	else \
	  echo "$$fail/$$count failed. See $$log for details."; \
	  echo "Or re-run: make check-one FILE=<path>"; \
	  false; \
	fi

check-one:
	@if [ -z "$(FILE)" ]; then echo "Usage: make check-one FILE=src/Categories/Rosen/Foo.agda"; false; fi
	$(AGDA) "$(FILE)"

clean:
	find . -name '*.agdai' -exec rm {} \;
