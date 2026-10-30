#
# NOTE: This Makefile relies on GNU make extensions
#

# Instructions:
#
#   touch Makefile.dependencies
#   make depend
#   make -k # -k is only necessary if there are verification errors

FILES:=$(shell echo */*.gh)

.PHONY: all
all: $(FILES:.gh=.ghv)

%.ghv: %.gh
	./gh_verify.py < $<
	@touch $@

clean:
	rm -f $(FILES:.gh=.ghv)

depend:
	egrep '^(import|export)' $(FILES) | sed -e 's!\(.*\)\.gh:.*[ 	]\([^ 	/]*/[^ 	/]*\).*!\1.ghv: \1.gh \2.ghi!' > Makefile.dependencies

include Makefile.dependencies
