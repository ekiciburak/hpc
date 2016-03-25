DIRS=exc_cl-hp exc_pl-hp st-hp
MAKF=$(DIRS:%=%/Makefile)

all: $(MAKF)

%/Makefile:%/make_Makefile
	(cd $*; ./make_Makefile; make)

clean:
	- $(foreach dir, $(DIRS), (cd $(dir); make clean; rm Makefile; rm *~; rm *.pdf; rm *.html; rm *.css);)
