BIN=bin

all: smlnj

smlnj:
	sml go-nj.sml
	bin/mkexec.sh `which sml` `pwd` jonprl

clean:
	rm -f bin/.heapimg.*
	rm -f bin/jonprl

install:
	rm -f $(DESTDIR)/bin/jonprl.new
	cp bin/jonprl $(DESTDIR)/bin/jonprl.new
	mv $(DESTDIR)/bin/jonprl.new $(DESTDIR)/bin/jonprl

