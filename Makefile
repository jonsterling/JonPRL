BIN=bin

all: smlnj

smlnj:
	sml build/go-nj.sml
	build/mkexec.sh `which sml` `pwd` jonprl

test:
	bin/jonprl example/test.jonprl example/monoid.jonprl example/squash.jonprl

clean:
	rm -f bin/.heapimg.*
	rm -f bin/jonprl
	rm -rf .cm

install:
	rm -f $(DESTDIR)/bin/jonprl.new
	cp bin/jonprl $(DESTDIR)/bin/jonprl.new
	mv $(DESTDIR)/bin/jonprl.new $(DESTDIR)/bin/jonprl

