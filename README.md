JonPRL is a proof refinement logic in the sense of λ-PRL or
[Nuprl](http://www.nuprl.org); JonPRL inherits its [computational type
theory](http://www.sciencedirect.com/science/article/pii/S1570868305000704)
from Allen, Bickford, Constable, Harper and many other names.

### Building & Installing JonPRL

JonPRL uses SML/NJ's [CM](http://www.smlnj.org/doc/CM/) for its build, and
[Smackage](https://github.com/standardml/smackage) for its dependencies.
(JonPRL is likely compatible with other SML implementations, but I currently
rely on CM and don't have the engineering bandwidth to test it with other
implementations and build systems.)

First make sure you have SML/NJ and Smackage set up properly. Then, install
JonPRL's dependencies:

```sh
git submodule init
git submodule update
smackage get parcom
```

Then, JonPRL may be built using its `Makefile`:

```sh
make smlnj
make test
```

This puts a binary in `./bin/jonprl`. Optionally, you may install JonPRL globally using:

```sh
sudo make install
```

### Running JonPRL

To run JonPRL, simply direct it at your development:

```sh
jonprl example/test.jonprl
```

You may specify as many files as you like in this command; they will be refined
in order, in case of any dependencies.
