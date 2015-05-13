### Building JonPRL

JonPRL uses SML/NJ's [CM](http://www.smlnj.org/doc/CM/) for its build, and
[Smackage](https://github.com/standardml/smackage) for its dependencies.
(JonPRL is likely compatible with other SML implementations, but I currently
rely on CM and don't have the engineering bandwidth to test it with other
implementations and build systems.)

First make sure you have SML/NJ and Smackage set up properly. Then, install
JonPRL's dependencies:

```sh
smackage get parcom
```

Finally, JonPRL may be built through the SML/NJ top-level as follows:

```
rlwrap sml
> CM.make "sources.cm";
```

Currently the only interface to JonPRL is as a library; the `Test` module
currently demonstrates how to interact with JonPRL, and is automatically
executed when `CM.make "sources.cm"` is called.

In the future, a proper top-level interface to JonPRL is of course desired, and
a Makefile for constructing binaries should be added.
