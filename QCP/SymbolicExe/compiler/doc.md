This directory contains the front end of SAC.

### [hashtbl.c](hashtbl.c)
This file contains implementation of a fixed-size linked hash table.

### [lexer.h](lexer.h) [lexer.l](lexer.l)
This file contains the lexer. The followings are unusual:
- The lexer is _reentrant_.
- We need an additional parameter to decide whether an identifier can be a
  type. This is to solve the famous ambiguous problem of C syntax in the presence
  of `typedef`.
- The header file is not automatically generated. Flex does not recognize the
  `lex_param` option in the parser file, so we define `YY_DECL` macro
  manually. (We can also define the macro in another file and include it before
  `lexer.h`. In this case, `lexer.h` will not redefine it.)

### [parser.y](parser.y)
This file contains the parser. It is a _pure_, _push_ parser, so you have to
manually feed it tokens. The result is stored in a pointer passed to
`yy_pushparse`.

### [lang.h](lang.h)
This file contains the syntax tree of complete C programs. Note that it is already
elaborated, compared to the source code.

### [plang.h](plang.h)
This file contains the syntax tree of _partial programs_. SAC is designed to work
interactively, so we cannot expect the user to write complete programs as
input. Rather, we read in meaningful pieces, namely partial programs,
incrementally.

### [alang.h](alang.h)
This file contains the syntax tree of _user assertions_. The internal
representation of assertions, __inner assertions_, is different from a user's
point of view.

### [env.h](env.h)
This file contains the definition of the program environment. It is mostly used
to look up various kinds of identifiers. The _local environment_ is indexed by
strings; it is updated according to C's scope rules. The _global environment_ is
indexed by unique identifiers--that is, in our case, natural numbers.

### [pparser.c](pparser.c)
This file contains various parser interface. 'parser' here is a broad term, a
synonym of 'front end'. Functions in this file assembly low-level passes
scattered in files beginning with 'cp' (that is, 'compiler pass').

### [ptrans.c](ptrans.c)
This file contains the missing automata, like that in a standard LR parser. It
is tedious, but we have a better control of the parsing process; for example, we
can handle context-sensitive grammars (although we do not need it
currently). `trans` also calls functions provided in `pparser.c`, so you can use
`trans` as the entry to process a partial program produced by the parser.

### [CP lift](cplift.c)
This pass lift anonymous, nested type definition to toplevel.

### [CP array parameter](cparrparam.c)
This pass convert array types of function parameters, if there is any, to
pointer types. This is compatible with the C standard.

### [CP assertion](cpassert.c)
This pass convert user assertions to inner assertions. Please refer to [todo]
for more information.

### [CP binding](cpbind.c)
This pass resolve various string references, such as variables and structure
names, to unique identifiers.

### [CP constant](cpconst.c)
This pass compute the values of expressions that should be
constants, including

- array sizes;
- conditions in `case` clauses;
- `sizeof` expressions.

To that end, we also compute sizes and alignments of structures and unions.

### [CP definition](cpdef.c)
This pass provides wrappers to define new entities. They check for redefinition,
conflicting types, and so on.

### [CP incomplete](cpincomplete.c)
This pass checks the use of incomplete types. Incomplete types cannot be taken
size of, or be used to define variables. Of course, there should not be
assignments in incomplete types; this is checked in another pass. See next.

### [CP pointer arithmetic](cpptrarith.c)
This pass, again, checks the use of incomplete types. We separate it out to
prevent circular dependency between passes.

### [CP left value](cplval.c)
This pass checks the use of _left values_. Only left values can be assigned or
taken address of.

### [CP type](cptype.c)
This pass does type checking, and tries to infer missing type annotations in
assertions. The inference mechanism is rather weak now.

### [CP user](cpuser.c)
This pass provides functions to convert inner assertions back to user
assertions. We make sure that if you convert the result to an inner assertion
again, its meaning is unchanged.
