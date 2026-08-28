We very much welcome contributions all forms, including feedback sharing, bug reports, feature requests, improved documentation, and source code or library contributions.

Before preparing a pull request (PR), please test your changes beforehand, running `dune build` to check that the Cube source code compiles properly and then checking that nothing in the library `lib/all.cube` was broken.

Here are some items on our TODO list:

- Expand the library with more formalized math for testing the limits of Cube
- Coercion reduction rules for constructors of inductive types
- Add type constructor inference
- Add explicit @ handling of implicit arguments
- Reintroduce Prod/Sigma as an inductive type to simplify the kernel
- Fix universe polymorphism bug when universe level occurs in proof
- Add structures
- Parse unicode subscript, superscript, Greek letters properly
- Add a better syntax Infer without : for empty ctx
- Wildcard printing: user should not see inductive data as part of context when _ is entered in a proof (remove ind@ctx hack)
- Parse numbers in applied exprs (but not as levels) as sss...s0, e.g 2 as ss0
- Let-in local definitions
- Introduce Quotients types
- readthedocs documentation
- Opening of modules for referring to module.foo as foo
- Go to definition VS code extension feature