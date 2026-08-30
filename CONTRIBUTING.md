We very much welcome contributions all forms, including feedback sharing, bug reports, feature requests, improved documentation, and source code or library contributions.

Before preparing a pull request (PR), please test your changes beforehand, running `dune build` to check that the Cube source code compiles properly and then checking that nothing in the library `lib/all.cube` was broken.

Here are some items on our TODO list:

- Add explicit @ handling of implicit arguments
- Coercion reduction rules for constructors of inductive types
- Do not automatically unfold terms tagged as theorem or as lemma
- Expand the library with more formalized math for testing strengths and limits
- Fix universe polymorphism bug when universe level occurs in proof
- Add structures
- Parse unicode subscript, superscript, Greek letters properly
- Proper handling of Infer in command apart from Thm
- Wildcard printing: user should not see inductive data as part of context when _ is entered in a proof (remove ind@ctx hack)
- Parse numbers in applied exprs (but not as levels) as sss...s0, e.g 2 as ss0
- Let-in local definitions
- Introduce Quotients types
- Opening of modules for referring to module.foo as foo
- Go to definition VS code extension feature
- Publish VS Code extension
- readthedocs documentation