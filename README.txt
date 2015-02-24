Structure is as follows:
- AbstractSyntax : Contains the compiler and stack-machine.
- CompExp : Only uses AbstractSyntax.
- DenSemantics :Contains the denotational semantics for the instructions of the language.
- Proofs : Uses AbstractSyntax, CompExp, and DenSemantics. Puts
everything together to form proofs for the stack machine's compiler.
