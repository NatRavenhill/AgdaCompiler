To approach the task we started by extending the stack machine. We split the files into:

- AbstractSyntax : Contains the definitions of the expressions and their fixities. We added subtraction, logical operators(not, and, or), comparison operators( <= , >=, ==), if_then_else, multiplcation and division and defined their fixities

- CompExp : Contains the stack machine and the compilation to the stack machine. In the stack machine we added instructions for Not, And and Or and an instruction to implement a for loop (FLoop). 
In the compilation we added the compilation for Booleans, using Val 1 to represent true and Val 0 to represent false. We then implemented the compilation for all the given operations and most of the new ones we created in AbstractSyntax. (we did not manage the while loop and for loop 

- DenSemantics :Contains the denotational semantics for the instructions of the language. We added semantics for all of our new operations, except for the for loop. We also implemented some examples of the semantics and compilation in this file to help with our understanding

-Main - contains more examples

-Proofs : Our partial proofs for soundness and adequacy is contained in this file and an explanation of our attempts.
