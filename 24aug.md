- commands on for coq
```
Ctrl c n
Ctrl c ret
Ctrl c b 
```
- There are 3 interesting types
    - Prop, Set, Type
    - Elements of Prop are types itself.
    - If it is a mathematical statement it is called a Prop.
    - The proof term is usually Prop type.
    - Prop are terms with type which do not have any computational content in it. It is for the proof checking.

- true and false are values of type bool.
- But True and False are values of Prop (and are also types (as we said earlier))

- The tactics provides a term (that we need not trust) but when we do a 'Qed' and if the term is true then we can trust it. Because the coq will be checking that term.
- We essentially use tactic to generate a term and we use coq to check it.
- 