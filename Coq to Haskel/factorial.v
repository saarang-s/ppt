Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * factorial n'
  end.

Require Extraction.

Extraction Language Haskell.

Extraction "/home/saarang/Semester 7/Proofs Types/Coq to Haskel/factorial.hs" factorial.