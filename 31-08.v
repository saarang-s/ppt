Print True.
Print bool.
Print False.

Print and.
Check and.
Print conj.
Check conj.

Print or.
Check or.
Check or_introl.
Check or_intror.

Definition foo (x : bool) := match x with 
                | true => nat
                | false => bool
end.

Check foo.

(* Prove not(False)*)

Lemma not_false : not False.
unfold not.
intro.
trivial.
Show Proof.
Qed.

Lemma not_not_A : forall (A: Prop),A-> not (not A).
intro.
unfold not.
intro.
intro.
exact (H0(H)).
Show Proof.
Qed.
