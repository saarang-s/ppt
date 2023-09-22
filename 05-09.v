Print "/\".
Locate "/\".

(* Trying to solve De-Morgans Law*)
(* *)


Goal forall A B, not (A) /\ not (B) -> not ( or A  B).
intros A B .
refine (fun pf => fun qf => match pf with 
                            | conj nPa nPb => 
                                          match qf with 
                                          | or_introl a => nPa a 
                                          | or_intror b => nPb b
                                          end
                                          end).
Qed.

(*Goal forall A B, not (A) /\ not (B) -> not ( or A B).*)

Definition and_b (x y: bool):= match x with 
                              | false => false
                              | true => y
                              end.
Qed.
(*Try to work out the above code*)

Print and_b true true.

