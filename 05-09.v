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
(*Try to work out the above code*)

Compute (and_b false true).

Definition or_b (x y:bool) := match x with 
                            | true => true
                            | false => y
                            end.

Compute (or_b true true).
