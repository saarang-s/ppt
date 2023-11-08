(* Definition eq (A : Type) x d *)

Inductive eq {A : Type} : A -> A -> Prop := 
                                            |eq_refl {x: A} : eq x x .

(* Inductive eq {A : Type} : A -> A -> Prop := 
                                            |eq_refl : forall x: A, eq x x .
 *)

(* sym : forall A (x y: A), eq x y -> eq y x *)

Definition sym {A} (x y: A) (pf : eq x y): eq y x := match pf with 
                                                    | eq_refl => eq_refl
                                                    end.

Inductive eq2 {A : Type} (x : A) : A -> Prop :=
                                              | eq_refl2 : eq2 x x.


(* trans : forall A (x y : A), eq x y -> forall z eq y z -> eq x z *)

Theorem trans : forall A (x y : A), eq x y -> forall z, eq y z -> eq x z .
Proof.
intros.
destruct H .
destruct H0.
exact eq_refl.
Qed.

(* This might not work

Definition trans_def  A (x y z: A) (pf1 : eq x y) (pf2 : eq y z) : eq x z := 
                                                                          match pf1 with 
                                                                          | eq_refl => match pf2 with 
                                                                                       | eq_refl => eq_refl end 
                                                                          end. *)

Definition trans_def A (x y: A) (pf1 : eq x y) : forall (z: A), eq y z -> eq x z := match pf1 with 
                                                                                  | eq_refl => 
                                                                                    fun (z : A) pf2 => pf2
                                                                                    end.




