(* Proof of transitivity of the sublist relationship:*)

open HolKernel Parse boolLib bossLib

val _ = new_theory "foo"

val sublist_def = Define`
    		  (sublist [] l1 = T) /\
  (sublist (h::t) [] = F) /\
  (sublist (x::l1) (y::l2) = (x = y) /\ sublist l1 l2 \/ sublist (x::l1) l2)`;

val _  = overload_on ("<=", ``sublist``)

(* This is to make the sublist theory usable by SRW_TAC *)
val _ = export_rewrites ["sublist_def"];


val cons_front_lemma = prove(
  ``!l1 l2. sublist l1 l2 ==> sublist l1 (h::l2)``,
  Induct_on `l1` THEN SRW_TAC [][] THEN Cases_on `l2` THEN SRW_TAC [][]);

val sublist_NIL = store_thm(
  "sublist_NIL",
  ``(l1:'a list) <= [] <=> (l1 = [])``,
  Cases_on `l1` THEN SRW_TAC [][]); 
val _ = export_rewrites ["sublist_NIL"]

val sublist_trans = store_thm(
  "sublist_trans",
  ``!l1 l2 l3:'a list. l1 <= l2 /\ l2 <= l3 ==> l1 <= l3``,
  Induct_on `l3` THEN SIMP_TAC (srw_ss()) [] THEN 
  Cases_on `l1` THEN SRW_TAC [][] THEN
  Cases_on `l2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
  METIS_TAC [sublist_def]);

val _ = export_theory()




(*
g `!l1 l2 l3. sublist l1 l2 /\ sublist l2 l3 ==> sublist l1 l3`;
expand (Induct_on `l1`);


For proving the base case

     expand(REPEAT STRIP_TAC);
expand(SRW_TAC [][]);

    


To prove the inductive case
Induct on l2
expand(Induct_on `l2`);


To prove l2 base case
expand(REPEAT GEN_TAC);
expand(SRW_TAC [] []);


And then to prove the general inductive case
Induct on l3
expand(Induct_on `l3`);



Proving the base case
expand(REPEAT GEN_TAC);
expand(SRW_TAC [] []);

Going back to the main inductive case
expand(REPEAT GEN_TAC);
expand(REPEAT STRIP_TAC);

expand(Q_TAC SUFF_TAC `( (h''=h') /\ sublist l1 l2) \/ sublist (h''::l1) l2 `);
expand(REPEAT STRIP_TAC);

expand(Q_TAC SUFF_TAC `( (h'=h) /\ sublist l2 l3) \/ sublist (h'::l2) l3 `);
expand(REPEAT STRIP_TAC);
expand(SRW_TAC [] []);
expand(METIS_TAC [sublist_def]);

expand(SRW_TAC [] []);
expand(METIS_TAC [sublist_def]);

expand(SRW_TAC [] []);
expand(METIS_TAC [sublist_def] );

expand(SRW_TAC [] []);
expand(METIS_TAC [sublist_def] );

expand(SRW_TAC [] []);
expand(METIS_TAC [sublist_def] );



------------------------------------------------------------------------------
Proof of concatenation respect:

val sublist_def = Define`
    		  (sublist [] l1 = T) /\
  (sublist (h::t) [] = F) /\
  (sublist (x::l1) (y::l2) = (x = y) /\ sublist l1 l2 \/ sublist (x::l1) l2)`;


This is to make the sublist theory usable by SRW_TAC
val _ = export_rewrites ["sublist_def"];
g `!l1 l2 l3 l4. sublist l1 l3 /\ sublist l2 l4 ==> sublist (APPEND l1 l2) (APPEND l3 l4)`;
expand (Induct_on `l1`);
expand (Induct_on `l2`);

to prove the base case;
expand(SRW_TAC [] []);
expand (Induct_on `l3`);

to prove the base case
expand(SRW_TAC [] []);
expand (Induct_on `l4`);

to prove the base case
expand(SRW_TAC [] []);
expand (Induct_on `l3`);
expand(SRW_TAC [] []);

To prove l4 inductive case:
expand(REPEAT STRIP_TAC);
expand(FULL_`SIMP_TAC (srw_ss()) []);


repeating the same to prove the inductive step of l1
expand (Induct_on `l2`);
expand (Induct_on `l3`);
expand(SRW_TAC [] []);
expand (Induct_on `l4`);
expand(SRW_TAC [] []);
expand(REPEAT STRIP_TAC);
expand(SRW_TAC [][]);
expand(Q_TAC SUFF_TAC `( (h''=h') /\ sublist l1 l3) \/ sublist (h''::l1) l3 `);
expand(REPEAT STRIP_TAC);
expand(METIS_TAC [sublist_def, listTheory.APPEND_NIL]);
expand(METIS_TAC [sublist_def, listTheory.APPEND_NIL]);
expand(METIS_TAC [sublist_def]);


repeating the same to prove the inductive step of l2
expand (Induct_on `l3`);
expand (Induct_on `l4`);
expand(SRW_TAC [][]);
expand(FULL_SIMP_TAC (srw_ss()) []);
expand(REPEAT STRIP_TAC);
expand(FULL_SIMP_TAC (srw_ss()) []);


*)
