open HolKernel Parse boolLib bossLib

val _ = new_theory "foo"
open listTheory
val sublist_def = Define`
    		  (sublist [] l1 = T) /\
  (sublist (h::t) [] = F) /\
  (sublist (x::l1) (y::l2) = (x = y) /\ sublist l1 l2 \/ sublist (x::l1) l2)`;

(* val _  = overload_on ("<=", ``sublist``) *)

(* This is to make the sublist theory usable by SRW_TAC *)
(* val _ = export_rewrites ["sublist_def"];*)


val sublist_cons = store_thm("sublist_cons",
``!l1 l2 h. sublist l1 l2 ==> sublist l1
  (h::l2)``, Induct_on `l1` THEN SRW_TAC [][] THEN Cases_on `l2` THEN
  SRW_TAC [][sublist_def]);

val sublist_NIL = store_thm(
  "sublist_NIL",
  ``sublist (l1:'a list) [] <=> (l1 = [])``,
  Cases_on `l1` THEN SRW_TAC [][sublist_def]); 
val _ = export_rewrites ["sublist_NIL"]

val sublist_trans = store_thm(
  "sublist_trans",
  ``!l1 l2 l3:'a list. sublist l1  l2 /\ sublist l2 l3 ==> sublist l1 l3``,
  Induct_on `l3` THEN SIMP_TAC (srw_ss()) [] THEN 
  Cases_on `l1` THEN SRW_TAC [][] THEN
  Cases_on `l2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
  METIS_TAC [sublist_def]);


val append_sublist_1 = store_thm("append_sublist_1",
``!l1 l2 l. sublist (l1 ++ l2 ) l
      	       ==> sublist (l1) l /\ sublist (l2) l``,
Induct_on `l`
THEN SRW_TAC[][sublist_def]
THEN Cases_on `l1`
THEN FULL_SIMP_TAC(srw_ss())[sublist_def]
THENL
[
        `sublist t l` by (FIRST_X_ASSUM (Q.SPECL_THEN [`t`,`l2`] MP_TAC)  THEN SRW_TAC[][sublist_def]) 
        THEN SRW_TAC[][sublist_def]
        ,
        METIS_TAC[(GSYM (MATCH_MP AND2_THM APPEND))]
	,
	Cases_on `l2`
	THEN FULL_SIMP_TAC(srw_ss())[sublist_def]
	THEN METIS_TAC[]
	,
	Q.PAT_ASSUM `sublist (h'::(t ++ l2)) l` (ASSUME_TAC o REWRITE_RULE[(GSYM (MATCH_MP AND2_THM APPEND))])
	THEN `sublist l2 l` by (FIRST_X_ASSUM (Q.SPECL_THEN [`h'::t`, `l2`] MP_TAC)  THEN SRW_TAC[][sublist_def]) 
	THEN Cases_on `l2`
	THEN FULL_SIMP_TAC(srw_ss())[sublist_def]
]);



val append_sublist = store_thm("append_sublist",
``!l1 l2 l3 l. sublist (l1 ++ l2 ++ l3) l
      	       ==> sublist (l1 ++ l3) l``,
Induct_on `l`
THEN SRW_TAC[][sublist_def]
THEN Cases_on `l1`
THEN FULL_SIMP_TAC(srw_ss())[sublist_def]
THEN1 METIS_TAC[append_sublist_1]
THEN1 METIS_TAC[]
THEN REWRITE_TAC[ Once (GSYM (MATCH_MP AND2_THM APPEND))]
THEN Q.PAT_ASSUM `sublist (h'::(t ++ l2 ++ l3)) l` (ASSUME_TAC o REWRITE_RULE[(GSYM (MATCH_MP AND2_THM APPEND))]) 
THEN METIS_TAC[]);


val sublist_refl = store_thm("sublist_refl",
``!l. sublist l l``,
Induct_on `l`
THEN SRW_TAC[][sublist_def]
);

val sublist_subset = store_thm("sublist_subset",
``!l1 l2. sublist l1 l2
      	  ==> set l1 SUBSET set l2``,
cheat
);


val sublist_append = store_thm("sublist_append",
``!l1 l1' l2 l2'. sublist l1 l1' /\ sublist l2 l2'
      	     	  ==> sublist (l1 ++ l2) (l1' ++ l2')``,
cheat
);


val sublist_length = store_thm("sublist_length",
``!l l'. sublist l l' 
      	     	  ==> LENGTH (l) <= LENGTH(l')``,
cheat
);

val sublist_filter = store_thm("sublist_filter",
``!l P. sublist (FILTER P l) l``,
cheat
);

val sublist_append_2 = store_thm("sublist_append_2",
``!l1 l2 l3. sublist l1 l2 
      	     	  ==> sublist l1 (l2 ++ l3)``,
cheat
);

val sublist_cons_2 = store_thm("sublist_cons_2",
``!l1 l2 h. sublist (h::l1) (h::l2)
      	     	  <=> sublist l1 l2``,
cheat);

val sublist_cons_3 = store_thm("sublist_cons_3",
``!l1 l2 h. sublist (h::l1) (l2)
      	     	  ==> sublist l1 l2``,
cheat);

val sublist_every = store_thm("sublist_every",
``!l1 l2 P. sublist (l1) (l2) /\ EVERY P l2
      	     	  ==> EVERY P l1 ``,
cheat);

val sublist_append_exists = store_thm("sublist_append_exists",
``!l1 l2 h. sublist (h::l1) (l2)
      	     	  ==> ?l3 l4. (l2 = l3 ++ [h] ++ l4 ) /\ sublist l1 l4``,
cheat);

val sublist_append_4 = store_thm("sublist_append_4",
``!l l1 l2 h. sublist (h::l) (l1 ++ [h] ++ l2) /\ EVERY (\x. ~(h = x)) l1
      	     	  ==> sublist l l2``,
cheat);

val sublist_append_5 = store_thm("sublist_append_5",
``!l l1 l2 h. sublist (h::l) (l1 ++ l2) /\ EVERY (\x. ~(h = x)) l1
      	     	  ==> sublist (h::l) l2``,
cheat);


val _ = export_theory()