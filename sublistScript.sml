open HolKernel Parse boolLib bossLib

open listTheory

val _ = new_theory "sublist"
val sublist_def = Define`
    		  (sublist [] l1 = T) /\
  (sublist (h::t) [] = F) /\
  (sublist (x::l1) (y::l2) = (x = y) /\ sublist l1 l2 \/ sublist (x::l1) l2)`;

(* val _  = overload_on ("<=", ``sublist``) *)

(* This is to make the sublist theory usable by SRW_TAC *)
(* val _ = export_rewrites ["sublist_def"];*)
val sublist_refl = store_thm(
  "sublist_refl",
  ``!l. sublist l l``,
  Induct_on `l` THEN SRW_TAC[][sublist_def]);
val _ = export_rewrites ["sublist_refl"]

val sublist_cons = store_thm("sublist_cons",
``!l1 l2 h. sublist l1 l2 ==> sublist l1 (h::l2)``,
  Induct_on `l1` THEN SRW_TAC [][] THEN Cases_on `l2` THEN
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

val sublist_length = store_thm("sublist_length",
``!l l'. sublist l l' ==> LENGTH l <= LENGTH l'``,
HO_MATCH_MP_TAC (theorem "sublist_ind") THEN SRW_TAC [][sublist_def] THEN
RES_TAC THEN DECIDE_TAC);

val sublist_CONS1_E = store_thm(
  "sublist_CONS1_E",
  ``!l1 l2. sublist (h::l1) l2 ==> sublist l1 l2``,
  HO_MATCH_MP_TAC (theorem "sublist_ind") THEN SRW_TAC [][sublist_def] THEN
  FULL_SIMP_TAC (srw_ss()) []);

val sublist_equal_lengths = store_thm(
  "sublist_equal_lengths",
  ``!l1 l2. sublist l1 l2 /\ (LENGTH l1 = LENGTH l2) ==> (l1 = l2)``,
  HO_MATCH_MP_TAC (theorem "sublist_ind") THEN SRW_TAC [][sublist_def] THENL [
    METIS_TAC [LENGTH_NIL],
    METIS_TAC [],
    IMP_RES_TAC sublist_length THEN FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    METIS_TAC[sublist_CONS1_E]
  ]);

val sublist_antisym = store_thm(
  "sublist_antisym",
  ``sublist l1 l2 /\ sublist l2 l1 ==> (l1 = l2)``,
  METIS_TAC [arithmeticTheory.LESS_EQUAL_ANTISYM, sublist_equal_lengths, sublist_length]);

val sublist_append_back = store_thm(
  "sublist_append_I",
  ``!l1 l2. sublist l1 (l2 ++ l1)``,
  Induct_on `l2` THEN SRW_TAC [][sublist_def] THEN
  METIS_TAC [sublist_cons]);

val sublist_snoc = store_thm(
  "sublist_snoc",
  ``!l1 l2 h. sublist l1 l2 ==> sublist l1 (l2 ++ [h])``,
  HO_MATCH_MP_TAC (theorem "sublist_ind") THEN SRW_TAC [][sublist_def] THEN
  METIS_TAC []);

val sublist_append_front = store_thm(
  "sublist_append_front",
  ``!l1 l2. sublist l1 (l1 ++ l2)``,
  Induct_on `l1` THEN SRW_TAC [][sublist_def]);

val sublist_append1_E = store_thm(
  "sublist_append1_E",
  ``sublist (l1 ++ l2) l ==> sublist l1 l /\ sublist l2 l``,
  METIS_TAC [sublist_trans, sublist_append_front, sublist_append_back]);

val append_sublist_1 = save_thm("append_sublist_1", sublist_append1_E);

val sublist_cons_exists = store_thm(
  "sublist_cons_exists",
  ``!h l1 l2.
      sublist (h::l1) l2 <=>
      ?l2a l2b. (l2 = l2a ++ [h] ++ l2b) /\
                ~MEM h l2a /\
                sublist l1 l2b``,
  Induct_on `l2` THEN SRW_TAC [][sublist_def] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL [
    MAP_EVERY Q.EXISTS_TAC [`[]`, `l2`] THEN SRW_TAC [][],
    Cases_on `h = h'` THEN SRW_TAC [][] THENL [
      Q.EXISTS_TAC `[]` THEN SRW_TAC[][] THEN
      METIS_TAC[sublist_append_back, sublist_trans],
      Q.EXISTS_TAC `h::l2a` THEN SRW_TAC [][]
    ],
    Cases_on `h = h'` THEN SRW_TAC [][] THEN
    Cases_on `l2a` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    METIS_TAC[]
  ]);

val sublist_append_exists = store_thm(
  "sublist_append_exists",
  ``!l1 l2 l3.
      sublist (l1 ++ l2) l3 <=>
      ?l3a l3b. (l3 = l3a ++ l3b) /\ sublist l1 l3a /\ sublist l2 l3b``,
  Induct THEN SRW_TAC [][sublist_def, EQ_IMP_THM, sublist_cons_exists] THENL [
    METIS_TAC [APPEND],
    METIS_TAC [sublist_trans, sublist_append_back],
    SRW_TAC [boolSimps.DNF_ss][] THEN METIS_TAC[],
    SRW_TAC [boolSimps.DNF_ss][] THEN METIS_TAC[]
  ]);

val sublist_append_both_I = store_thm(
  "sublist_append_both_I",
  ``sublist a b /\ sublist c d ==> sublist (a ++ c) (b ++ d)``,
  METIS_TAC [sublist_append_exists]);

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


val sublist_subset = store_thm("sublist_subset",
  ``!l1 l2. sublist l1 l2 ==> set l1 SUBSET set l2``,
  SIMP_TAC (srw_ss()) [pred_setTheory.SUBSET_DEF] THEN
  HO_MATCH_MP_TAC (theorem "sublist_ind") THEN SRW_TAC [][sublist_def] THEN
  METIS_TAC[]);


val sublist_filter = store_thm("sublist_filter",
  ``!l P. sublist (FILTER P l) l``,
  Induct THEN SRW_TAC [][sublist_def, sublist_cons]);


val sublist_cons_3 = save_thm("sublist_cons_3", sublist_CONS1_E);

val sublist_every = store_thm("sublist_every",
``!l1 l2 P. sublist l1 l2 /\ EVERY P l2 ==> EVERY P l1``,
METIS_TAC[EVERY_MEM, sublist_subset, pred_setTheory.SUBSET_DEF]);

val _ = export_theory()
