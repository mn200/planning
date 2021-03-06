(* fun cheat g = ACCEPT_TAC (mk_thm g) g *)

open HolKernel Parse boolLib bossLib;
open finite_mapTheory
open arithmeticTheory
open pred_setTheory
open sublistTheory

val _ = new_theory "FM_plan";
val _ = type_abbrev("state", ``:'a |->bool``)

val _ = Hol_datatype `problem = <|I:'a state;
      		     	          A:('a state# 'a state) set;
				  G:'a state |>`
val planning_problem_def = 
    Define`planning_problem( PROB)  = (!a. a IN PROB.A ==> (FDOM(SND (a)) ⊆ FDOM(PROB.I)) /\ (FDOM(FST (a)) ⊆ FDOM(PROB.I)) )  /\ (FDOM PROB.G = FDOM PROB.I)`;

val state_succ_def
 = Define`state_succ (s:'a state) a  =    if (FST a ⊑  s) then ( FUNION (SND a) s ) else s`;

val exec_plan_def = 
Define`(exec_plan(s, a::as) = exec_plan((state_succ s a ), as))
	 /\ (exec_plan(s, []) = s)`;

val plan_def = Define`(plan(  PROB, as) =
  (planning_problem(PROB)/\ (exec_plan(PROB.I, as) = PROB.G)) /\ ((set as) SUBSET PROB.A))`; 

val exec_plan_Append = store_thm("exec_plan_Append", 
  ``!as_a as_b s. exec_plan(s, as_a++as_b) = exec_plan(exec_plan(s,as_a),as_b)``,
	Induct_on `as_a` THEN1 FULL_SIMP_TAC (srw_ss()) [exec_plan_def]
 	THEN 
 	REPEAT STRIP_TAC
 	THEN
 	FULL_SIMP_TAC (srw_ss()) [exec_plan_def]
);

 val cycle_removal_lemma = 
store_thm("cycle_removal_lemma",
``!PROB as1 as2 as3. (plan( PROB,  (as1 ++ as2 ++ as3)))
 /\ (exec_plan(PROB.I,as1++as2) = exec_plan(PROB.I,as1)) /\ (as2 <> [])
 ==> (plan( PROB, (as1++as3))) ``,
 REPEAT STRIP_TAC 
 THEN ASSUME_TAC exec_plan_Append
THEN	SRW_TAC [][] 
	THEN
	Q_TAC SUFF_TAC `(planning_problem(PROB)/\ (exec_plan(PROB.I, as1++as2++as3) = PROB.G))`
	THENL
 	[
		REPEAT STRIP_TAC
 		THEN
		Q_TAC SUFF_TAC `(exec_plan(PROB.I, as1++as3) = PROB.G)`
		THENL
		[			
			REPEAT STRIP_TAC
			THEN
			FULL_SIMP_TAC(srw_ss())[plan_def]			
			,
			METIS_TAC[]
		]
		,
		FULL_SIMP_TAC (srw_ss()) []
		THEN
		METIS_TAC [plan_def,listTheory.APPEND]
		THEN
		METIS_TAC [plan_def]
 	]
); 







val general_theorem = store_thm("general_theorem",
  ``!P f l. (!p. P p /\ f p > l:num ==> ?p'. P p' /\ f p' < f p) ==>
    !p. P p ==> ?p'. P p' /\ f p' <= l``,
  NTAC 4 STRIP_TAC THEN
  Q_TAC SUFF_TAC `!n p. (n = f p) /\ P p ==> ?p'. P p' /\ f p' <= l` THEN1 METIS_TAC[] THEN
  HO_MATCH_MP_TAC arithmeticTheory.COMPLETE_INDUCTION THEN 
  REPEAT STRIP_TAC THEN 
  Cases_on `f p <= l` THENL [
    METIS_TAC[],
    `f p > l` by DECIDE_TAC THEN 
    `?p'. P p' /\ f p' < f p` by METIS_TAC[] THEN 
    Cases_on `f p' <= l` THEN1 METIS_TAC[] THEN
    METIS_TAC [DECIDE ``~(x:num <= y:num) <=> x > y``]
  ]);

val general_theorem' = store_thm("general_theorem'",
  ``!P f l prob. (!p. P( prob, p) /\ f p > l:num ==> ?p'. P( prob, p') /\ f p' < f p) ==>
    !p. P( prob, p) ==> ?p'. P( prob, p') /\ f p' <= l``,
  NTAC 5 STRIP_TAC THEN (* GEN_TAC THEN completeInduct_on `f p` THEN *)
  Q_TAC SUFF_TAC `!n p. (n = f p) /\ P( prob, p) ==> ?p'. P( prob,  p') /\ f p' <= l` THEN1 METIS_TAC[] THEN
  (* MATCH_MP_TAC 
    (arithmeticTheory.COMPLETE_INDUCTION 
    |> SPEC_ALL 
    |> INST [``P:num->bool`` |-> 
             ``\n:num. !p:'a. (n = f p) /\ P( prob, p) ==> ?p'. P( prob, p') /\ f p' <= l``]
    |> BETA_RULE) *)

  HO_MATCH_MP_TAC arithmeticTheory.COMPLETE_INDUCTION THEN 
  REPEAT STRIP_TAC THEN 
  Cases_on `f p <= l` THENL [
    METIS_TAC[],
    `f p > l` by DECIDE_TAC THEN 
    `?p'. P( prob, p') /\ f p' < f p` by METIS_TAC[] THEN 
    Cases_on `f p' <= l` THEN1 METIS_TAC[] THEN
    METIS_TAC [DECIDE ``~(x:num <= y:num) <=> x > y``]
  ]);
 
val construction_of_all_possible_states_lemma = store_thm(
"construction_of_all_possible_states_lemma",
``!e X. ( ~(e IN (X)))==>
 ({s:'a state | (FDOM s) = e INSERT X} = IMAGE (\s. s |+ (e,T)) {s:'a state | (FDOM s) = X} UNION
                                IMAGE (\s. s |+ (e,F)) {s:'a state | (FDOM s) = X})``,
     SRW_TAC [][Once pred_setTheory.EXTENSION]
     THEN SRW_TAC[][] 
     THEN EQ_TAC 
    	  THENL[
		SRW_TAC[][]
		THEN `FCARD (x) = CARD( e INSERT X)` by SRW_TAC[][CARD_DEF, FCARD_DEF] 
		THEN CONV_TAC(OR_EXISTS_CONV)
		THEN Cases_on`x ' e`	
		THENL
		[
			Q_TAC SUFF_TAC `x = ((x \\ e) |+ (e,T))` 
			THENL
			[
				REPEAT STRIP_TAC
				THEN `FDOM (x \\ e) = X ` by (SRW_TAC[][]
				     THEN FULL_SIMP_TAC(srw_ss())[INSERT_DEF,DELETE_DEF, EXTENSION]
				     THEN STRIP_TAC
				     THEN EQ_TAC
				     THEN METIS_TAC[])
				THEN METIS_TAC[]
				,
			     	SRW_TAC[][fmap_EXT] 
			     	THENL
				[
					EQ_TAC
			     	   	THEN1 FULL_SIMP_TAC(srw_ss()) [] 
				   	THEN FULL_SIMP_TAC(srw_ss()) [] 
					,
					EQ_TAC
					THENL
					[
						`~(x' = e) ` by (SRW_TAC[][]
						      	   THEN METIS_TAC[IN_DEF])
						THEN FULL_SIMP_TAC(srw_ss()) [FDOM_DEF, INSERT_DEF] 
						THEN METIS_TAC[DOMSUB_FAPPLY_NEQ, FUPDATE_PURGE, NOT_EQ_FAPPLY]
						,
						`~(x' = e) ` by (SRW_TAC[][]
						      	   THEN METIS_TAC[IN_DEF])
						THEN FULL_SIMP_TAC(srw_ss()) [FDOM_DEF, INSERT_DEF] 
						THEN METIS_TAC[DOMSUB_FAPPLY_NEQ, FUPDATE_PURGE, NOT_EQ_FAPPLY]
					]
				]
			]
			,
			Q_TAC SUFF_TAC `x = ((x \\ e) |+ (e,F))` 
			THENL
			[
				REPEAT STRIP_TAC
				THEN `FDOM (x \\ e) = X ` by (SRW_TAC[][]
				     THEN FULL_SIMP_TAC(srw_ss())[INSERT_DEF,DELETE_DEF, EXTENSION]
				     THEN STRIP_TAC
				     THEN EQ_TAC
				     THEN METIS_TAC[])
				THEN METIS_TAC[]
				,
			     	SRW_TAC[][fmap_EXT] 
			     	THENL
				[
					EQ_TAC
			     	   	THEN1 FULL_SIMP_TAC(srw_ss()) [] 
				   	THEN FULL_SIMP_TAC(srw_ss()) [] 
					,
					EQ_TAC
					THENL
					[
						`~(x' = e) ` by (SRW_TAC[][]
						      	   THEN METIS_TAC[IN_DEF])
						THEN FULL_SIMP_TAC(srw_ss()) [FDOM_DEF, INSERT_DEF] 
						THEN METIS_TAC[DOMSUB_FAPPLY_NEQ, FUPDATE_PURGE, NOT_EQ_FAPPLY]
						,
						`~(x' = e) ` by (SRW_TAC[][]
						      	   THEN METIS_TAC[IN_DEF])
						THEN FULL_SIMP_TAC(srw_ss()) [FDOM_DEF, INSERT_DEF] 
						THEN METIS_TAC[DOMSUB_FAPPLY_NEQ, FUPDATE_PURGE, NOT_EQ_FAPPLY]
					]
				]
			]
		]		
	       ,
	       SIMP_TAC (srw_ss()) [GSYM EXISTS_OR_THM] 
               THEN DISCH_THEN (Q.X_CHOOSE_THEN `s` ASSUME_TAC)
 	       THEN FULL_SIMP_TAC (srw_ss()) []              
]); 

val card_union' = store_thm("card_union'",
  ``FINITE s /\ FINITE t /\ DISJOINT s t ==> (CARD (s UNION t) = CARD s + CARD t)``,
  METIS_TAC [DISJOINT_DEF, CARD_EMPTY, arithmeticTheory.ADD_CLAUSES, CARD_UNION]);



val FINITE_states = store_thm("FINITE_states",
  ``!X. FINITE (X:'a set) ==> FINITE { s : 'a state | FDOM(s) = X}``, 
  Induct_on `FINITE`  THEN SRW_TAC [][GSPEC_EQ, FDOM_EQ_EMPTY] THEN 
  Q_TAC SUFF_TAC   `FINITE ((IMAGE (λ(s :α state). s |+ ((e :α),T)) {s | FDOM s = (X :α -> bool)}) UNION  (IMAGE (λ(s :α state). s |+ (e,F)) {s | FDOM s = X}))`
  THENL
  [
	REPEAT STRIP_TAC
	THEN METIS_TAC[construction_of_all_possible_states_lemma]
  ,
	 METIS_TAC[FINITELY_INJECTIVE_IMAGE_FINITE, FINITE_UNION, IMAGE_FINITE]
  ]);

val CARD_INJ_IMAGE_2 = store_thm(
  "CARD_INJ_IMAGE_2",
  ``!f s. FINITE s ==> (!x y. ((x IN s) /\ (y IN s)) ==> ((f x = f y) <=> (x = y))) ==>
          (CARD (IMAGE f s) = CARD s)``,
  REWRITE_TAC [GSYM AND_IMP_INTRO] THEN NTAC 2 STRIP_TAC THEN
  Q.ID_SPEC_TAC `s` THEN HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SRW_TAC [][] THEN METIS_TAC[]);

val card_of_set_of_all_possible_states = store_thm("card_of_set_of_all_possible_states",
    ``! X. FINITE X ==> (CARD { s:'a state | FDOM(s) = X } = 2 EXP (CARD X))``,
     HO_MATCH_MP_TAC pred_setTheory.FINITE_INDUCT THEN REPEAT STRIP_TAC THENL 
     [
	 FULL_SIMP_TAC(srw_ss())[GSPEC_EQ, FDOM_EQ_EMPTY]
         ,
     	 FULL_SIMP_TAC(srw_ss())[construction_of_all_possible_states_lemma, CARD_DEF, CARD_INSERT]
     	 (* THEN `{s | state s (e INSERT X)} = ( IMAGE (\s. TLit e INSERT s) { s | state s X } UNION
                                IMAGE (\s. FLit e INSERT s) { s | state s X })` by METIS_TAC[construction_of_all_possible_states_lemma] 
     	 THEN ASM_SIMP_TAC (srw_ss()) [] *)
	 THEN `DISJOINT (IMAGE (λ(s :α state). s |+ ((e :α),T)) {s | FDOM s = (X :α -> bool)}) (IMAGE (λ(s :α state). s |+ (e,F)) {s | FDOM s = X})`
            by( SRW_TAC [][DISJOINT_DEF, Once EXTENSION] THEN 
	        SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN 
		SRW_TAC[][] THEN 
		METIS_TAC[SAME_KEY_UPDATES_DIFFER])
         THEN SRW_TAC[][card_union', FINITE_states] 

      	 THEN Q.ISPEC_THEN `(λ(s:'a state). s |+ ((e :α),T))` 
             (Q.ISPEC_THEN `{ s:'a state | FDOM(s) = X}` (MP_TAC o SIMP_RULE (srw_ss()) [FINITE_states])) CARD_INJ_IMAGE_2
         THEN REPEAT STRIP_TAC 
      	 THEN `FINITE{s:'a state| FDOM(s) = X}` by METIS_TAC[FINITE_states]
      	 THEN `(∀x:'a state y:'a state. (FDOM(x) = X) /\ (FDOM(y) = X) ==>
              ((x|+ (e,T) = y|+(e,T)) ⇔ (x = y)))` by METIS_TAC[FUPD11_SAME_NEW_KEY]

      	 THEN `CARD (IMAGE (λ(s:'a state). s |+ ((e :α),T)) {s:'a state | FDOM(s) = X}) = CARD ( {s:'a state | FDOM(s) = X} ) ` by
      	      FULL_SIMP_TAC(srw_ss())[ FINITE_states, GSPECIFICATION,  CARD_INJ_IMAGE]


      	 THEN Q.ISPEC_THEN `(λ(s:'a state). s |+ ((e :α),F))` 
             (Q.ISPEC_THEN `{ s:'a state | FDOM(s) = X}` (MP_TAC o SIMP_RULE (srw_ss()) [FINITE_states])) CARD_INJ_IMAGE_2
         THEN REPEAT STRIP_TAC 
      	 THEN `FINITE{s:'a state| FDOM(s) = X}` by METIS_TAC[FINITE_states]
      	 THEN `(∀x:'a state y:'a state. (FDOM(x) = X) /\ (FDOM(y) = X) ==>
              ((x|+ (e,F) = y|+(e,F)) ⇔ (x = y)))` by METIS_TAC[FUPD11_SAME_NEW_KEY]

      	 THEN `CARD (IMAGE (λ(s:'a state). s |+ ((e :α),F)) {s:'a state | FDOM(s) = X}) = CARD ( {s:'a state | FDOM(s) = X} ) ` by
      	      FULL_SIMP_TAC(srw_ss())[ FINITE_states, GSPECIFICATION,  CARD_INJ_IMAGE]



      	 THEN ASM_SIMP_TAC (srw_ss()) [] 
      	 THEN `!x. 2**x + 2**x = 2**(SUC x)` by( FULL_SIMP_TAC(srw_ss())[EXP, MULT]
      	   	       	      	      	     THEN REPEAT STRIP_TAC
					     THEN Induct_on `x` THEN1 FULL_SIMP_TAC(srw_ss())[EXP, MULT, ADD]
					     THEN FULL_SIMP_TAC(srw_ss())[EXP, MULT, ADD]
					     THEN METIS_TAC[EQ_MULT_LCANCEL, ADD, LEFT_ADD_DISTRIB])
 	 THEN METIS_TAC[]
    ]
);



open listTheory;							 




val state_list_def = Define`(
((state_list( s:'a state,  a::as:(('a state# 'a state) list))) = s :: (state_list( (state_succ s a), as)) )

    /\ (state_list( s, NIL) = [])) `;

val empty_state_list_lemma = store_thm("empty_state_list_lemma",
``!as s. ([] = state_list (s,as)) <=> (as = [])``,
Induct_on`as`
THEN1 SRW_TAC[][state_list_def]
THEN SRW_TAC[][state_list_def]
);
val state_list_length_lemma = store_thm("state_list_length_lemma",
``!as s. LENGTH(as) = LENGTH(state_list(s,as))``,
Induct_on`as`
THEN1 SRW_TAC[][state_list_def]
THEN SRW_TAC[][state_list_def]
);

(* val state_set_def = Define`(
(s::ss) INSERT (state_set(ss)) )
/\ (state_set([]) = EMPTY)
)`;
*)

(* val state_set_finite_lemma = prove(``!as s. FINITE (state_set(state_list(s, as))) ``, SRW_TAC[][]) *)

val state_set_def = Define`
(state_set(s::ss) = [s] INSERT IMAGE (CONS s) (state_set ss)) /\
(state_set [] = {})
`

val state_set_thm = store_thm(
  "state_set_thm",
  ``!s1. s1 IN state_set s2 <=> s1 <<= s2 /\ s1 <> []``, 
  Induct_on `s2` THEN SRW_TAC [][state_set_def,rich_listTheory.IS_PREFIX_NIL] THEN 
  Cases_on `s1` THEN SRW_TAC [][] THEN Cases_on `t = []` THEN SRW_TAC [][]);



val state_set_finite = store_thm(
  "state_set_finite",
  ``!X. FINITE (state_set X)``,
  Induct_on `X` THEN SRW_TAC [][state_set_def])
val _ = export_rewrites ["state_set_finite"]



val LENGTH_state_set = store_thm(
  "LENGTH_state_set",
  ``!X e. e IN state_set X ==> LENGTH e <= LENGTH X``,
  Induct_on `X` THEN SRW_TAC[][state_set_def] THEN SRW_TAC[][] THEN RES_TAC THEN DECIDE_TAC);

val lemma_temp = store_thm("lemma_temp",
``!x PROB as h. plan(PROB,as) ==> x IN state_set (state_list (PROB.I,as)) ==> LENGTH((h::state_list (PROB.I,as))) > LENGTH(x)``,
SRW_TAC [][] THEN IMP_RES_TAC LENGTH_state_set THEN DECIDE_TAC);

val NIL_NOTIN_stateset = store_thm(
  "NIL_NOTIN_stateset",
  ``!X. [] NOTIN state_set X``,
  Induct_on `X` THEN SRW_TAC [][state_set_def]);
val _ = export_rewrites ["NIL_NOTIN_stateset"]

val state_set_card = store_thm(
  "state_set_card",
  ``!X. CARD (state_set X) = LENGTH X``,
  Induct_on `X` THEN SRW_TAC [][state_set_def] THEN 
  SRW_TAC [][CARD_INJ_IMAGE]);

(* val state_set_card = store_thm(
  "state_set_card",
  ``!X. CARD (state_set X) = LENGTH X``,
  Induct_on `X` THEN SRW_TAC [][state_set_def] THEN 
  `h::X NOTIN state_set X` 
    by (STRIP_TAC THEN IMP_RES_TAC LENGTH_state_set THEN FULL_SIMP_TAC (srw_ss()) [] THEN DECIDE_TAC) THEN
  SRW_TAC[][]);


val state_set_card_lemma = store_thm("state_set_card_lemma",
``!PROB as. plan(PROB,as)==>
    (CARD(state_set(state_list(PROB.I, as))) = LENGTH(state_list(PROB.I, as)))``,
SRW_TAC [][]) *)


val _ = export_rewrites ["state_set_card"]

val FDOM_state_succ = store_thm(
  "FDOM_state_succ",
  ``FDOM (SND a) SUBSET	FDOM s ==> (FDOM (state_succ s a) = FDOM s)``,
  SRW_TAC [][state_succ_def] THEN 
  SRW_TAC [][EXTENSION] THEN FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN METIS_TAC[]);

val lemma_1_1_1 = store_thm("lemma_1_1_1",
``! PROB. planning_problem PROB /\ (FDOM I' = FDOM PROB.I) ==> 
                                  planning_problem (PROB with I := I')``,
                  SRW_TAC [][planning_problem_def]);

val lemma_1_1 = store_thm("lemma_1_1",
				``! PROB as h. plan(PROB, h::as) ==> 
    	      		  plan(PROB with I := state_succ PROB.I h, as)``,
	        SRW_TAC[][plan_def] THENL
                [
			MATCH_MP_TAC lemma_1_1_1 THEN SRW_TAC[][] THEN 
			MATCH_MP_TAC FDOM_state_succ THEN 
			METIS_TAC [planning_problem_def],
			FULL_SIMP_TAC (srw_ss()) [exec_plan_def]
                ])

val plan_CONS = store_thm(
  "plan_CONS",
  ``plan (PROB, h::as) <=> 
      plan(PROB with I := state_succ PROB.I h, as) /\ h IN PROB.A /\
      planning_problem PROB``,
  SRW_TAC[][EQ_IMP_THM, lemma_1_1] THEN
  FULL_SIMP_TAC (srw_ss()) [plan_def, planning_problem_def, exec_plan_def]);
  

val IS_SUFFIX_MEM = store_thm(
  "IS_SUFFIX_MEM",
  ``IS_SUFFIX s (h::t) ==> MEM h s``,
  SRW_TAC [][rich_listTheory.IS_SUFFIX_APPEND] THEN SRW_TAC[][]);

val IS_PREFIX_MEM = store_thm(
  "IS_PREFIX_MEM",
  ``!y. x <<= y ==> !e. MEM e x ==> MEM e y``,
  Induct_on `x` THEN SRW_TAC [][] THEN Cases_on `y` THEN FULL_SIMP_TAC (srw_ss()) []);


val MEM_LAST' = store_thm(
  "MEM_LAST'",
  ``seq <> [] ==> MEM (LAST seq) seq``,
  Cases_on `seq` THEN SRW_TAC[][rich_listTheory.MEM_LAST]);

fun qispl_then [] ttac = ttac
  | qispl_then (q::qs) ttac = Q.ISPEC_THEN q (qispl_then qs ttac)

val MEM_statelist_FDOM = store_thm(
  "MEM_statelist_FDOM",
  ``!PROB h as s0. plan (PROB, as) /\ (FDOM s0 = FDOM PROB.I) /\ MEM h (state_list(s0, as)) ==> (FDOM h = FDOM PROB.I)``,
  Induct_on `as` THEN SRW_TAC[][state_list_def] THEN SRW_TAC[][] THEN 
  FULL_SIMP_TAC (srw_ss()) [plan_CONS] THEN 
  Q.MATCH_ASSUM_RENAME_TAC `MEM s X` ["X"] THEN 
  Q.MATCH_ASSUM_RENAME_TAC `a IN PROB.A` [] THEN 
  FIRST_X_ASSUM (Q.SPECL_THEN [`PROB with I := state_succ PROB.I a`, `s`, `state_succ s0 a`] MP_TAC) THEN 
  ASM_SIMP_TAC (srw_ss()) [] THEN 
  DISCH_THEN (fn th => SUBGOAL_THEN (lhand (concl th)) (ASSUME_TAC o MATCH_MP th)) THENL [
    `FDOM (SND a) SUBSET FDOM s0 /\ FDOM (SND a) SUBSET FDOM PROB.I`
      by FULL_SIMP_TAC (srw_ss()) [planning_problem_def] THEN 
    SRW_TAC[][FDOM_state_succ],
    SRW_TAC[][] THEN MATCH_MP_TAC FDOM_state_succ THEN 
    FULL_SIMP_TAC (srw_ss()) [planning_problem_def]
  ])


val lemma_1 = store_thm("lemma_1",
``! as PROB. plan( PROB,as) ==>
     ( (IMAGE LAST ( state_set ( state_list ( PROB.I, as ) ) )  ) SUBSET { s| (FDOM(s)) = (FDOM(PROB.I))}) ``,
     SIMP_TAC (srw_ss()) [SUBSET_DEF, state_set_thm] THEN 
     SRW_TAC[][] THEN 
     Cases_on `x'` THEN1 FULL_SIMP_TAC(srw_ss()) [] THEN 
     IMP_RES_TAC MEM_LAST' THEN 
     METIS_TAC[MEM_statelist_FDOM,IS_PREFIX_MEM, plan_def, planning_problem_def]);
(* val lemma_1 = store_thm("lemma_1",
``! as PROB. plan( PROB,as) ==>
     ( (IMAGE (LAST) ( state_set ( state_list ( PROB.I, as ) ) )  ) SUBSET { s| (FDOM(s)) = (FDOM(PROB.I))}) ``,
     SIMP_TAC (srw_ss()) [SUBSET_DEF, state_set_thm ] THEN 
     SRW_TAC[][] THEN 
     Cases_on `x'` THEN FULL_SIMP_TAC(srw_ss()) [] THEN 
     IMP_RES_TAC IS_SUFFIX_MEM THEN 
     METIS_TAC [MEM_statelist_FDOM]); *)


val lemma_2_1_1_1 = store_thm("lemma_2_1_1_1",
``! as x PROB. ~(as = []) /\ (plan (PROB,as) )  ==> x IN (state_set(state_list (PROB.I,as))) ==> (LENGTH(x)<= LENGTH(as))``,	    
  METIS_TAC [LENGTH_state_set,state_list_length_lemma ]);


val lemma_2_1_1_2 = store_thm("lemma_2_1_1_2",
``!l1 l2. (LENGTH(l1) >(LENGTH(l2))) ==> ~(l1 =l2)``,
REPEAT STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) []);


val lemma_2_1_1 = store_thm("lemma_2_1_1",
``! as PROB h. plan(PROB, h::as) ==> (CARD (state_set (state_list (PROB.I,h::as))) = SUC(CARD (state_set (state_list ((problem_I_fupd (K (state_succ PROB.I h)) PROB).I,as)))))``,
SRW_TAC [][GSYM state_list_length_lemma]);

val lemma_2_1 = store_thm("lemma_2_1",
``!as PROB. plan( PROB,as) ==> (LENGTH(as) = CARD(state_set(state_list(PROB.I,as))))``,
SRW_TAC [][GSYM state_list_length_lemma])

val LENGTH_INJ_PREFIXES = store_thm(
  "LENGTH_INJ_PREFIXES",
  ``!x1 x2. x1 <<= y /\ x2 <<= y ==> ((LENGTH x1 = LENGTH x2) <=> (x1 = x2))``,
  Induct_on `y` THEN SRW_TAC [][rich_listTheory.IS_PREFIX_NIL] THEN 
  Cases_on `x1` THEN Cases_on `x2` THEN FULL_SIMP_TAC (srw_ss()) []);

val lemma_2_2_1 = store_thm(
"lemma_2_2_1",
``!as x y PROB. plan (PROB,as) /\  
    		  	      x ∈ state_set (state_list (PROB.I,as)) 
			      /\ y ∈ state_set (state_list (PROB.I,as)) /\ ~(x = y) 
    		  	      ==>  ~(LENGTH(x) = LENGTH(y))``,
SRW_TAC [][state_set_thm] THEN METIS_TAC[LENGTH_INJ_PREFIXES]);

(* val lemma_2_2 = store_thm("lemma_2_2",
    ``!as PROB. plan(PROB, as) ==> ~(INJ LAST (state_set(state_list(PROB.I, as))) {s | FDOM(s) = FDOM(PROB.I)})
    	      	       ==> ?slist_1 slist_2.( (slist_1 IN state_set(state_list(PROB.I, as))) /\ (slist_2 IN state_set(state_list(PROB.I, as))) 
		       /\ ((LAST slist_1)=(LAST slist_2)) /\ ~((LENGTH(slist_1) = LENGTH(slist_2))))``,
SRW_TAC[][INJ_DEF,state_set_thm]		       
THENL 
[
   SRW_TAC[][],
   METIS_TAC[LENGTH_INJ_PREFIXES]
]) *)

val lemma_2_2 = store_thm("lemma_2_2",
    ``!as PROB. plan(PROB, as) ==> ~(INJ (LAST) (state_set(state_list(PROB.I, as))) {s | FDOM(s) = FDOM(PROB.I)})
    	      	       ==> ?slist_1 slist_2.( (slist_1 IN state_set(state_list(PROB.I, as))) /\ (slist_2 IN state_set(state_list(PROB.I, as))) 
		       /\ ((LAST slist_1)=(LAST slist_2)) /\ ~((LENGTH(slist_1) = LENGTH(slist_2))))``,
REWRITE_TAC[INJ_DEF]		       
THEN SRW_TAC[][]
THENL
[
	`!x. x ∈ state_set (state_list (PROB.I,as))  ==> LAST(x) IN {s | FDOM s = FDOM PROB.I}` by
	     (REWRITE_TAC[]
	     THEN FULL_SIMP_TAC(srw_ss())[lemma_1, GSPECIFICATION, SPECIFICATION, IMAGE_DEF]
	     THEN` ∀as PROB. plan (PROB,as) ⇒ IMAGE LAST (state_set (state_list (PROB.I,as))) ⊆ {s | FDOM s = FDOM PROB.I} ` by METIS_TAC[lemma_1]
	     THEN FULL_SIMP_TAC(srw_ss())[GSPECIFICATION, SPECIFICATION, IMAGE_DEF, GSPEC_ETA, SUBSET_DEF]
	     THEN METIS_TAC[GSPECIFICATION, SPECIFICATION, IMAGE_DEF, GSPEC_ETA, SUBSET_DEF])
	THEN  `FDOM(LAST x) = FDOM(PROB.I)` by( FULL_SIMP_TAC(srw_ss())[GSPECIFICATION, SPECIFICATION, IMAGE_DEF, GSPEC_ETA, SUBSET_DEF]    
	      THEN METIS_TAC[GSPECIFICATION, SPECIFICATION, IMAGE_DEF, GSPEC_ETA, SUBSET_DEF])
	,
	METIS_TAC[lemma_2_2_1]
  ]);



val lemma_2_3_1_1 = store_thm("lemma_2_3_1_1",
``!sl. [] NOTIN state_set(sl)``,
Induct_on`sl`
THEN1 SRW_TAC[][state_set_def]
THEN  SRW_TAC[][state_set_def]
); 


val lemma_2_3_1_2_1 = store_thm("lemma_2_3_1_2_1",
``! sl . sl <> [] ==> sl IN state_set(sl)``,
SRW_TAC [][state_set_thm])

(* val lemma_2_3_1_2_1 = store_thm("lemma_2_3_1_2_1",
``! sl . sl <> [] ==> sl IN state_set(sl)``,
Induct_on`sl`
THEN1 SRW_TAC[][state_set_def]	
THEN SRW_TAC[][state_set_def]
); *)


(* val lemma_2_3_1_2 = store_thm("lemma_2_3_1_2",
``!h sl  sl'. sl <> [] /\ h::sl IN state_set(sl') ==>
    		    	       	     	  sl IN state_set(sl')``,
	Induct_on`sl'`
	THEN1 METIS_TAC[state_set_def, NOT_IN_EMPTY]
	THEN SRW_TAC[][state_set_def]
	THENL
	[
		Cases_on`sl`
		THEN1 SRW_TAC[][state_set_def, lemma_2_3_1_1]
		THEN METIS_TAC[  lemma_2_3_1_2_1]		
		,
		METIS_TAC[]
	]
);  *)


val lemma_2_3_1_3_1 = store_thm("lemma_2_3_1_3_1",
``!PROB h as. plan(PROB,h::as) ==> (PROB.G  =  (PROB with I:=(state_succ PROB.I h)).G) ``,
SRW_TAC[][]);

(* val lemma_2_3_1_3 = store_thm("lemma_2_3_1_3",
``!PROB h as. plan(PROB,as) /\ h::[] IN state_set(state_list(PROB.I, as)) ==>
    		    	       	     	  (exec_plan( h, [LAST as]) = PROB.G)``,
Induct_on`as`
THEN1 SRW_TAC[][state_set_def, state_list_def]
THEN SRW_TAC[][state_set_def, state_list_def, exec_plan_def] 

THENL
[
	`as = []` by 
     	    (FULL_SIMP_TAC(srw_ss())[state_set_def, state_list_def, exec_plan_def]
     	THEN METIS_TAC[empty_state_list_lemma])
	THEN SRW_TAC[][]
	THEN FULL_SIMP_TAC(srw_ss())[state_set_def, state_list_def, exec_plan_def, plan_def] 	
	,
	FULL_SIMP_TAC(srw_ss())[state_set_def, state_list_def, exec_plan_def]
	THEN Cases_on`?x y. as = SNOC x y`
	THENL
	[
		FULL_SIMP_TAC(srw_ss())[LAST_CONS_cond]
		THEN `plan (PROB with I:= (state_succ PROB.I h),(y ++ [x]))` by METIS_TAC[lemma_1_1]
		THEN `[h'] ∈ state_set (state_list ((PROB with I:= (state_succ PROB.I h)).I ,y ++ [x]))` by
		     SRW_TAC[][]
		THEN UNDISCH_TAC ``∀PROB' h. plan (PROB',as) ∧ [h] ∈ state_set (state_list (PROB'.I,as)) ⇒ (state_succ h (LAST as) = PROB'.G)``
		THEN SRW_TAC[][]
		THEN METIS_TAC[lemma_2_3_1_3_1]
		,
		`as = []` by METIS_TAC[SNOC_CASES]
		THEN FULL_SIMP_TAC(srw_ss())[plan_def, exec_plan_def, state_set_def, state_list_def]
	]
] 
); *)


val lmma_2_3_1_4 = store_thm ("lemma_2_3_1_4",
``! l. l<>[] ==> FRONT l <<= l``,
Induct_on`l`
THEN1 SRW_TAC[][]
THEN SRW_TAC[][]
THEN Cases_on`l`
THEN1 SRW_TAC[][]
THEN SRW_TAC[][]
);


(* val lemma_2_3_1_5_1_1 = store_thm("lemma_2_3_1_5_1_1",
``!s0 s1 a:('a state # 'a state). ((state_succ s0 a) = (state_succ s1 a)) ==>
    		      		(s0 = s1)``,
SRW_TAC[][state_succ_def]
THEN `(((FDOM (SND a)) UNION (FDOM s0)) = ((FDOM (SND a)) UNION (FDOM s1)))` by METIS_TAC[FUNION_DEF]
THEN 
); 

val lemma_2_3_1_5_1 = prove(``!s0 s1 l. (exec_plan(s0,l) = exec_plan(s1,l)) ==> (s0 = s1)``,
Induct_on`l`
THEN1 SRW_TAC[][exec_plan_def]
THEN SRW_TAC[][exec_plan_def]
); 

val lemma_2_3_1_5 = prove(``! PROB l1 l2 s. plan(PROB, l1 ++ l2) /\  /\ (exec_plan (s,l2) = PROB.G)  ==>
    		    	      	      	   (exec_plan (PROB.I,l1) = s)``,
Induct_on`l1`
THENL
[
	Induct_on`l2`
	THEN1 FULL_SIMP_TAC(srw_ss())[exec_plan_def, plan_def, planning_problem_def]
	THEN SRW_TAC[][]plan_def, planning_problem_def, exec_plan_def, state_succ_def]
	THENL
	[
		`plan((PROB with I:= (state_succ PROB.I h)), l2)` by METIS_TAC[lemma_1_1]
		THEN ``
		`(SND h ⊌ s) = (SND h ⊌ PROB.I)` by METIS_TAC[plan_def, planning_problem_def, exec_plan_def, state_succ_def]
		FULL_SIMP_TAC(srw_ss()) [plan_def, planning_problem_def, exec_plan_def, state_succ_def]
		THEN SRW_TAC[][]
		THEN 
		,
		,
		,
	]
	THEN FULL_SIMP_TAC(srw_ss()) [planning_problem_def]
	THEN FULL_SIMP_TAC(srw_ss()) [exec_plan_def] 
	THEN `(SND h ⊌ s) = (SND h ⊌ i)` by SRW_TAC[][]
	THEN FULL_SIMP_TAC(srw_ss())[FUNION_DEF]
	,
	
 

); *)



val lemma_2_3_1_1 = prove(
``! h slist as. h::slist ∈ state_set (state_list (s,as)) ==> (h = s)``,
    Induct_on`as`
    THEN SRW_TAC[][state_list_def, state_set_def] 
);

val lemma_2_3_1_2 = store_thm("lemma_2_3_1_2",
``!s slist h t. slist <> [] /\ s::slist ∈ state_set (state_list (s,h::t)) ==> slist ∈ state_set (state_list (state_succ s h , t))``,
Induct_on`slist`
THEN SRW_TAC[][state_set_def, state_list_def, NIL_NOTIN_stateset, state_succ_def]
);



val lemma_2_3_1 = store_thm("lemma_2_3_1_thm",
``!slist as PROB. as <> [] /\ slist <> [] /\plan(PROB,as) ==>  slist IN state_set (state_list (PROB.I,as)) 
	 ==> ?as'.  (as' <<= as) /\ (exec_plan(PROB.I,as') = LAST slist) /\ ( (LENGTH slist) = SUC (LENGTH as') )``,
Induct_on`slist`
THEN1 FULL_SIMP_TAC(srw_ss())[state_set_def, state_list_def]
THEN SRW_TAC[][]
THEN `PROB.I::slist ∈ state_set (state_list (PROB.I,as))` by METIS_TAC[lemma_2_3_1_1]
THEN Cases_on`as`
THEN1 SRW_TAC[][]
THEN `plan((PROB with I := (state_succ PROB.I h')), t) ` by METIS_TAC[lemma_1_1]
THEN Cases_on`slist`

THENL
[
	Q.EXISTS_TAC `[]`
	THEN SRW_TAC[][lemma_2_3_1_1, exec_plan_def, state_succ_def]
	THEN METIS_TAC[lemma_2_3_1_1]
	,
	`h''::t' ∈ state_set (state_list ( (PROB with I := state_succ PROB.I h').I,t))` by SRW_TAC[][lemma_2_3_1_2]
	THEN Cases_on`t`
	THENL
	[
		FULL_SIMP_TAC(srw_ss())[plan_def, planning_problem_def, exec_plan_def, state_set_def, state_list_def]
		,
		Q.REFINE_EXISTS_TAC `h'::as''`
		THEN SRW_TAC[][exec_plan_def]
		THEN FIRST_X_ASSUM (Q.SPECL_THEN [`h'''::t''`, `PROB with I:= state_succ PROB.I h'`] MP_TAC) 
		THEN SRW_TAC[][]
	]
	
])



open rich_listTheory;

val lemma_2_3_2_1 = store_thm("lemma_2_3_2_1",
``!l. LENGTH l >= 0``,
Induct_on`l`
THEN SRW_TAC[][]
);

val  lemma_2_3_2 = store_thm("lemma_2_3_2",
``! l l1 l2. (* l<> [] /\ l2 <> []  /\ *) (LENGTH(l2) > LENGTH(l1)) /\ (l1 <<= l) /\ (l2 <<= l) ==> (l1 <<= l2)``,

Induct_on`l2`
THEN1 SRW_TAC[ARITH_ss][]
THEN Induct_on`l1`
THEN SRW_TAC[][]
THENL
[
	Cases_on`l`	
	THEN SRW_TAC[][]
	THEN FULL_SIMP_TAC(srw_ss()) []
	,
	Cases_on`l`	
	THEN FULL_SIMP_TAC(srw_ss()) []
	THEN `LENGTH(l2)>LENGTH(l1)` by METIS_TAC[LESS_MONO_REV, GREATER_DEF]	
	THEN Cases_on`t`
	THEN1 METIS_TAC[IS_PREFIX_NIL]
	THEN `(l2  <> [])` by 
	     (SRW_TAC[][]
	     THEN `LENGTH l1 >= 0` by METIS_TAC [lemma_2_3_2_1]
	     THEN `LENGTH l2 > 0` by DECIDE_TAC
	     THEN METIS_TAC[LENGTH_NOT_NULL, NULL_DEF, GREATER_DEF])
        THEN `h'''::t' <> []` by SRW_TAC[][]
	THEN METIS_TAC[]
]);


(* val list_diff_def = Define`(list_diff( h1::t1, h2::t2) = if (h1::t1 <<= h2::t2) then (list_diff( t1,  t2) ) else [])
    		         /\ (list_diff( [], l) = l) /\ (list_diff(l , []) = [])`;

val lemma_2_3_3 = store_thm("lemma_2_3_3",
`` !l1 l. (l1 <<= l) /\ (l <> []) ==> (l = l1++ (list_diff(l1,l)))``,
Induct_on`l1`
THEN SRW_TAC[][list_diff_def]
THEN Cases_on`l`
THEN SRW_TAC[][list_diff_def]
THENL
[
	Cases_on`t`
	THENL
	[
		SRW_TAC[][IS_PREFIX_NIL]
		THEN METIS_TAC[list_diff_def, IS_PREFIX_NIL]	
		,
		`h'::t' <> []` by SRW_TAC[][]
		THEN METIS_TAC[]
	]
	,
	FULL_SIMP_TAC(srw_ss())[]
	,
]
); *)



val lemma_2_3 = prove(``!as PROB slist_1 slist_2. as <> [] /\ plan(PROB, as) /\ (slist_1 <> []) /\ (slist_2 <> []) /\
    	      ( (slist_1 IN state_set(state_list(PROB.I, as))) /\ 
	      (slist_2 IN state_set(state_list(PROB.I, as))) /\
	       ~(LENGTH slist_1 = LENGTH slist_2) /\ ((LAST slist_1)=(LAST slist_2)))
    	      	      ==> ?as1 as2 as3. (as1++as2++as3 = as) /\ (exec_plan(PROB.I,as1++as2) = exec_plan(PROB.I,as1)) /\  ~(as2=[])``,
SRW_TAC[][]
THEN `?as_1.  (as_1 <<= as) /\ (exec_plan(PROB.I,as_1) = LAST slist_1) /\ ((LENGTH slist_1) = SUC (LENGTH as_1))` by METIS_TAC[ lemma_2_3_1]
THEN `?as_2.  (as_2 <<= as) /\ (exec_plan(PROB.I,as_2) = LAST slist_2) /\ ((LENGTH slist_2) = SUC (LENGTH as_2))` by METIS_TAC[ lemma_2_3_1]
THEN `(LENGTH as_1) <> (LENGTH as_2)` by DECIDE_TAC
THEN `((LENGTH as_1) < (LENGTH as_2)) \/ ((LENGTH as_1) > (LENGTH as_2))` by DECIDE_TAC
THENL
[
	`as_1<<=as_2` by METIS_TAC[lemma_2_3_2, GREATER_DEF]
	THEN `?a. as_2 = as_1 ++ a` by METIS_TAC[IS_PREFIX_APPEND]
	THEN `?b. as = as_2 ++b` by METIS_TAC[IS_PREFIX_APPEND]
	THEN Cases_on`a`
	THEN1 FULL_SIMP_TAC(srw_ss())[]
	THEN Q.EXISTS_TAC `as_1`
	THEN Q.EXISTS_TAC `h::t`
	THEN Q.EXISTS_TAC `b`
	THEN SRW_TAC[][]
	,
	`as_2<<=as_1` by METIS_TAC[lemma_2_3_2, GREATER_DEF]
	THEN `?a. as_1 = as_2 ++ a` by METIS_TAC[IS_PREFIX_APPEND]
	THEN `?b. as = as_1 ++b` by METIS_TAC[IS_PREFIX_APPEND]
	THEN Cases_on`a`
	THEN1 FULL_SIMP_TAC(srw_ss())[]
	THEN Q.EXISTS_TAC `as_2`
	THEN Q.EXISTS_TAC `h::t`
	THEN Q.EXISTS_TAC `b`
	THEN SRW_TAC[][]
]);



val lemma_2 = store_thm("lemma_2",
``!PROB as:(α state # α state) list. plan(PROB,as) ==> (LENGTH(as)) > (2** (CARD (FDOM (PROB.I))))
 ==> ?as1 as2 as3. (as1++as2++as3 = as) /\ (exec_plan(PROB.I,as1++as2) = exec_plan(PROB.I,as1)) /\  ~(as2=[])``,
SRW_TAC[][]
THEN `(CARD(state_set (state_list (PROB.I,as)))) > (2 ** CARD (FDOM PROB.I)) ` by METIS_TAC[lemma_2_1]
THEN `~INJ (LAST) (state_set (state_list (PROB.I,as))) ({s:'a state | FDOM(s) = FDOM(PROB.I)}) ` by 
     	   (SRW_TAC[][PHP,card_of_set_of_all_possible_states, FINITE_states, plan_def, planning_problem_def]
	   THEN `FINITE (FDOM PROB.I)` by SRW_TAC[][]
	   THEN ASSUME_TAC(Q.SPEC `(FDOM PROB.I)` card_of_set_of_all_possible_states)
	   THEN `(CARD {s:'a state | FDOM s = FDOM PROB.I} = 2 ** CARD (FDOM PROB.I))` by SRW_TAC[][]
	   THEN `CARD (state_set (state_list (PROB.I,as))) > CARD({s:'a state | FDOM(s) = FDOM(PROB.I)})` by METIS_TAC[card_of_set_of_all_possible_states]
	   THEN ASSUME_TAC(Q.ISPEC`({s:'a state | FDOM(s) = FDOM(PROB.I)})`
	                  (Q.ISPEC `(state_set (state_list (PROB.I,as:(α state # α state) list)))` 
			  (Q.ISPEC `LAST` PHP)))
           THEN FULL_SIMP_TAC(srw_ss())[GSYM GREATER_DEF]
	   THEN SRW_TAC[][]
	   THEN FULL_SIMP_TAC(srw_ss())[FINITE_states])
THEN `∃slist_1 slist_2.
       slist_1 ∈ state_set (state_list (PROB.I,as)) ∧
       slist_2 ∈ state_set (state_list (PROB.I,as)) ∧
       (LAST slist_1 = LAST slist_2) ∧ LENGTH slist_1 ≠ LENGTH slist_2` by METIS_TAC[lemma_2_2]
THEN Cases_on`as` 
THENL
[
	FULL_SIMP_TAC(srw_ss())[]
	THEN Cases_on`(FDOM PROB.I)`
	THEN1 FULL_SIMP_TAC(srw_ss())[]
	THEN DECIDE_TAC
	,
	`h::t <> []` by SRW_TAC[][lemma_2_3]
	THEN METIS_TAC[lemma_2_3, state_set_thm]
]);


val lemma_3_1  = store_thm("lemma_3_1",
``!l1 l2 l3. (l2 <> []) ==> LENGTH(l1++l3) <LENGTH(l1++l2++l3)``,
Induct_on`l2`
THEN SRW_TAC[][]
);
val lemma_3 = store_thm("lemma_3",
``!as PROB. plan(PROB,as) /\ ((LENGTH(as)) > (2** (CARD (FDOM (PROB.I))))) ==>
      ?as'. plan(PROB,as') /\ (LENGTH(as')<LENGTH(as))``,
SRW_TAC[][]
THEN `?as1 as2 as3. (as1++as2++as3 = as) /\ (exec_plan(PROB.I,as1++as2) = exec_plan(PROB.I,as1)) /\  ~(as2=[])` by METIS_TAC[lemma_2]
THEN ` plan (PROB,as1 ++ as3)` by METIS_TAC[cycle_removal_lemma]
THEN METIS_TAC[lemma_3_1]
);



val lemma_3 = store_thm("lemma_3",
``!as PROB. plan(PROB,as) /\ ((LENGTH(as)) > (2** (CARD (FDOM (PROB.I))))) ==>
      ?as'. plan(PROB,as') /\ (LENGTH(as')<LENGTH(as)) /\ sublist as' as``,
SRW_TAC[][]
THEN `?as1 as2 as3. (as1++as2++as3 = as) /\ (exec_plan(PROB.I,as1++as2) = exec_plan(PROB.I,as1)) /\  ~(as2=[])` by METIS_TAC[lemma_2]
THEN ` plan (PROB,as1 ++ as3)` by METIS_TAC[cycle_removal_lemma]
THEN Q.EXISTS_TAC `as1 ++ as3`
THEN METIS_TAC[lemma_3_1, append_sublist, sublist_refl]
);

val main_lemma = store_thm("main_lemma",
``!PROB as. plan(PROB, as:(α state # α state) list)
	 ==> ?as'. plan(PROB,as')  /\ sublist as' as  /\ (LENGTH(as') <=  (2** (CARD (FDOM (PROB.I)))))``,
SRW_TAC[][]
THEN Cases_on`(LENGTH(as) <=  (2** (CARD (FDOM (PROB.I)))))`
THENL
[
	 Q.EXISTS_TAC `as`
	 THEN METIS_TAC[sublist_refl]
	,
	`(LENGTH as > 2 ** CARD (FDOM PROB.I))` by DECIDE_TAC
	THEN ASSUME_TAC(Q.SPEC `as` (sublist_refl |> INST_TYPE [alpha |-> ``:('a state # 'a state )``]))
	THEN MP_TAC (general_theorem
		|> Q.ISPEC `(\as''. plan(PROB, as'') /\ sublist as'' as)` 
		|> Q.SPEC `LENGTH`
		|> Q.SPEC `(2** (CARD (FDOM (PROB.I))))`)
	THEN SRW_TAC[][]
	THEN Q.PAT_ASSUM `a ⇒ 
	     		     ∀p.
			        plan (PROB,p) ∧ b ⇒
				 ∃p'.(plan (PROB,p') ∧ c) ∧ LENGTH p' ≤ 2 ** CARD (FDOM PROB.I)` 
				 (MATCH_MP_TAC o REWRITE_RULE[GSYM CONJ_ASSOC] o Q.SPEC `as` o REWRITE_RULE[AND_IMP_INTRO] o (CONV_RULE RIGHT_IMP_FORALL_CONV)) 
	THEN SRW_TAC[SatisfySimps.SATISFY_ss][]
	THEN METIS_TAC[sublist_trans, lemma_3]
]);
val _ = export_theory();

