

open HolKernel Parse boolLib bossLib;

val _ = new_theory "GraphPlanTheorem";
open HolKernel Parse boolLib bossLib;
open finite_mapTheory
open arithmeticTheory
open pred_setTheory
open FM_planTheory
open rich_listTheory
open listTheory;							 





(* (* fun cheat g = ACCEPT_TAC (mk_thm g) g *)

open HolKernel Parse boolLib bossLib;
open finite_mapTheory
open arithmeticTheory
open pred_setTheory

val _ = new_theory "FM_plan";
val _ = type_abbrev("state", ``:'a |->bool``)

val _ = Hol_datatype `problem = <|I:'a state;
      		     	          A:('a state# 'a state) set;
				  G:'a state |>`
val planning_problem_def = 
    Define`planning_problem( PROB)  = (!a. a IN PROB.A ==> (FDOM(SND (a)) ⊆ FDOM(PROB.I))) /\ (FDOM PROB.G = FDOM PROB.I)`;

val state_succ_2_def
 = Define`state_succ_2 (s:'a state) a  =    if (FST a ⊑  s) then ( FUNION (SND a) s ) else s`;

val exec_plan_def = 
Define`(exec_plan(s, a::as) = exec_plan((state_succ_2 s a ), as))
	 /\ (exec_plan(s, []) = s)`;

val plan_def_2 = Define`(plan_2(  PROB, as) =
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
``!PROB as1 as2 as3. (plan_2( PROB,  (as1 ++ as2 ++ as3)))
 /\ (exec_plan(PROB.I,as1++as2) = exec_plan(PROB.I,as1)) /\ (as2 <> [])
 ==> (plan_2( PROB, (as1++as3))) ``,
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
			FULL_SIMP_TAC(srw_ss())[plan_def_2]			
			,
			METIS_TAC[]
		]
		,
		FULL_SIMP_TAC (srw_ss()) []
		THEN
		METIS_TAC [plan_def_2,listTheory.APPEND]
		THEN
		METIS_TAC [plan_def_2]
 	]
); 







val general_theorem = store_thm("general_theorem",
  ``!P f l. (!p. P p /\ f p > l:num ==> ?p'. P p' /\ f p' < f p) ==>
    !p. P p ==> ?p'. P p' /\ f p' <= l``,
  NTAC 4 STRIP_TAC THEN (* GEN_TAC THEN completeInduct_on `f p` THEN *)
  Q_TAC SUFF_TAC `!n p. (n = f p) /\ P p ==> ?p'. P p' /\ f p' <= l` THEN1 METIS_TAC[] THEN
  (* MATCH_MP_TAC 
    (arithmeticTheory.COMPLETE_INDUCTION 
    |> SPEC_ALL 
    |> INST [``P:num->bool`` |-> 
             ``\n:num. !p:'a. (n = f p) /\ P p ==> ?p'. P p' /\ f p' <= l``]
    |> BETA_RULE) *)

  HO_MATCH_MP_TAC arithmeticTheory.COMPLETE_INDUCTION THEN 
  REPEAT STRIP_TAC THEN 
  Cases_on `f p <= l` THENL [
    METIS_TAC[],
    `f p > l` by DECIDE_TAC THEN 
    `?p'. P p' /\ f p' < f p` by METIS_TAC[] THEN 
    Cases_on `f p' <= l` THEN1 METIS_TAC[] THEN
    METIS_TAC [DECIDE ``~(x:num <= y:num) <=> x > y``]
  ]);

val general_theorem' = store_thm("general_theorem",
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
((state_list( s:'a state,  a::as:(('a state# 'a state) list))) = s :: (state_list( (state_succ_2 s a), as)) )

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
``!x PROB as h. plan_2(PROB,as) ==> x IN state_set (state_list (PROB.I,as)) ==> LENGTH((h::state_list (PROB.I,as))) > LENGTH(x)``,
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
``!PROB as. plan_2(PROB,as)==>
    (CARD(state_set(state_list(PROB.I, as))) = LENGTH(state_list(PROB.I, as)))``,
SRW_TAC [][]) *)


val _ = export_rewrites ["state_set_card"]

val FDOM_state_succ = store_thm(
  "FDOM_state_succ",
  ``FDOM (SND a) SUBSET	FDOM s ==> (FDOM (state_succ_2 s a) = FDOM s)``,
  SRW_TAC [][state_succ_2_def] THEN 
  SRW_TAC [][EXTENSION] THEN FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN METIS_TAC[]);

val lemma_1_1_1 = store_thm("lemma_1_1_1",
``! PROB. planning_problem PROB /\ (FDOM I' = FDOM PROB.I) ==> 
                                  planning_problem (PROB with I := I')``,
                  SRW_TAC [][planning_problem_def]);

val lemma_1_1 = store_thm("lemma_1_1",
				``! PROB as h. plan_2(PROB, h::as) ==> 
    	      		  plan_2(PROB with I := state_succ_2 PROB.I h, as)``,
	        SRW_TAC[][plan_def_2] THENL
                [
			MATCH_MP_TAC lemma_1_1_1 THEN SRW_TAC[][] THEN 
			MATCH_MP_TAC FDOM_state_succ THEN 
			METIS_TAC [planning_problem_def],
			FULL_SIMP_TAC (srw_ss()) [exec_plan_def]
                ])

val plan_CONS = store_thm(
  "plan_CONS",
  ``plan_2 (PROB, h::as) <=> 
      plan_2(PROB with I := state_succ_2 PROB.I h, as) /\ h IN PROB.A /\
      planning_problem PROB``,
  SRW_TAC[][EQ_IMP_THM, lemma_1_1] THEN
  FULL_SIMP_TAC (srw_ss()) [plan_def_2, planning_problem_def, exec_plan_def]);
  

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
  ``!PROB h as s0. plan_2 (PROB, as) /\ (FDOM s0 = FDOM PROB.I) /\ MEM h (state_list(s0, as)) ==> (FDOM h = FDOM PROB.I)``,
  Induct_on `as` THEN SRW_TAC[][state_list_def] THEN SRW_TAC[][] THEN 
  FULL_SIMP_TAC (srw_ss()) [plan_CONS] THEN 
  Q.MATCH_ASSUM_RENAME_TAC `MEM s X` ["X"] THEN 
  Q.MATCH_ASSUM_RENAME_TAC `a IN PROB.A` [] THEN 
  FIRST_X_ASSUM (Q.SPECL_THEN [`PROB with I := state_succ_2 PROB.I a`, `s`, `state_succ_2 s0 a`] MP_TAC) THEN 
  ASM_SIMP_TAC (srw_ss()) [] THEN 
  DISCH_THEN (fn th => SUBGOAL_THEN (lhand (concl th)) (ASSUME_TAC o MATCH_MP th)) THENL [
    `FDOM (SND a) SUBSET FDOM s0 /\ FDOM (SND a) SUBSET FDOM PROB.I`
      by FULL_SIMP_TAC (srw_ss()) [planning_problem_def] THEN 
    SRW_TAC[][FDOM_state_succ],
    SRW_TAC[][] THEN MATCH_MP_TAC FDOM_state_succ THEN 
    FULL_SIMP_TAC (srw_ss()) [planning_problem_def]
  ])


val lemma_1 = store_thm("lemma_1",
``! as PROB. plan_2( PROB,as) ==>
     ( (IMAGE LAST ( state_set ( state_list ( PROB.I, as ) ) )  ) SUBSET { s| (FDOM(s)) = (FDOM(PROB.I))}) ``,
     SIMP_TAC (srw_ss()) [SUBSET_DEF, state_set_thm] THEN 
     SRW_TAC[][] THEN 
     Cases_on `x'` THEN1 FULL_SIMP_TAC(srw_ss()) [] THEN 
     IMP_RES_TAC MEM_LAST' THEN 
     METIS_TAC[MEM_statelist_FDOM,IS_PREFIX_MEM, plan_def_2, planning_problem_def]);
(* val lemma_1 = store_thm("lemma_1",
``! as PROB. plan_2( PROB,as) ==>
     ( (IMAGE (LAST) ( state_set ( state_list ( PROB.I, as ) ) )  ) SUBSET { s| (FDOM(s)) = (FDOM(PROB.I))}) ``,
     SIMP_TAC (srw_ss()) [SUBSET_DEF, state_set_thm ] THEN 
     SRW_TAC[][] THEN 
     Cases_on `x'` THEN FULL_SIMP_TAC(srw_ss()) [] THEN 
     IMP_RES_TAC IS_SUFFIX_MEM THEN 
     METIS_TAC [MEM_statelist_FDOM]); *)


val lemma_2_1_1_1 = store_thm("lemma_2_1_1_1",
``! as x PROB. ~(as = []) /\ (plan_2 (PROB,as) )  ==> x IN (state_set(state_list (PROB.I,as))) ==> (LENGTH(x)<= LENGTH(as))``,	    
  METIS_TAC [LENGTH_state_set,state_list_length_lemma ]);


val lemma_2_1_1_2 = store_thm("lemma_2_1_1_2",
``!l1 l2. (LENGTH(l1) >(LENGTH(l2))) ==> ~(l1 =l2)``,
REPEAT STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) []);


val lemma_2_1_1 = store_thm("lemma_2_1_1",
``! as PROB h. plan_2(PROB, h::as) ==> (CARD (state_set (state_list (PROB.I,h::as))) = SUC(CARD (state_set (state_list ((problem_I_fupd (K (state_succ_2 PROB.I h)) PROB).I,as)))))``,
SRW_TAC [][GSYM state_list_length_lemma]);

val lemma_2_1 = store_thm("lemma_2_1",
``!as PROB. plan_2( PROB,as) ==> (LENGTH(as) = CARD(state_set(state_list(PROB.I,as))))``,
SRW_TAC [][GSYM state_list_length_lemma])

val LENGTH_INJ_PREFIXES = store_thm(
  "LENGTH_INJ_PREFIXES",
  ``!x1 x2. x1 <<= y /\ x2 <<= y ==> ((LENGTH x1 = LENGTH x2) <=> (x1 = x2))``,
  Induct_on `y` THEN SRW_TAC [][rich_listTheory.IS_PREFIX_NIL] THEN 
  Cases_on `x1` THEN Cases_on `x2` THEN FULL_SIMP_TAC (srw_ss()) []);

val lemma_2_2_1 = store_thm(
"lemma_2_2_1",
``!as x y PROB. plan_2 (PROB,as) /\  
    		  	      x ∈ state_set (state_list (PROB.I,as)) 
			      /\ y ∈ state_set (state_list (PROB.I,as)) /\ ~(x = y) 
    		  	      ==>  ~(LENGTH(x) = LENGTH(y))``,
SRW_TAC [][state_set_thm] THEN METIS_TAC[LENGTH_INJ_PREFIXES]);

(* val lemma_2_2 = store_thm("lemma_2_2",
    ``!as PROB. plan_2(PROB, as) ==> ~(INJ LAST (state_set(state_list(PROB.I, as))) {s | FDOM(s) = FDOM(PROB.I)})
    	      	       ==> ?slist_1 slist_2.( (slist_1 IN state_set(state_list(PROB.I, as))) /\ (slist_2 IN state_set(state_list(PROB.I, as))) 
		       /\ ((LAST slist_1)=(LAST slist_2)) /\ ~((LENGTH(slist_1) = LENGTH(slist_2))))``,
SRW_TAC[][INJ_DEF,state_set_thm]		       
THENL 
[
   SRW_TAC[][],
   METIS_TAC[LENGTH_INJ_PREFIXES]
]) *)

val lemma_2_2 = store_thm("lemma_2_2",
    ``!as PROB. plan_2(PROB, as) ==> ~(INJ (LAST) (state_set(state_list(PROB.I, as))) {s | FDOM(s) = FDOM(PROB.I)})
    	      	       ==> ?slist_1 slist_2.( (slist_1 IN state_set(state_list(PROB.I, as))) /\ (slist_2 IN state_set(state_list(PROB.I, as))) 
		       /\ ((LAST slist_1)=(LAST slist_2)) /\ ~((LENGTH(slist_1) = LENGTH(slist_2))))``,
REWRITE_TAC[INJ_DEF]		       
THEN SRW_TAC[][]
THENL
[
	`!x. x ∈ state_set (state_list (PROB.I,as))  ==> LAST(x) IN {s | FDOM s = FDOM PROB.I}` by
	     (REWRITE_TAC[]
	     THEN FULL_SIMP_TAC(srw_ss())[lemma_1, GSPECIFICATION, SPECIFICATION, IMAGE_DEF]
	     THEN` ∀as PROB. plan_2 (PROB,as) ⇒ IMAGE LAST (state_set (state_list (PROB.I,as))) ⊆ {s | FDOM s = FDOM PROB.I} ` by METIS_TAC[lemma_1]
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
``!PROB h as. plan_2(PROB,h::as) ==> (PROB.G  =  (PROB with I:=(state_succ_2 PROB.I h)).G) ``,
SRW_TAC[][]);

(* val lemma_2_3_1_3 = store_thm("lemma_2_3_1_3",
``!PROB h as. plan_2(PROB,as) /\ h::[] IN state_set(state_list(PROB.I, as)) ==>
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
	THEN FULL_SIMP_TAC(srw_ss())[state_set_def, state_list_def, exec_plan_def, plan_def_2] 	
	,
	FULL_SIMP_TAC(srw_ss())[state_set_def, state_list_def, exec_plan_def]
	THEN Cases_on`?x y. as = SNOC x y`
	THENL
	[
		FULL_SIMP_TAC(srw_ss())[LAST_CONS_cond]
		THEN `plan_2 (PROB with I:= (state_succ_2 PROB.I h),(y ++ [x]))` by METIS_TAC[lemma_1_1]
		THEN `[h'] ∈ state_set (state_list ((PROB with I:= (state_succ_2 PROB.I h)).I ,y ++ [x]))` by
		     SRW_TAC[][]
		THEN UNDISCH_TAC ``∀PROB' h. plan_2 (PROB',as) ∧ [h] ∈ state_set (state_list (PROB'.I,as)) ⇒ (state_succ_2 h (LAST as) = PROB'.G)``
		THEN SRW_TAC[][]
		THEN METIS_TAC[lemma_2_3_1_3_1]
		,
		`as = []` by METIS_TAC[SNOC_CASES]
		THEN FULL_SIMP_TAC(srw_ss())[plan_def_2, exec_plan_def, state_set_def, state_list_def]
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
``!s0 s1 a:('a state # 'a state). ((state_succ_2 s0 a) = (state_succ_2 s1 a)) ==>
    		      		(s0 = s1)``,
SRW_TAC[][state_succ_2_def]
THEN `(((FDOM (SND a)) UNION (FDOM s0)) = ((FDOM (SND a)) UNION (FDOM s1)))` by METIS_TAC[FUNION_DEF]
THEN 
); 

val lemma_2_3_1_5_1 = prove(``!s0 s1 l. (exec_plan(s0,l) = exec_plan(s1,l)) ==> (s0 = s1)``,
Induct_on`l`
THEN1 SRW_TAC[][exec_plan_def]
THEN SRW_TAC[][exec_plan_def]
); 

val lemma_2_3_1_5 = prove(``! PROB l1 l2 s. plan_2(PROB, l1 ++ l2) /\  /\ (exec_plan (s,l2) = PROB.G)  ==>
    		    	      	      	   (exec_plan (PROB.I,l1) = s)``,
Induct_on`l1`
THENL
[
	Induct_on`l2`
	THEN1 FULL_SIMP_TAC(srw_ss())[exec_plan_def, plan_def_2, planning_problem_def]
	THEN SRW_TAC[][]plan_def_2, planning_problem_def, exec_plan_def, state_succ_2_def]
	THENL
	[
		`plan_2((PROB with I:= (state_succ_2 PROB.I h)), l2)` by METIS_TAC[lemma_1_1]
		THEN ``
		`(SND h ⊌ s) = (SND h ⊌ PROB.I)` by METIS_TAC[plan_def_2, planning_problem_def, exec_plan_def, state_succ_2_def]
		FULL_SIMP_TAC(srw_ss()) [plan_def_2, planning_problem_def, exec_plan_def, state_succ_2_def]
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
``!s slist h t. slist <> [] /\ s::slist ∈ state_set (state_list (s,h::t)) ==> slist ∈ state_set (state_list (state_succ_2 s h , t))``,
Induct_on`slist`
THEN SRW_TAC[][state_set_def, state_list_def, NIL_NOTIN_stateset, state_succ_2_def]
);



val lemma_2_3_1 = store_thm("lemma_2_3_1_thm",
``!slist as PROB. as <> [] /\ slist <> [] /\plan_2(PROB,as) ==>  slist IN state_set (state_list (PROB.I,as)) 
	 ==> ?as'.  (as' <<= as) /\ (exec_plan(PROB.I,as') = LAST slist) /\ ( (LENGTH slist) = SUC (LENGTH as') )``,
Induct_on`slist`
THEN1 FULL_SIMP_TAC(srw_ss())[state_set_def, state_list_def]
THEN SRW_TAC[][]
THEN `PROB.I::slist ∈ state_set (state_list (PROB.I,as))` by METIS_TAC[lemma_2_3_1_1]
THEN Cases_on`as`
THEN1 SRW_TAC[][]
THEN `plan_2((PROB with I := (state_succ_2 PROB.I h')), t) ` by METIS_TAC[lemma_1_1]
THEN Cases_on`slist`

THENL
[
	Q.EXISTS_TAC `[]`
	THEN SRW_TAC[][lemma_2_3_1_1, exec_plan_def, state_succ_2_def]
	THEN METIS_TAC[lemma_2_3_1_1]
	,
	`h''::t' ∈ state_set (state_list ( (PROB with I := state_succ_2 PROB.I h').I,t))` by SRW_TAC[][lemma_2_3_1_2]
	THEN Cases_on`t`
	THENL
	[
		FULL_SIMP_TAC(srw_ss())[plan_def_2, planning_problem_def, exec_plan_def, state_set_def, state_list_def]
		,
		Q.REFINE_EXISTS_TAC `h'::as''`
		THEN SRW_TAC[][exec_plan_def]
		THEN FIRST_X_ASSUM (Q.SPECL_THEN [`h'''::t''`, `PROB with I:= state_succ_2 PROB.I h'`] MP_TAC) 
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



val lemma_2_3 = prove(``!as PROB slist_1 slist_2. as <> [] /\ plan_2(PROB, as) /\ (slist_1 <> []) /\ (slist_2 <> []) /\
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
``!PROB as:(α state # α state) list. plan_2(PROB,as) ==> (LENGTH(as)) > (2** (CARD (FDOM (PROB.I))))
 ==> ?as1 as2 as3. (as1++as2++as3 = as) /\ (exec_plan(PROB.I,as1++as2) = exec_plan(PROB.I,as1)) /\  ~(as2=[])``,
SRW_TAC[][]
THEN `(CARD(state_set (state_list (PROB.I,as)))) > (2 ** CARD (FDOM PROB.I)) ` by METIS_TAC[lemma_2_1]
THEN `~INJ (LAST) (state_set (state_list (PROB.I,as))) ({s:'a state | FDOM(s) = FDOM(PROB.I)}) ` by 
     	   (SRW_TAC[][PHP,card_of_set_of_all_possible_states, FINITE_states, plan_def_2, planning_problem_def]
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
``!as PROB. plan_2(PROB,as) /\ ((LENGTH(as)) > (2** (CARD (FDOM (PROB.I))))) ==>
      ?as'. plan_2(PROB,as') /\ (LENGTH(as')<LENGTH(as))``,
SRW_TAC[][]
THEN `?as1 as2 as3. (as1++as2++as3 = as) /\ (exec_plan(PROB.I,as1++as2) = exec_plan(PROB.I,as1)) /\  ~(as2=[])` by METIS_TAC[lemma_2]
THEN ` plan_2 (PROB,as1 ++ as3)` by METIS_TAC[cycle_removal_lemma]
THEN METIS_TAC[lemma_3_1]
);

val main_lemma = store_thm("main_lemma",
``!PROB as. plan_2(PROB, as:(α state # α state) list)
	 ==> ?as'. plan_2(PROB,as') /\ (LENGTH(as') <=  (2** (CARD (FDOM (PROB.I)))))``,
SRW_TAC[][]
THEN Cases_on`(LENGTH(as) <=  (2** (CARD (FDOM (PROB.I)))))`
THENL
[
	 Q.EXISTS_TAC `as`
	 THEN METIS_TAC[]
	,
	`(LENGTH as > 2 ** CARD (FDOM PROB.I))` by DECIDE_TAC 
	THEN METIS_TAC[general_theorem', lemma_3 ]
]);

*)

(* -------------------------------------------------------------------------------------------------------    *)
(* val graph_plan_lemma_1_1_1_5 = store_thm("graph_plan_lemma_1_1_1_5",
``!PROB as vs. (plan_2(PROB, as) 
  /\ (!as'. ((as' <> []) /\ (as'<<= as)) ==> ((FST(LAST as') SUBMAP LAST (state_list(PROB.I, as'))) )) 
 /\ (vs SUBSET FDOM(PROB.I)) /\ dep_var_set(PROB, (FDOM PROB.I) DIFF vs, vs  )  /\ ~dep_var_set(PROB, vs, (FDOM PROB.I) DIFF vs))
==> plan_2(prob_proj(PROB,vs), ( FILTER (\a. varset_action(a, vs)) (MAP (\ a. ( DRESTRICT (FST a) vs, SND a)) as)))``,
Induct_on`as`
THEN1 SRW_TAC[][graph_plan_lemma_1_1_1_5_1] 
THEN SRW_TAC[][]
THEN `plan_2 (PROB with I:=state_succ_2 PROB.I h,as)` by METIS_TAC[lemma_1_1]
THEN `h IN PROB.A` by FULL_SIMP_TAC(srw_ss())[plan_def_2]
THEN `(FDOM PROB.I DIFF vs) SUBSET FDOM(PROB.I)` by SRW_TAC[][]
THEN `vs SUBSET FDOM((PROB with I:= state_succ_2 PROB.I h).I)` by FULL_SIMP_TAC(srw_ss())[FDOM_state_succ, plan_def_2, planning_problem_def]
THEN Cases_on`as<>[]`
THENL
[
 	`∀as'.(as' ≠ [] ∧ as' ≼ as ⇒ FST (LAST as') ⊑ LAST (state_list (state_succ_2 PROB.I h, as')))` by METIS_TAC[Q.SPEC `h` (Q.SPEC `PROB.I` (Q.SPEC `as` graph_plan_lemma_1_1_1_5_4))]
	THEN `plan_2(prob_proj (PROB with I:=state_succ_2 PROB.I h,vs),FILTER (λa. varset_action (a,vs))(MAP (λa. (DRESTRICT (FST a) vs,SND a)) as))` by FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_1_1_1_5_3, FDOM_state_succ, plan_def_2, planning_problem_def, graph_plan_lemma_1_1_1_5_4]
	THEN `FST (h:('a state # 'a state))  SUBMAP (PROB.I:('a state))` by
     	     (SRW_TAC[][] THEN `[h] <<= h::as` by SRW_TAC[][] THEN 
     	     `FST (LAST [h]) ⊑ LAST (state_list (PROB.I,[h]))` by SRW_TAC[][LAST_compute, state_list_def] THEN 
     	     FULL_SIMP_TAC(srw_ss())[state_list_def])
	THEN `varset_action (h,vs)` by FULL_SIMP_TAC(srw_ss())[varset_action_def]
	THEN METIS_TAC[graph_plan_lemma_1_1_1_5_2, FDOM_state_succ, plan_def_2, planning_problem_def,prob_proj_def, varset_action_def]
	,
	SRW_TAC[][]
	THEN SRW_TAC[][MAP]
	THEN ASSUME_TAC (Q.SPEC `vs`( Q.SPEC `h` (Q.SPEC `[]` (Q.SPEC `PROB` graph_plan_lemma_1_1_1_5_2))))
	THEN  `FST (h:('a state # 'a state))  SUBMAP (PROB.I:('a state))` by
     	     (SRW_TAC[][] THEN `[h] <<= h::as` by SRW_TAC[][] THEN 
     	     `FST (LAST [h]) ⊑ LAST (state_list (PROB.I,[h]))` by SRW_TAC[][LAST_compute, state_list_def] THEN 
     	     FULL_SIMP_TAC(srw_ss())[state_list_def])
	THEN `varset_action (h,vs)` by FULL_SIMP_TAC(srw_ss())[varset_action_def]
	THEN METIS_TAC[graph_plan_lemma_1_1_1_5_1, plan_def_2]
	,
	`~varset_action (h,vs)` by FULL_SIMP_TAC(srw_ss())[varset_action_def]
	THEN `planning_problem(PROB)` by FULL_SIMP_TAC(srw_ss())[plan_def_2]
	THEN `(DRESTRICT (state_succ_2 PROB.I h) vs = DRESTRICT PROB.I vs)` by METIS_TAC[ graph_plan_lemma_1_1_1_5_5, plan_def_2]
	THEN `prob_proj (PROB,vs)  = prob_proj (PROB with I := state_succ_2 PROB.I h,vs)` by SRW_TAC[][prob_proj_def]
	THEN `∀as'.(as' ≠ [] ∧ as' ≼ as ⇒ FST (LAST as') ⊑ LAST (state_list (state_succ_2 PROB.I h, as')))` by METIS_TAC[Q.SPEC `h` (Q.SPEC `PROB.I` (Q.SPEC `as` graph_plan_lemma_1_1_1_5_4))]
	THEN `plan_2(prob_proj (PROB with I:=state_succ_2 PROB.I h,vs),FILTER (λa. varset_action (a,vs))(MAP (λa. (DRESTRICT (FST a) vs,SND a)) as))` by FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_1_1_1_5_3, FDOM_state_succ, plan_def_2, planning_problem_def, graph_plan_lemma_1_1_1_5_4]
	THEN METIS_TAC[]
	,
	`~varset_action (h,vs)` by FULL_SIMP_TAC(srw_ss())[varset_action_def]
	THEN `planning_problem(PROB)` by FULL_SIMP_TAC(srw_ss())[plan_def_2]
	THEN `(DRESTRICT (state_succ_2 PROB.I h) vs = DRESTRICT PROB.I vs)` by METIS_TAC[ graph_plan_lemma_1_1_1_5_5, plan_def_2]
	THEN `prob_proj (PROB,vs)  = prob_proj (PROB with I := state_succ_2 PROB.I h,vs)` by SRW_TAC[][prob_proj_def]
	THEN SRW_TAC[][]
	THEN SRW_TAC[][MAP]
	THEN `prob_proj (PROB,vs)  = prob_proj (PROB with I := state_succ_2 PROB.I h,vs)` by SRW_TAC[][prob_proj_def]
	THEN METIS_TAC[graph_plan_lemma_1_1_1_5_1]
]);

val graph_plan_lemma_1_1_1_3 = store_thm("graph_plan_lemma_1_1_1_3",
``!PROB vs as.
	  (plan_2(PROB,as) 
	  /\ (vs SUBSET FDOM PROB.I)
	  /\ (dep_var_set(PROB, (FDOM PROB.I) DIFF vs, vs)) /\ ~(dep_var_set(PROB, vs,  (FDOM PROB.I) DIFF vs))
	  /\ LENGTH( FILTER (\a. varset_action(a, vs)) (MAP (\ a. ( DRESTRICT (FST a) vs, SND a)) as)) > (2**(CARD(vs)))  
	  /\ (∀as'. (as' ≠ [] ∧ as' ≼ as) ⇒ (FST (LAST as') ⊑ LAST (state_list (PROB.I,as')))))
	  ==>
	  (∃as1 as2 as3. 
	  	(as1 ++ as2 ++ as3 =
		      (FILTER (\a. varset_action(a, vs)) (MAP (\ a. ( DRESTRICT (FST a) vs, SND a)) as))) ∧
       	  ((exec_plan((prob_proj(PROB, vs)).I,as1 ++ as2) = exec_plan ((prob_proj(PROB, vs)).I,as1)) ∧ (as2 ≠ [])))``,
SRW_TAC[][]
THEN `CARD (FDOM (prob_proj(PROB, vs)).I) = CARD(vs)` by METIS_TAC[graph_plan_lemma_1_1_1_3_1]
THEN `plan_2
       (prob_proj (PROB,vs),
        FILTER (λa. varset_action (a,vs))
          (MAP (λa. (DRESTRICT (FST a) vs,SND a)) as))` by FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_1_1_1_3_3]
THEN `planning_problem(prob_proj(PROB,vs))` by METIS_TAC[graph_plan_lemma_1_1_1_3_2, plan_def_2] 
THEN `LENGTH (FILTER (λa. varset_action (a,vs)) (MAP (λa. (DRESTRICT (FST a) vs,SND a)) as)) > 2 ** CARD (FDOM (prob_proj (PROB,vs)).I) ` by SRW_TAC[][]
THEN METIS_TAC[lemma_2]);
*)

(* -==========================================================================================================  *) 


val dep_def = Define`dep(PROB, v1, v2) <=>  (?a. (a IN PROB.A) /\ (((v1 IN (FDOM (FST a))) /\ (v2 IN (FDOM (SND a))) )) \/(((v1 IN (FDOM (SND a))) /\ (v2 IN (FDOM (SND a))) )) ) `;


val dep_var_set_def  = Define`dep_var_set (PROB, vs1, vs2) <=> ? v1 v2. (v1 IN vs1) /\ (v2 IN vs2) /\ (DISJOINT vs1 vs2) /\ dep(PROB, v1, v2)`;

val prob_proj_def = Define`prob_proj(PROB, vs) = ((PROB with I := DRESTRICT PROB.I vs) with G := DRESTRICT PROB.G vs) with A := IMAGE (\a. (DRESTRICT (FST a) vs, DRESTRICT (SND a) vs) ) PROB.A`;

val action_proj_def = Define `action_proj(a, vs) = (DRESTRICT (FST a) vs,DRESTRICT (SND a) vs)` ;

val as_proj_def = Define `as_proj(as, vs) = (FILTER(λa. (FDOM (SND a)) <> EMPTY)) (MAP (λa. (DRESTRICT (FST a) vs, DRESTRICT (SND a) vs)) as)`;


val varset_action_def = Define ` varset_action(a:('a state # 'a state), varset) <=>  ((FDOM (SND a)) SUBSET varset) `;

val sat_precond_as_def = Define `sat_precond_as(s, as) = 
    (!as'. ((as' <> []) /\ (as'<<= as)) ==> ((FST(LAST as') SUBMAP LAST (state_list(s, as'))) ))`; 

val graph_plan_lemma_1_1_1_2_1_1_1 = store_thm("graph_plan_lemma_1_1_1_2_1_1_1",

``∀ s h as a' as'. (as <> []) /\ (as' <> []) /\  ( (a'::as' ≼ h::as) /\ FST (LAST as') ⊑ LAST (state_list (s,a'::as')))   ==> (as' ≼ as /\ FST (LAST as') ⊑ LAST (state_list (state_succ_2 s a',as')))``,

Induct_on`as'` 
THEN1 SRW_TAC [] []
THEN SRW_TAC [] [isPREFIX_THM]
THEN FULL_SIMP_TAC(srw_ss()) [state_succ_2_def, state_list_def]);



val graph_plan_lemma_1_1_1_2_1_1 = store_thm("graph_plan_lemma_1_1_1_2_1_1",
``!as s h. 
  (as <> [] /\ ∀as'.  (as' ≠ [] ∧ as' ≼ h::as ⇒ FST (LAST as') ⊑ LAST (state_list (s,as'))))   ==> 
  ∀as'.  (as' ≠ [] ∧ as' ≼ as ⇒ FST (LAST as') ⊑ LAST (state_list (state_succ_2 s h,as')))``,
SRW_TAC [] []
THEN `h::as' ≼ h::as` by METIS_TAC[isPREFIX_THM]
THEN `FST (LAST (h::as')) ⊑ LAST (state_list (s,h::as'))` by SRW_TAC[][]
THEN `FST (LAST (h::as')) = FST (LAST (as'))` by( Cases_on`as'` 
     THEN SRW_TAC[][isPREFIX_THM])
THEN `(state_list (s,h::as')) = s::(state_list (state_succ_2 s h,as'))` by SRW_TAC[][state_list_def]
THEN `LAST (state_list (s,h::as')) = LAST (s::state_list (state_succ_2 s h,as'))` by METIS_TAC[]
THEN `LAST (s::state_list (state_succ_2 s h,as')) = LAST (state_list (state_succ_2 s h,as'))` by (Cases_on`as'` 
      THEN SRW_TAC[][isPREFIX_THM, state_list_def])
THEN METIS_TAC[]);


val graph_plan_lemma_1_1_1_2_1 = store_thm("graph_plan_lemma_1_1_1_2_1",
``!as_1 as_2 as s. (as_1++as_2 = as) /\  (as <> []) /\ (∀as'. (as' ≠ [] ∧ as' ≼ as) ⇒ (FST (LAST as') ⊑ LAST (state_list (s,as'))))
==>((∀as'. (as' ≠ [] ∧ as' ≼ as_1) ⇒ (FST (LAST as') ⊑ LAST (state_list (s,as')))) /\
	(∀as'. (as' ≠ [] ∧ as' ≼ as_2) ⇒ (FST (LAST as') ⊑ LAST (state_list (exec_plan(s, as_1),as'))))  )``,

 Induct_on`as`
THEN SRW_TAC[][exec_plan_def]
THENL
[
	Cases_on`as_1`
	THEN1 FULL_SIMP_TAC(srw_ss())[rich_listTheory.IS_PREFIX_NIL, isPREFIX_THM, exec_plan_def]
	THEN Cases_on`as'`
	THEN FULL_SIMP_TAC(srw_ss())[rich_listTheory.IS_PREFIX_NIL, isPREFIX_THM]
	THEN SRW_TAC[][ ]
	THEN METIS_TAC[IS_PREFIX_APPEND1, isPREFIX_THM, APPEND, rich_listTheory.IS_PREFIX_APPEND]
	,
	Cases_on`as_1`
	THENL
	[
		FULL_SIMP_TAC(srw_ss())[rich_listTheory.IS_PREFIX_NIL, isPREFIX_THM, exec_plan_def]
		THEN METIS_TAC[IS_PREFIX_APPEND1, isPREFIX_THM, APPEND, rich_listTheory.IS_PREFIX_APPEND, graph_plan_lemma_1_1_1_2_1_1]
		,
		FULL_SIMP_TAC(srw_ss())[rich_listTheory.IS_PREFIX_NIL, isPREFIX_THM, exec_plan_def]
		THEN Cases_on`as=[]`
		THENL
		[
			SRW_TAC[][]
			THEN FULL_SIMP_TAC(srw_ss())[rich_listTheory.IS_PREFIX_NIL, isPREFIX_THM, exec_plan_def, APPEND_EQ_SING]
			THEN SRW_TAC[][]	
			THEN FULL_SIMP_TAC(srw_ss())[rich_listTheory.IS_PREFIX_NIL, isPREFIX_THM, exec_plan_def, APPEND_EQ_SING]
			,
			`∀as'. (as' ≠ [] ∧ as' ≼ as) ⇒ FST (LAST as') ⊑ LAST (state_list (state_succ_2 s h,as'))`
by METIS_TAC[graph_plan_lemma_1_1_1_2_1_1]
			THEN SRW_TAC[][exec_plan_def]

		] 
	]
]);


val graph_plan_lemma_1_1_1_2_3_1 = store_thm("graph_plan_lemma_1_1_1_2_3_1",
``!s vs a . (vs SUBSET FDOM s) /\ varset_action(a,vs) ==> ((DRESTRICT ((SND a) ⊌ s) vs) = ((SND a) ⊌ (DRESTRICT s vs)))``,
SRW_TAC[][varset_action_def]
THEN `FDOM(DRESTRICT (SND a ⊌ s) vs) = FDOM(SND a ⊌ DRESTRICT s vs)`
     by (SRW_TAC[][FDOM_DRESTRICT]
     THEN FULL_SIMP_TAC(srw_ss())[INTER_DEF, UNION_DEF, EXTENSION, SUBSET_DEF, SPECIFICATION]
     THEN METIS_TAC[])
THEN `!x. (DRESTRICT (SND a ⊌ s) vs) ' x = (SND a ⊌ DRESTRICT s vs) ' x`      by (SRW_TAC[][]
     THEN REWRITE_TAC[DRESTRICT_DEF]
     THEN FULL_SIMP_TAC(srw_ss())[SUBSET_DEF,FUNION_DEF, UNION_DEF, EXTENSION, DRESTRICT_DEF]
     THEN SRW_TAC[][]
     THENL
     [
	METIS_TAC[SPECIFICATION]
	,
	METIS_TAC[SPECIFICATION]
	,
	METIS_TAC[SPECIFICATION]
     ])
THEN METIS_TAC[fmap_EQ_THM]
);

val graph_plan_lemma_1_1_1_2_3_2 = store_thm("graph_plan_lemma_1_1_1_2_3_2",
``!fm1 fm2 vs.  (fm2 SUBMAP fm1) 
       ==> ((DRESTRICT fm2 vs) SUBMAP (DRESTRICT fm1 vs) )``,
SRW_TAC[][SUBSET_DEF, SUBMAP_DEF]
THEN FULL_SIMP_TAC(srw_ss())[SUBSET_DEF, SUBMAP_DEF, FDOM_DRESTRICT, DRESTRICT_DEF]
);


val graph_plan_lemma_1_1_1_2_3 = store_thm ("graph_plan_lemma_1_1_1_2_3",
``!s a vs. ( (FST a) SUBMAP s /\ vs SUBSET FDOM s /\ (FDOM (SND a) SUBSET FDOM s) /\ varset_action(a,vs)) ==> 
     (state_succ_2 (DRESTRICT s vs) (DRESTRICT (FST a) vs,SND a) =
     		   DRESTRICT (state_succ_2 s a) vs)``,
  SRW_TAC[][state_succ_2_def]
  THEN METIS_TAC[graph_plan_lemma_1_1_1_2_3_1, graph_plan_lemma_1_1_1_2_3_2]
);




val graph_plan_lemma_1_1_1_2_4 = store_thm ("graph_plan_lemma_1_1_1_2_4",
``! h as s. (∀l. l ≠ [] ∧ l ≼ h::as ⇒ FST (LAST l) ⊑ LAST (state_list (s,l)))
      ==> FST(h) SUBMAP s``,
SRW_TAC[][]
THEN `[h] ≠ [] ∧ [h] ≼ h::as ⇒ FST (LAST [h]) ⊑ LAST (state_list (s,h::[]))` by FULL_SIMP_TAC(srw_ss())[state_list_def, isPREFIX_THM] 
THEN FULL_SIMP_TAC(srw_ss())[state_list_def, isPREFIX_THM]
);

val graph_plan_lemma_1_1_1_2_5 = store_thm("graph_plan_lemma_1_1_1_2_5",
``!PROB a vs s. (dep_var_set(PROB, (FDOM PROB.I) DIFF vs, vs  )  /\ ~dep_var_set(PROB, vs, (FDOM PROB.I) DIFF vs)  /\  ¬varset_action (a,vs) /\ a IN PROB.A /\ vs SUBSET FDOM(PROB.I) /\ (FDOM s = FDOM PROB.I) /\ planning_problem(PROB))
==> (DRESTRICT (state_succ_2 s a) vs = DRESTRICT s vs)``,
SRW_TAC[][varset_action_def, dep_var_set_def, dep_def, SUBSET_DEF, planning_problem_def]

THEN `FDOM(DRESTRICT (state_succ_2 s a) vs) = FDOM(DRESTRICT s vs)` by METIS_TAC[FDOM_state_succ, SUBSET_DEF, FDOM_DRESTRICT]
THEN `!x. DRESTRICT (state_succ_2 s a) vs ' x = DRESTRICT s vs ' x` by (SRW_TAC[][state_succ_2_def]
     THEN REWRITE_TAC[DRESTRICT_DEF]
     THEN FULL_SIMP_TAC(srw_ss())[SUBSET_DEF,FUNION_DEF,UNION_DEF, EXTENSION, DRESTRICT_DEF, DISJOINT_DEF, INTER_DEF]
     THEN SRW_TAC[][]
     THEN METIS_TAC[SPECIFICATION])
THEN METIS_TAC[fmap_EQ_THM]
);


val graph_plan_lemma_1_1_1_2 = store_thm("graph_plan_lemma_1_1_1_2",
``!PROB s s' vs as.
	  (planning_problem(PROB)/\ (FDOM s = FDOM PROB.I) /\ (FDOM s' = FDOM PROB.I) /\ (set (as) SUBSET PROB.A) 
	  /\ (vs SUBSET FDOM PROB.I)
	  /\ (dep_var_set(PROB, (FDOM PROB.I) DIFF vs, vs)) /\ ~(dep_var_set(PROB, vs,  (FDOM PROB.I) DIFF vs))
	  /\ (∀l. (l ≠ [] ∧ (l ≼ as)) ⇒ FST (LAST l) ⊑ LAST (state_list (s, l))))
	  ==> (((exec_plan((DRESTRICT s vs), 
	     	(FILTER (\a. varset_action(a, vs)) (MAP (\ a. ( DRESTRICT (FST a) vs, SND a)) as))) 
	     = (DRESTRICT s' vs)))   
     	  <=>
	  ((DRESTRICT (exec_plan(s,as)) vs) = (DRESTRICT s' vs)))``,
Induct_on`as`
THEN SRW_TAC[][exec_plan_def]
THEN FULL_SIMP_TAC(srw_ss())[exec_plan_def]
THEN Cases_on`as = []`
THENL
[
     SRW_TAC[][exec_plan_def]
     THEN  FULL_SIMP_TAC(srw_ss())[exec_plan_def]
     THEN `FST(h) SUBMAP s` by METIS_TAC[graph_plan_lemma_1_1_1_2_4]
     THEN `varset_action(h,vs)` by FULL_SIMP_TAC(srw_ss())[varset_action_def]
     THEN METIS_TAC[graph_plan_lemma_1_1_1_2_3, planning_problem_def, varset_action_def]
     ,
     `∀l. l ≠ [] ∧ l ≼ as ⇒ FST (LAST l) ⊑ LAST (state_list (state_succ_2 s h,l))` by METIS_TAC[graph_plan_lemma_1_1_1_2_1_1]
     THEN `(state_succ_2 (DRESTRICT s vs) (DRESTRICT (FST h) vs,SND h) = DRESTRICT (state_succ_2 s h) vs)` by 
	       (SRW_TAC[][]
	       THEN `FST(h) SUBMAP s` by METIS_TAC[graph_plan_lemma_1_1_1_2_4]
	       THEN FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_1_1_1_2_3, planning_problem_def]
	       THEN `varset_action(h,vs)` by FULL_SIMP_TAC(srw_ss())[varset_action_def]
	       THEN METIS_TAC[graph_plan_lemma_1_1_1_2_3, varset_action_def, planning_problem_def, graph_plan_lemma_1_1_1_2_4])
THEN METIS_TAC[FDOM_state_succ, planning_problem_def]
     ,
     SRW_TAC[][exec_plan_def]
     THEN FULL_SIMP_TAC(srw_ss())[exec_plan_def]
     THEN `~varset_action(h,vs)` by FULL_SIMP_TAC(srw_ss())[varset_action_def]
     THEN METIS_TAC[graph_plan_lemma_1_1_1_2_5]
     ,
     `∀l. l ≠ [] ∧ l ≼ as ⇒ FST (LAST l) ⊑ LAST (state_list (state_succ_2 s h,l))` by METIS_TAC[graph_plan_lemma_1_1_1_2_1_1]
     THEN `~varset_action(h,vs)` by FULL_SIMP_TAC(srw_ss())[varset_action_def]
     THEN `DRESTRICT (state_succ_2 s h) vs = DRESTRICT s vs ` by METIS_TAC[graph_plan_lemma_1_1_1_2_5, varset_action_def]
     THEN METIS_TAC[FDOM_state_succ, planning_problem_def]
]);



val graph_plan_lemma_1_1_1_3_1 = store_thm("graph_plan_lemma_1_1_1_3_1",
``!PROB vs. (vs SUBSET FDOM(PROB.I) )
==>(CARD( FDOM((prob_proj(PROB, vs)).I)) = CARD(vs))``,
SRW_TAC[][prob_proj_def, FDOM_DRESTRICT]
THEN METIS_TAC[INTER_COMM ,SUBSET_INTER_ABSORPTION]
);


val graph_plan_lemma_1_1_1_3_2 = store_thm("graph_plan_lemma_1_1_1_3_2",
``!PROB vs. planning_problem(PROB) /\ vs SUBSET FDOM(PROB.I) 
	==> planning_problem(prob_proj(PROB,vs))``,
SRW_TAC[][prob_proj_def, plan_def_2, exec_plan_def, planning_problem_def]
THEN SRW_TAC[][prob_proj_def, plan_def_2, exec_plan_def, planning_problem_def]
THEN REWRITE_TAC[DRESTRICT_DEF]
THEN REWRITE_TAC[INTER_DEF] 
THEN FULL_SIMP_TAC(srw_ss())[SUBSET_DEF]
THEN METIS_TAC[SPECIFICATION]);



val graph_plan_lemma_1_1_1_3_3_1 = store_thm("graph_plan_lemma_1_1_1_3_3_1",
``!PROB vs. plan_2(PROB,[]) /\ (vs SUBSET FDOM PROB.I) ==> plan_2(prob_proj (PROB,vs), [])``,
SRW_TAC[][prob_proj_def, plan_def_2, exec_plan_def, planning_problem_def]
THEN SRW_TAC[][prob_proj_def, plan_def_2, exec_plan_def, planning_problem_def]
THEN REWRITE_TAC[DRESTRICT_DEF]
THEN REWRITE_TAC[INTER_DEF] 
THEN FULL_SIMP_TAC(srw_ss())[SUBSET_DEF]
THEN METIS_TAC[SPECIFICATION]
);


val graph_plan_lemma_1_1_1_3_3_2_1 = store_thm("graph_plan_lemma_1_1_1_3_3_2_1",
`` !PROB vs a.  vs ⊆ FDOM PROB.I ∧ varset_action ((DRESTRICT (FST a) vs,SND a),vs) ∧
  (a IN PROB.A) ⇒ ((DRESTRICT (FST a) vs,SND a) IN ( (prob_proj(PROB, vs)) .A))``,
SRW_TAC[][prob_proj_def,state_succ_2_def, varset_action_def, planning_problem_def, SUBSET_DEF,DRESTRICT_DEF,EXTENSION]
THEN Q.EXISTS_TAC`a`
THEN SRW_TAC[][]
THEN `!x. ((SND a) ' x = (DRESTRICT (SND a) vs) ' x)` by (SRW_TAC[][]
     THEN REWRITE_TAC[DRESTRICT_DEF]
     THEN SRW_TAC[][]
     THEN METIS_TAC[NOT_FDOM_FAPPLY_FEMPTY])
THEN `FDOM( SND a) = FDOM (DRESTRICT (SND a) vs)` by (SRW_TAC[][]
     THEN REWRITE_TAC[DRESTRICT_DEF]
     THEN METIS_TAC[SUBSET_DEF, SUBSET_INTER_ABSORPTION])
THEN METIS_TAC[fmap_EQ_THM]);



val graph_plan_lemma_1_1_1_3_3_2_2 = store_thm("graph_plan_lemma_1_1_1_3_3_2_2",
``!PROB as. plan_2(PROB, as) ==> (FDOM PROB.I = FDOM PROB.G)``,
Induct_on`as`
THEN1 SRW_TAC[][plan_def_2, exec_plan_def]
THEN SRW_TAC[][]
THEN `plan_2 (PROB with I:=state_succ_2 PROB.I h ,as)` by METIS_TAC[lemma_1_1]
THEN `FDOM (PROB with I := state_succ_2 PROB.I h).I = FDOM (PROB with I := state_succ_2 PROB.I h).G`  by METIS_TAC[]
THEN `FDOM (PROB with I := state_succ_2 PROB.I h).G = FDOM(PROB.G)` by SRW_TAC[][state_succ_2_def]
THEN METIS_TAC[FDOM_state_succ, plan_def_2, planning_problem_def, exec_plan_def]
);

val graph_plan_lemma_1_1_1_3_3_2_3 = store_thm("graph_plan_lemma_1_1_1_3_3_2_3",
``!x y vs. (vs SUBSET FDOM y) /\ (FDOM x SUBSET FDOM y ) ==> (FDOM (DRESTRICT (x) vs) ⊆ FDOM (DRESTRICT y vs))``,
SRW_TAC[][FDOM_DRESTRICT]
THEN FULL_SIMP_TAC(srw_ss())[SUBSET_DEF, INTER_DEF]
);



val graph_plan_lemma_1_1_1_3_3_2_6 = store_thm("graph_plan_lemma_1_1_1_3_3_2_6",
``!PROB vs. (vs SUBSET (FDOM PROB.I)) /\ (FDOM PROB.I = FDOM PROB.G)
	==> (FDOM (prob_proj (PROB,vs)).G = FDOM (prob_proj (PROB,vs)).I)``,
SRW_TAC[][prob_proj_def]
THEN SRW_TAC[][DRESTRICT_DEF]
);

val graph_plan_lemma_1_1_1_3_3_2_7= store_thm("graph_plan_lemma_1_1_1_3_3_2_7",
``!x vs. FDOM(x) SUBSET vs ==> (DRESTRICT x vs = x) ``,
SRW_TAC[][]     
THEN `FDOM x = FDOM(DRESTRICT x vs)` by METIS_TAC[FDOM_DRESTRICT, SUBSET_INTER_ABSORPTION]
THEN METIS_TAC[fmap_EQ_THM, DRESTRICT_DEF]
);


val graph_plan_lemma_1_1_1_3_3_2_8= store_thm("graph_plan_lemma_1_1_1_3_3_2_8",
``! as PROB vs a. FST a ⊑ PROB.I /\ varset_action(a, vs) /\ vs SUBSET FDOM(PROB.I)
==>( exec_plan ((prob_proj (PROB,vs)).I,(DRESTRICT (FST a) vs,SND a)::as) =   exec_plan((prob_proj (PROB with I := state_succ_2 PROB.I a,vs)).I,as))``,
Induct_on`as`
THEN SRW_TAC[][exec_plan_def, state_succ_2_def, prob_proj_def] 
THEN METIS_TAC[graph_plan_lemma_1_1_1_2_3_1,graph_plan_lemma_1_1_1_2_3_2] 
);


val graph_plan_lemma_1_1_1_3_3_2_9= store_thm("graph_plan_lemma_1_1_1_3_3_2_9",
``∀PROB h as vs . vs SUBSET FDOM(PROB.I) ⇒
     ((prob_proj(PROB,vs)).G = (prob_proj(PROB with I := state_succ_2 PROB.I h, vs)).G)``,
     SRW_TAC[][prob_proj_def]);

val graph_plan_lemma_1_1_1_3_3_2 = store_thm("graph_plan_lemma_1_1_1_3_3_2",
``!PROB as a vs. ((FST a) SUBMAP PROB.I) /\ planning_problem(PROB) /\ (vs SUBSET FDOM(PROB.I)) /\ (a IN PROB.A) /\ varset_action (a,vs) /\ plan_2(prob_proj(PROB with I:= state_succ_2 PROB.I a, vs), as)
==> plan_2(prob_proj (PROB,vs),(DRESTRICT (FST a) vs,(SND a))::as)``,
Cases_on`as`
THENL
[
	SRW_TAC[][]
	THEN FULL_SIMP_TAC(srw_ss())[ plan_def_2]
	THEN SRW_TAC[][]
	THENL
	[
		FULL_SIMP_TAC(srw_ss())[planning_problem_def]
		THEN SRW_TAC[][]
		THENL
		[
			FULL_SIMP_TAC(srw_ss())[prob_proj_def] 
			THEN SRW_TAC[][]
			THEN METIS_TAC[graph_plan_lemma_1_1_1_3_3_2_3]
			,
			METIS_TAC[graph_plan_lemma_1_1_1_3_3_2_6]			
		]
		,
		FULL_SIMP_TAC(srw_ss())[exec_plan_def,state_succ_2_def]
		THEN SRW_TAC[][]
		THENL
		[
			FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_1_1_1_2_3_1, prob_proj_def]
			THEN METIS_TAC[graph_plan_lemma_1_1_1_2_3_1]
			,
			FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_1_1_1_2_3_1, prob_proj_def, planning_problem_def]
			THEN METIS_TAC[graph_plan_lemma_1_1_1_2_3_2]
		]
		,
		FULL_SIMP_TAC(srw_ss())[prob_proj_def, varset_action_def]
		THEN METIS_TAC[graph_plan_lemma_1_1_1_3_3_2_7]
	]
	,
	SRW_TAC[][plan_def_2]
	THENL
	[
		FULL_SIMP_TAC(srw_ss())[planning_problem_def]
		THEN SRW_TAC[][]
		THENL
		[
			FULL_SIMP_TAC(srw_ss())[prob_proj_def] 
			THEN SRW_TAC[][]
			THEN METIS_TAC[graph_plan_lemma_1_1_1_3_3_2_3]
			,
			METIS_TAC[graph_plan_lemma_1_1_1_3_3_2_6]			
		]
		,
		METIS_TAC[graph_plan_lemma_1_1_1_3_3_2_8, graph_plan_lemma_1_1_1_3_3_2_9]
		,
		FULL_SIMP_TAC(srw_ss())[prob_proj_def, varset_action_def]
		THEN METIS_TAC[graph_plan_lemma_1_1_1_3_3_2_7]
		,
		FULL_SIMP_TAC(srw_ss())[prob_proj_def, varset_action_def]
		THEN METIS_TAC[graph_plan_lemma_1_1_1_3_3_2_7]
		,
		FULL_SIMP_TAC(srw_ss())[prob_proj_def, varset_action_def]
	]	
]);




val graph_plan_lemma_1_1_1_3_3_3 = store_thm("graph_plan_lemma_1_1_1_3_3_3",
``!PROB vs1 vs2 a. (a IN PROB.A) /\ (vs1 SUBSET FDOM(PROB.I)) /\ (vs2 SUBSET FDOM(PROB.I)) ==>  (dep_var_set(PROB with I:= state_succ_2 PROB.I a,vs1,vs2) <=> dep_var_set(PROB, vs1, vs2))``,
SRW_TAC[][dep_var_set_def, dep_def]
);






val graph_plan_lemma_1_1_1_3_3_6 = store_thm("graph_plan_lemma_1_1_1_3_3_6",
``! x y vs.  varset_action((x ,DRESTRICT y vs),vs)``,
SRW_TAC[][varset_action_def, FDOM_DRESTRICT]
);



val graph_plan_lemma_1_1_1_3_3_7_1 = store_thm("graph_plan_lemma_1_1_1_3_3_7_1",
``!h s vs. (FDOM(SND h) SUBSET FDOM s) ==> ( FDOM(state_succ_2 s (action_proj(h,vs))) =
       		     FDOM (state_succ_2 s h))``,
SRW_TAC[][action_proj_def, state_succ_2_def, FUNION_DEF, FDOM_DRESTRICT, INTER_DEF, SUBSET_DEF, UNION_DEF, EXTENSION, SUBMAP_DEF]
THEN METIS_TAC[]
);

val graph_plan_lemma_1_1_1_3_3_7_2_1 = store_thm("graph_plan_lemma_1_1_1_3_3_7_2_1",
``!x vs y. x IN vs ==> (x IN FDOM (DRESTRICT (y) vs) <=> (x ∈ FDOM (y)))``,
SRW_TAC[][DRESTRICT_DEF]);

val graph_plan_lemma_1_1_1_3_3_7_2 = store_thm("graph_plan_lemma_1_1_1_3_3_7_2",
``!h s vs. ((FST h) SUBMAP s) /\ (FDOM(SND h) SUBSET FDOM s) ==> (DRESTRICT (state_succ_2 s (action_proj(h,vs))) vs =
       		     DRESTRICT (state_succ_2 s h) vs)``,
SRW_TAC[][]
THEN `FDOM(DRESTRICT (state_succ_2 s (action_proj(h,vs))) vs) = FDOM (DRESTRICT (state_succ_2 s h) vs)` by
     SRW_TAC[][graph_plan_lemma_1_1_1_3_3_7_1, FDOM_DRESTRICT]
THEN `!x. (DRESTRICT (state_succ_2 s (action_proj(h,vs))) vs) ' x = (DRESTRICT (state_succ_2 s h) vs) ' x` by
     (FULL_SIMP_TAC(srw_ss())[action_proj_def, state_succ_2_def, FUNION_DEF, DRESTRICT_DEF, SUBSET_DEF, INTER_DEF, EXTENSION]
     THEN SRW_TAC[][]
     THENL
     [
	FULL_SIMP_TAC(srw_ss())[FUNION_DEF]
     	THEN SRW_TAC[][]
     	THEN1 FULL_SIMP_TAC(srw_ss())[DRESTRICT_DEF]
     	THEN METIS_TAC[graph_plan_lemma_1_1_1_3_3_7_2_1]
	,
	FULL_SIMP_TAC(srw_ss())[FUNION_DEF]
     	THEN SRW_TAC[][]
     	THEN1 FULL_SIMP_TAC(srw_ss())[DRESTRICT_DEF]
     	THEN METIS_TAC[graph_plan_lemma_1_1_1_3_3_7_2_1]
	,
	FULL_SIMP_TAC(srw_ss())[FUNION_DEF]
     	THEN SRW_TAC[][]
     	THEN1 FULL_SIMP_TAC(srw_ss())[DRESTRICT_DEF]
     	THEN METIS_TAC[graph_plan_lemma_1_1_1_3_3_7_2_1]
	,
	FULL_SIMP_TAC(srw_ss())[FUNION_DEF, SUBMAP_DEF, FDOM_DRESTRICT, INTER_DEF, DRESTRICT_DEF]
     	THEN METIS_TAC[graph_plan_lemma_1_1_1_3_3_7_2_1]
	,
	FULL_SIMP_TAC(srw_ss())[FUNION_DEF, SUBMAP_DEF, FDOM_DRESTRICT, INTER_DEF, DRESTRICT_DEF]
     	THEN METIS_TAC[graph_plan_lemma_1_1_1_3_3_7_2_1]	
     ])
THEN METIS_TAC[fmap_EQ_THM]
);

val graph_plan_lemma_1_1_1_3_3_7 = store_thm("graph_plan_lemma_1_1_1_3_3_7",
``! PROB vs h as.
h IN PROB.A /\ planning_problem(PROB) /\ FST h SUBMAP PROB.I /\ (plan_2(prob_proj (PROB with I:=state_succ_2 PROB.I h,vs),as))
    ==>
(plan_2(prob_proj (PROB with I:=state_succ_2 PROB.I (action_proj(h,vs)),vs),as))``,
FULL_SIMP_TAC(srw_ss())[plan_def_2]
THEN SRW_TAC[][]
THENL
[
	FULL_SIMP_TAC(srw_ss())[prob_proj_def, planning_problem_def]
	THEN SRW_TAC[][]
	THEN SRW_TAC[][pairTheory.SND]
	THENL
	[
		`FDOM (state_succ_2 PROB.I (action_proj(h,vs)) ) = FDOM PROB.I` by 
     	      	      (`FDOM (state_succ_2 PROB.I h) = FDOM PROB.I` by METIS_TAC[FDOM_state_succ]
    	      	THEN METIS_TAC[graph_plan_lemma_1_1_1_3_3_7_1])
		THEN FULL_SIMP_TAC(srw_ss())[FDOM_DRESTRICT, INTER_DEF, SUBSET_DEF, EXTENSION] 
		THEN METIS_TAC[]
		,
		METIS_TAC[graph_plan_lemma_1_1_1_3_3_7_1, FDOM_DRESTRICT]
	]
	,
	`(prob_proj(PROB with I := state_succ_2 PROB.I (action_proj (h,vs)),vs))
		 = (prob_proj(PROB with I := state_succ_2 PROB.I h,vs))` by(
		 FULL_SIMP_TAC(srw_ss())[prob_proj_def, graph_plan_lemma_1_1_1_3_3_7_2_1, planning_problem_def]
		 THEN SRW_TAC[][graph_plan_lemma_1_1_1_3_3_7_2])
	THEN SRW_TAC[][]
	,
	FULL_SIMP_TAC(srw_ss())[prob_proj_def]	
]);





val graph_plan_lemma_1_1_1_3_3_8_1 = store_thm("graph_plan_lemma_1_1_1_3_3_8_1",
``!s vs a . FST a SUBMAP s ==> (state_succ_2 (DRESTRICT s vs) (action_proj(a, vs))=
     	DRESTRICT (state_succ_2 s a) vs)``,
SRW_TAC[][state_succ_2_def,action_proj_def]
THEN `FDOM (DRESTRICT (SND a) vs ⊌ DRESTRICT s vs) = FDOM (DRESTRICT (SND a ⊌ s) vs)` by
     (SRW_TAC[][FDOM_DRESTRICT]
     THEN FULL_SIMP_TAC(srw_ss())[INTER_DEF, UNION_DEF, EXTENSION, SUBSET_DEF, SPECIFICATION]
     THEN METIS_TAC[])
THEN `!x. (DRESTRICT (SND a) vs ⊌ DRESTRICT s vs) ' x = (DRESTRICT (SND a ⊌ s) vs) ' x` by (SRW_TAC[][]
     THEN REWRITE_TAC[DRESTRICT_DEF]
     THEN FULL_SIMP_TAC(srw_ss())[SUBSET_DEF,FUNION_DEF, UNION_DEF, EXTENSION, DRESTRICT_DEF]
     THEN SRW_TAC[][]
     THEN METIS_TAC[SPECIFICATION])
THEN METIS_TAC[fmap_EQ_THM, FDOM_FUNION, graph_plan_lemma_1_1_1_2_3_2]);


val graph_plan_lemma_1_1_1_3_3_8_2= store_thm("graph_plan_lemma_1_1_1_3_3_8_2",
``! as PROB vs a. FST a ⊑ PROB.I ==>( exec_plan ((prob_proj (PROB,vs)).I,action_proj(a,vs)::as) =   exec_plan((prob_proj (PROB with I := state_succ_2 PROB.I a,vs)).I,as))``,
Induct_on`as`
THEN SRW_TAC[][exec_plan_def, prob_proj_def] 
THEN METIS_TAC[graph_plan_lemma_1_1_1_3_3_8_1]
);


val graph_plan_lemma_1_1_1_3_3_8 = store_thm("graph_plan_lemma_1_1_1_3_3_8",
``!PROB as a vs. ((FST a) SUBMAP PROB.I) /\ planning_problem(PROB) /\ (vs SUBSET FDOM(PROB.I)) /\ (a IN PROB.A) /\ plan_2(prob_proj(PROB with I:= state_succ_2 PROB.I a, vs), as)
==> plan_2(prob_proj (PROB,vs),action_proj(a, vs)::as)``,
Cases_on`as`
THENL
[
	SRW_TAC[][]
	THEN FULL_SIMP_TAC(srw_ss())[ plan_def_2]
	THEN SRW_TAC[][]
	THENL
	[
		FULL_SIMP_TAC(srw_ss())[planning_problem_def]
		THEN SRW_TAC[][]
		THENL
		[
			FULL_SIMP_TAC(srw_ss())[prob_proj_def] 
			THEN SRW_TAC[][]
			THEN METIS_TAC[graph_plan_lemma_1_1_1_3_3_2_3]
			,
			METIS_TAC[graph_plan_lemma_1_1_1_3_3_2_6]			
		]
		,
		FULL_SIMP_TAC(srw_ss())[exec_plan_def]
		THEN FULL_SIMP_TAC(srw_ss())[prob_proj_def]
		THEN METIS_TAC[graph_plan_lemma_1_1_1_3_3_8_1]
		,
		FULL_SIMP_TAC(srw_ss())[prob_proj_def, action_proj_def]
		THEN METIS_TAC[]
	]
	,
	SRW_TAC[][plan_def_2]
	THENL
	[
		FULL_SIMP_TAC(srw_ss())[planning_problem_def]
		THEN SRW_TAC[][]
		THENL
		[
			FULL_SIMP_TAC(srw_ss())[prob_proj_def] 
			THEN SRW_TAC[][]
			THEN METIS_TAC[graph_plan_lemma_1_1_1_3_3_2_3]
			, 
			METIS_TAC[graph_plan_lemma_1_1_1_3_3_2_6]			
		]
		,
		METIS_TAC[graph_plan_lemma_1_1_1_3_3_8_2, graph_plan_lemma_1_1_1_3_3_2_9]
		,
		FULL_SIMP_TAC(srw_ss())[prob_proj_def,action_proj_def]
		THEN METIS_TAC[graph_plan_lemma_1_1_1_3_3_2_7]
		,
		FULL_SIMP_TAC(srw_ss())[prob_proj_def, action_proj_def]
		THEN METIS_TAC[graph_plan_lemma_1_1_1_3_3_2_7]
		,
		FULL_SIMP_TAC(srw_ss())[prob_proj_def, action_proj_def]
	]
])
val graph_plan_lemma_1_1_1_3_3_9 = store_thm("graph_plan_lemma_1_1_1_3_3_9",
``!as a vs. FDOM (DRESTRICT (SND a) vs) <> ∅ ==>
     ((as_proj (a::as,vs)) =  (action_proj(a, vs)::as_proj(as,vs))) ``,
SRW_TAC[][action_proj_def, as_proj_def]);

val graph_plan_lemma_1_1_1_3_3_10 = store_thm("graph_plan_lemma_1_1_1_3_3_10",
``!as a vs. (FDOM (DRESTRICT (SND a) vs) = ∅) ==>
      (as_proj (a::as,vs) = as_proj(as,vs))``,
SRW_TAC[][action_proj_def, as_proj_def]);







val graph_plan_lemma_1_1_1_3_3_11_1_1_1 = store_thm("graph_plan_lemma_1_1_1_3_3_11_1_1_1",
``!fm1 fm2 vs. (vs ⊆ FDOM fm1) /\ (fm2 = fm1) 
       ==> ((DRESTRICT fm2 vs) = (DRESTRICT fm1 vs) )``,
SRW_TAC[][SUBSET_DEF, SUBMAP_DEF]
);


val graph_plan_lemma_1_1_1_3_3_11_1_1_2 = store_thm("graph_plan_lemma_1_1_1_3_3_11_1_1_2",
``!x vs s. (DISJOINT (FDOM (x)) vs) ==> ((DRESTRICT s vs) = (DRESTRICT (x ⊌ s) vs))``,

SRW_TAC[][dep_var_set_def, dep_def, DISJOINT_DEF, DRESTRICT_DEF, INTER_DEF, EXTENSION, planning_problem_def, FUNION_DEF]
THEN `!x''. (x'' IN vs) ==> (((x ⊌ s) ' x'') = s ' x'')` by (SRW_TAC[][FUNION_DEF] THEN METIS_TAC[])
THEN `FDOM (DRESTRICT s vs) = FDOM ( DRESTRICT(x ⊌ s) vs)` by( SRW_TAC [][FDOM_DRESTRICT,EXTENSION] THEN FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN METIS_TAC[])
THEN SRW_TAC[][]
THEN `!x''. (DRESTRICT s vs) ' x'' = (DRESTRICT (x ⊌ s) vs) ' x''` by (Cases_on`x'' ∉ FDOM x`
     THEN Cases_on`x'' ∉ vs`
     THEN SRW_TAC[][FDOM_DRESTRICT, INTER_DEF, DRESTRICT_DEF]
     THEN METIS_TAC[])
THEN METIS_TAC[fmap_EQ_THM]
);


val graph_plan_lemma_1_1_1_3_3_11_1_1 = store_thm("graph_plan_lemma_1_1_1_3_3_11_1_1",
``!a vs s. (DISJOINT  (FDOM (SND a)) vs)
==> ((DRESTRICT s vs) = (DRESTRICT (state_succ_2 s  a) vs))``,
SRW_TAC[][]
THEN SRW_TAC[][dep_var_set_def, dep_def, DISJOINT_DEF, DRESTRICT_DEF, INTER_DEF, EXTENSION, planning_problem_def]
THEN SRW_TAC[][state_succ_2_def, FUNION_DEF]
THEN METIS_TAC[graph_plan_lemma_1_1_1_3_3_11_1_1_2]
);


val graph_plan_lemma_1_1_1_3_3_11_1 = store_thm("graph_plan_lemma_1_1_1_3_3_11_1",
``!s a vs. (FDOM (DRESTRICT (SND a) vs) = ∅) ==>
       (DRESTRICT (state_succ_2 s (action_proj (a,vs))) vs = DRESTRICT s vs)``,
SRW_TAC[][action_proj_def]
THEN `FDOM (DRESTRICT (DRESTRICT (SND a) vs) vs) = EMPTY` by FULL_SIMP_TAC(srw_ss())[DRESTRICT_IDEMPOT]
THEN FULL_SIMP_TAC(srw_ss())[Once FDOM_DRESTRICT]
THEN `DISJOINT (FDOM (DRESTRICT (SND (DRESTRICT (FST a) vs,DRESTRICT (SND a) vs)) vs)) vs` by SRW_TAC[][DISJOINT_DEF]
THEN FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_1_1_1_3_3_11_1_1]); 


val graph_plan_lemma_1_1_1_3_3_11 = store_thm("graph_plan_lemma_1_1_1_3_3_11",
``!PROB a vs. (FDOM (DRESTRICT (SND a) vs) = ∅) ==>
       (prob_proj(PROB with I := state_succ_2 PROB.I (action_proj (a,vs)),vs)
		  = prob_proj(PROB, vs))``,
SRW_TAC[][prob_proj_def, graph_plan_lemma_1_1_1_3_3_11_1]);

val graph_plan_lemma_1_1_1_3_3 = store_thm("graph_plan_lemma_1_1_1_3_3",
``!PROB as vs. (plan_2(PROB, as) 
  /\ (!as'. ((as' <> []) /\ (as'<<= as)) ==> ((FST(LAST as') SUBMAP LAST (state_list(PROB.I, as'))) )) 
 /\ (vs SUBSET FDOM(PROB.I)))
==> plan_2(prob_proj(PROB,vs), as_proj(as, vs))``,
Induct_on`as`
THEN1 SRW_TAC[][graph_plan_lemma_1_1_1_3_3_1, as_proj_def] 
THEN SRW_TAC[][]
THEN `plan_2 (PROB with I:=state_succ_2 PROB.I h,as)` by METIS_TAC[lemma_1_1]
THEN `h IN PROB.A` by FULL_SIMP_TAC(srw_ss())[plan_def_2]
THEN `(FDOM PROB.I DIFF vs) SUBSET FDOM(PROB.I)` by SRW_TAC[][]
THEN `vs SUBSET FDOM((PROB with I:= state_succ_2 PROB.I h).I)` by FULL_SIMP_TAC(srw_ss())[FDOM_state_succ, plan_def_2, planning_problem_def]
THEN Cases_on`as<>[]`
THENL
[
 	`∀as'.(as' ≠ [] ∧ as' ≼ as ⇒ FST (LAST as') ⊑ LAST (state_list (state_succ_2 PROB.I h, as')))` by METIS_TAC[Q.SPEC `h` (Q.SPEC `PROB.I` (Q.SPEC `as` graph_plan_lemma_1_1_1_2_1_1))]
	THEN `plan_2(prob_proj (PROB with I:=state_succ_2 PROB.I h,vs),as_proj(as,vs))` by FULL_SIMP_TAC(srw_ss())[FDOM_state_succ, plan_def_2, planning_problem_def]
	THEN `plan_2(prob_proj (PROB with I:=state_succ_2 PROB.I (action_proj(h,vs)),vs),as_proj(as,vs))` by 
	     (SRW_TAC[][]
	     THEN `(FST h) SUBMAP PROB.I` by METIS_TAC[graph_plan_lemma_1_1_1_2_4]
	     THEN METIS_TAC[graph_plan_lemma_1_1_1_3_3_7, planning_problem_def, plan_def_2])
	THEN Cases_on `(FDOM (DRESTRICT (SND h) vs) <> ∅)`
	THENL
	[
		SRW_TAC[][graph_plan_lemma_1_1_1_3_3_9]
		THEN METIS_TAC[graph_plan_lemma_1_1_1_3_3_8, plan_def_2, graph_plan_lemma_1_1_1_2_4]
		,
		FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_1_1_1_3_3_10]
		THEN METIS_TAC[graph_plan_lemma_1_1_1_3_3_11]
	]
	,
	SRW_TAC[][as_proj_def]
	THEN SRW_TAC[][MAP_EQ_NIL]
	THEN SRW_TAC[][GSYM action_proj_def]
	THEN `plan_2(prob_proj (PROB with I:=state_succ_2 PROB.I h,vs),[])` by METIS_TAC[graph_plan_lemma_1_1_1_3_3_1]
	THEN `plan_2(prob_proj (PROB with I:=state_succ_2 PROB.I (action_proj(h,vs)),vs),[])` by 
		(SRW_TAC[][]
	     	THEN `(FST h) SUBMAP PROB.I` by METIS_TAC[graph_plan_lemma_1_1_1_2_4]
	     	THEN METIS_TAC[graph_plan_lemma_1_1_1_3_3_7, planning_problem_def, plan_def_2])
	THEN METIS_TAC[graph_plan_lemma_1_1_1_3_3_8, plan_def_2, graph_plan_lemma_1_1_1_2_4, graph_plan_lemma_1_1_1_3_3_11]
]);


val graph_plan_lemma_1_1_1_3 = store_thm("graph_plan_lemma_1_1_1_3",
``!PROB vs as.
	  (plan_2(PROB,as) 
	  /\ (vs SUBSET FDOM PROB.I)
	  /\ LENGTH(as_proj(as, vs)) > (2**(CARD(vs)))  
	  /\ (∀as'. (as' ≠ [] ∧ as' ≼ as) ⇒ (FST (LAST as') ⊑ LAST (state_list (PROB.I,as')))))
	  ==>
	  (∃as1 as2 as3. 
	  	(as1 ++ as2 ++ as3 =
		      as_proj(as, vs)) ∧
       	  ((exec_plan((prob_proj(PROB, vs)).I,as1 ++ as2) = exec_plan ((prob_proj(PROB, vs)).I,as1)) ∧ (as2 ≠ [])))``,
SRW_TAC[][]
THEN `CARD (FDOM (prob_proj(PROB, vs)).I) = CARD(vs)` by METIS_TAC[graph_plan_lemma_1_1_1_3_1]
THEN `plan_2(prob_proj (PROB,vs), as_proj(as, vs))` by FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_1_1_1_3_3]
THEN `planning_problem(prob_proj(PROB,vs))` by METIS_TAC[graph_plan_lemma_1_1_1_3_2, plan_def_2] 
THEN `LENGTH (as_proj(as, vs)) > 2 ** CARD (FDOM (prob_proj (PROB,vs)).I) ` by SRW_TAC[][]
THEN METIS_TAC[lemma_2]);


val graph_plan_lemma_1_1_1_4 = store_thm("graph_plan_lemma_1_1_1_4",
``!vs as: ('a state # 'a state) list. ( LENGTH(FILTER (\a. varset_action(a, vs)) as) = LENGTH( FILTER (\a. varset_action(a, vs)) (MAP (\ a. ( DRESTRICT (FST a) vs, SND a)) as)))``,
Induct_on`as`
THEN SRW_TAC[][FILTER]
THEN FULL_SIMP_TAC(srw_ss())[LENGTH_MAP, varset_action_def]
);




val graph_plan_lemma_1_1_1_6_1_1 = store_thm("graph_plan_lemma_1_1_1_6_1_1",
``!PROB a vs. ((vs SUBSET FDOM(PROB.I)) /\ dep_var_set(PROB, FDOM(PROB.I) DIFF vs, vs) /\ ~dep_var_set(PROB, vs, FDOM(PROB.I) DIFF vs)) /\ (a IN PROB.A) /\ (varset_action (a,vs))
==> (DISJOINT  (FDOM (SND a)) (FDOM(PROB.I) DIFF vs))``,
SRW_TAC[][dep_var_set_def, dep_def, DISJOINT_DEF, INTER_DEF, EXTENSION, varset_action_def, SUBSET_DEF]
THEN METIS_TAC[]
);

val graph_plan_lemma_1_1_1_6_1 = store_thm("graph_plan_lemma_1_1_1_6_1",
``!PROB s vs a. (planning_problem(PROB) /\ (FDOM s = FDOM PROB.I) /\ (vs SUBSET FDOM PROB.I) /\ (dep_var_set(PROB, (FDOM PROB.I) DIFF vs, vs)) /\ ~(dep_var_set(PROB, vs,  (FDOM PROB.I) DIFF vs)) /\  varset_action (a,vs) /\ (a IN PROB.A))
==> (DRESTRICT (state_succ_2 s a) (FDOM PROB.I DIFF vs) = (DRESTRICT s (FDOM PROB.I DIFF vs)))``,

SRW_TAC[][]
THEN METIS_TAC[graph_plan_lemma_1_1_1_1_1_2, graph_plan_lemma_1_1_1_1_1_1, graph_plan_lemma_1_1_1_6_1_1,DIFF_SUBSET]
);

val graph_plan_lemma_1_1_1_6_2_1 = store_thm("graph_plan_lemma_1_1_1_6_2_1",
``!PROB s s' a vs. (planning_problem(PROB) /\ (FDOM s = FDOM PROB.I) /\ (FDOM s' = FDOM PROB.I) 
	    /\ (a IN PROB.A)
	    /\ (vs SUBSET FDOM PROB.I) 
     	    /\ ((DRESTRICT s vs) = (DRESTRICT s' vs)) /\ (FDOM(FST a) SUBSET vs))
	    ==>
	    ((DRESTRICT (state_succ_2 s a) vs) = (DRESTRICT (state_succ_2 s' a) vs))
``,
SRW_TAC[][state_succ_2_def]
THENL
     [
	`FDOM (DRESTRICT (SND a ⊌ s) vs) = FDOM(DRESTRICT (SND a ⊌ s') vs)` by FULL_SIMP_TAC(srw_ss())[DRESTRICT_DEF, FUNION_DEF]	
	THEN `!x. (DRESTRICT (SND a ⊌ s) vs) ' x = (DRESTRICT (SND a ⊌ s') vs) ' x` by
     	     (FULL_SIMP_TAC(srw_ss())[DRESTRICT_DEF, FUNION_DEF, UNION_DEF, INTER_DEF]
     	     THEN SRW_TAC[][]
     	     THEN `x IN FDOM (DRESTRICT s vs)` by SRW_TAC[][FDOM_DRESTRICT]
     	     THEN `x IN FDOM (DRESTRICT s' vs)` by SRW_TAC[][FDOM_DRESTRICT]
     	     THEN METIS_TAC[DRESTRICT_DEF])
	THEN METIS_TAC[fmap_EQ_THM]
	,
	`FDOM (DRESTRICT (SND a ⊌ s) vs) = FDOM(DRESTRICT (s') vs)` by
	      (FULL_SIMP_TAC(srw_ss())[DRESTRICT_DEF, FUNION_DEF, INTER_DEF, fmap_EXT, FDOM_DRESTRICT, SUBSET_DEF, INTER_DEF, EXTENSION, SUBMAP_DEF, FUNION_DEF]	
	      THEN SRW_TAC[][]
	      THEN METIS_TAC[fmap_EQ_THM, SUBSET_DEF])
	THEN `!x. (DRESTRICT (SND a ⊌ s) vs) ' x = (DRESTRICT (s') vs) ' x` by(
     	     FULL_SIMP_TAC(srw_ss())[DRESTRICT_DEF, FUNION_DEF, INTER_DEF, fmap_EXT, FDOM_DRESTRICT, SUBSET_DEF, INTER_DEF, EXTENSION, SUBMAP_DEF, FUNION_DEF]
	     THEN SRW_TAC[][]
     	     THEN METIS_TAC[DRESTRICT_DEF])
	THEN METIS_TAC[fmap_EQ_THM]
	,
 	`FDOM (DRESTRICT s vs) = FDOM(DRESTRICT (SND a ⊌ s') vs)` by
	      (FULL_SIMP_TAC(srw_ss())[DRESTRICT_DEF, FUNION_DEF, INTER_DEF, fmap_EXT, FDOM_DRESTRICT, SUBSET_DEF, INTER_DEF, EXTENSION, SUBMAP_DEF, FUNION_DEF]	
	      THEN SRW_TAC[][]
	      THEN METIS_TAC[fmap_EQ_THM, SUBSET_DEF])
	THEN `!x. (DRESTRICT s vs) ' x = (DRESTRICT (SND a ⊌ s') vs) ' x` by (
     	     FULL_SIMP_TAC(srw_ss())[DRESTRICT_DEF, FUNION_DEF, INTER_DEF, fmap_EXT, FDOM_DRESTRICT, SUBSET_DEF, INTER_DEF, EXTENSION, SUBMAP_DEF, FUNION_DEF]
	     THEN SRW_TAC[][]
     	     THEN METIS_TAC[DRESTRICT_DEF])
	THEN METIS_TAC[fmap_EQ_THM]
	
     ]);


val graph_plan_lemma_1_1_1_6_2_2 = store_thm("graph_plan_lemma_1_1_1_6_2_2",
``!PROB a vs. (planning_problem(PROB) /\ (vs SUBSET FDOM PROB.I) /\ a IN PROB.A /\ FDOM(FST a) SUBSET FDOM(PROB.I)
	    /\ (dep_var_set(PROB, (FDOM PROB.I) DIFF vs, vs)) /\ ~(dep_var_set(PROB, vs,  (FDOM PROB.I) DIFF vs)) 
     	    /\ ~varset_action(a,vs) )
	    ==>
	    (FDOM (FST a) SUBSET ((FDOM PROB.I) DIFF vs))``,
SRW_TAC[][dep_var_set_def, varset_action_def, dep_def, SUBSET_DEF, DISJOINT_DEF, INTER_DEF, EXTENSION, planning_problem_def]
THEN METIS_TAC[]
);

val graph_plan_lemma_1_1_1_6_2_3 = store_thm("graph_plan_lemma_1_1_1_6_2_3",
``!fm1 fm2. ~(FDOM fm1 SUBSET FDOM fm2)
	    ==>
	    ~(fm1 SUBMAP fm2)``,
SRW_TAC[][SUBSET_DEF, SUBMAP_DEF]
THEN METIS_TAC[]
);



val graph_plan_lemma_1_1_1_6_2 = store_thm("graph_plan_lemma_1_1_1_6_2",
``!PROB s s' as vs. (planning_problem(PROB) /\ (FDOM s = FDOM PROB.I) /\ (FDOM s' = FDOM PROB.I) 
	    /\ (set as SUBSET PROB.A)
	    /\ (vs SUBSET FDOM PROB.I) 
	    /\ (dep_var_set(PROB, (FDOM PROB.I) DIFF vs, vs)) /\ ~(dep_var_set(PROB, vs,  (FDOM PROB.I) DIFF vs)) 
     	    /\ ((DRESTRICT s ((FDOM PROB.I) DIFF vs)) = (DRESTRICT s' ((FDOM PROB.I) DIFF vs))))
	    ==>
            (DRESTRICT (exec_plan (s,FILTER (λa. ¬varset_action (a,vs)) as)) (FDOM PROB.I DIFF vs)
	    	      = 
                  DRESTRICT (exec_plan (s',FILTER (λa. ¬varset_action (a,vs)) as)) (FDOM PROB.I DIFF vs))``,
Induct_on`as`
THEN SRW_TAC[][exec_plan_def]
THEN Cases_on`FDOM(FST h) SUBSET FDOM(PROB.I)`
THENL
[
	`(FDOM (FST h) SUBSET ((FDOM PROB.I) DIFF vs))` by METIS_TAC[graph_plan_lemma_1_1_1_6_2_2]
	THEN ASSUME_TAC (Q.SPEC `((FDOM PROB.I) DIFF vs)`( Q.SPEC `h`(Q.SPEC `s'`(Q.SPEC `s`(Q.SPEC `PROB`( graph_plan_lemma_1_1_1_6_2_1))))))
	THEN `FDOM PROB.I DIFF vs ⊆ FDOM PROB.I` by METIS_TAC[DIFF_SUBSET]
	THEN `DRESTRICT (state_succ_2 s h) (FDOM PROB.I DIFF vs) = DRESTRICT (state_succ_2 s' h) (FDOM PROB.I DIFF vs)` by METIS_TAC[] 
	THEN METIS_TAC[planning_problem_def, FDOM_state_succ]
	,
	SRW_TAC[][]
	THEN METIS_TAC[graph_plan_lemma_1_1_1_6_2_3, state_succ_2_def]
]);

val graph_plan_lemma_1_1_1_6 = store_thm("graph_plan_lemma_1_1_1_6",
``!PROB s as vs. (planning_problem(PROB) /\ (FDOM s = FDOM PROB.I) /\ (set as SUBSET PROB.A)
	    /\ (vs SUBSET FDOM PROB.I) 
	    /\ (dep_var_set(PROB, (FDOM PROB.I) DIFF vs, vs)) /\ ~(dep_var_set(PROB, vs,  (FDOM PROB.I) DIFF vs))) 
     	    ==>
            ((DRESTRICT (exec_plan(s,as)) ((FDOM PROB.I) DIFF vs)) = (DRESTRICT (exec_plan (s,FILTER (\a. ~varset_action (a,vs)) as)) ((FDOM PROB.I) DIFF vs)))``,
Induct_on`as`
THEN SRW_TAC[][exec_plan_def]
THENL
[
	METIS_TAC[FDOM_state_succ, planning_problem_def]	
	,	
	`DRESTRICT (state_succ_2 s h) (FDOM PROB.I DIFF vs) = DRESTRICT s (FDOM PROB.I DIFF vs)` by METIS_TAC[graph_plan_lemma_1_1_1_6_1]
	THEN `DRESTRICT (exec_plan (s,FILTER (λa. ¬varset_action (a,vs)) as)) (FDOM PROB.I DIFF vs)
             = DRESTRICT (exec_plan ((state_succ_2 s h),FILTER (λa. ¬varset_action (a,vs)) as)) (FDOM PROB.I DIFF vs)` by METIS_TAC[graph_plan_lemma_1_1_1_6_2, FDOM_state_succ, planning_problem_def]
	THEN METIS_TAC[FDOM_state_succ, planning_problem_def] 
]);


val graph_plan_lemma_1_1_1_6 = store_thm("graph_plan_lemma_1_1_1_6",
``!PROB s as vs P. (planning_problem(PROB) /\ (FDOM s = FDOM PROB.I) /\ (set as SUBSET PROB.A)
	    /\ (vs SUBSET FDOM PROB.I) 
	    /\ (!a. P a ==> DISJOINT (FDOM (SND a)) vs)) 
     	    ==>
            ((DRESTRICT (exec_plan(s,as)) (vs)) = (DRESTRICT (exec_plan (s,FILTER (\a. ~(P a)) as)) (vs)))``,
Induct_on`as`
THEN SRW_TAC[][exec_plan_def]
THENL
[
	METIS_TAC[FDOM_state_succ, planning_problem_def]	
	,
	`DRESTRICT (state_succ_2 s h) (vs) = DRESTRICT s (vs)` by METIS_TAC[GSYM graph_plan_lemma_1_1_1_3_3_11_1_1]
	THEN `DRESTRICT (exec_plan (s,FILTER (λa. ¬varset_action (a,vs)) as)) (FDOM PROB.I DIFF vs)
             = DRESTRICT (exec_plan ((state_succ_2 s h),FILTER (λa. ¬varset_action (a,vs)) as)) (FDOM PROB.I DIFF vs)` by METIS_TAC[graph_plan_lemma_1_1_1_6_2, FDOM_state_succ, planning_problem_def]
	THEN METIS_TAC[FDOM_state_succ, planning_problem_def] 
]);


val graph_plan_lemma_1_1_1_7 = store_thm("graph_plan_lemma_1_1_1_7",
``!PROB s s' vs. ((vs SUBSET FDOM s) /\ (FDOM s = FDOM s') 
	    /\ ((DRESTRICT s ((FDOM s) DIFF vs)) = (DRESTRICT s' ((FDOM s) DIFF vs)))
	    /\ ((DRESTRICT s vs) = (DRESTRICT s' vs)) )  
     	    ==>
            (s = s')``,
SRW_TAC[][SUBSET_DEF, DRESTRICT_DEF]
THEN `!x. s ' x = s' ' x` by SRW_TAC[][]
THEN Cases_on`x IN FDOM s`
THEN FULL_SIMP_TAC(srw_ss()) [DRESTRICT_DEF, INTER_DEF, fmap_EXT]
THEN SRW_TAC[][]
THEN METIS_TAC[DRESTRICT_DEF, INTER_DEF, FDOM_F_FEMPTY1, NOT_FDOM_FAPPLY_FEMPTY]
THEN METIS_TAC[fmap_EQ_THM]
);

val graph_plan_lemma_1_1_1_8_1 = store_thm("graph_plan_lemma_1_1_1_8_1",
``! as s PROB. ((set as) SUBSET (PROB.A) /\ planning_problem(PROB) /\ (FDOM s = FDOM PROB.I)) ==> (FDOM(exec_plan(s, as)) = FDOM PROB.I)``,
Induct_on `as`
THEN SRW_TAC[][exec_plan_def]
THEN FULL_SIMP_TAC(srw_ss())[SPECIFICATION, planning_problem_def]
THEN METIS_TAC[FDOM_state_succ, planning_problem_def]
);

val graph_plan_lemma_1_1_1_8 = store_thm("graph_plan_lemma_1_1_1_8",
``! as PROB s. (planning_problem(PROB) /\ (FDOM s = FDOM PROB.I) 	   
	  /\ (set as SUBSET PROB.A)) ==> plan_2((PROB with I:=s) with G:=exec_plan(s,as), as)``,
SRW_TAC[][plan_def_2, planning_problem_def] 
THEN SRW_TAC[][]
THEN METIS_TAC[graph_plan_lemma_1_1_1_8_1,planning_problem_def]
);

val graph_plan_lemma_1_1_1_8_2 = store_thm("graph_plan_lemma_1_1_1_8_2",
``!P l s. set(l) SUBSET s ==>
       	  set(FILTER P l) SUBSET s``,
 METIS_TAC [LIST_TO_SET_FILTER, INTER_SUBSET, SUBSET_TRANS]);

val rem_condless_act_def
   = Define `(rem_condless_act(s:'a state, pfx_a:(('a state # 'a state) list),  a::as:(('a state # 'a state) list) )	         = if ((FST a) SUBMAP exec_plan(s, pfx_a)) then rem_condless_act(s, pfx_a++[a], as)
	     else rem_condless_act(s, pfx_a, as))
	   /\ (rem_condless_act(s:'a state, pfx_a:(('a state # 'a state) list), [] ) = pfx_a)`;


val graph_plan_lemma_1_1_1_9_1_1 = store_thm("graph_plan_lemma_1_1_1_9_1_1",
``!s h as pfx. exec_plan (s,rem_condless_act (s,h:: pfx,as)) = exec_plan (state_succ_2 s h,rem_condless_act (state_succ_2 s h ,pfx,as))``,
Induct_on`as`
THEN SRW_TAC[][rem_condless_act_def, exec_plan_def, state_succ_2_def] 
);

val graph_plan_lemma_1_1_1_9_1 = store_thm("graph_plan_lemma_1_1_1_9_1",
``!as PROB s. ( planning_problem(PROB) /\ (FDOM s = FDOM PROB.I) 	   
	  /\ (set as SUBSET PROB.A)) ==>
	  (exec_plan(s, as) = exec_plan(s, rem_condless_act(s, [], as)))``,
Induct_on`as`
THEN SRW_TAC[][rem_condless_act_def, exec_plan_def]
THEN METIS_TAC[graph_plan_lemma_1_1_1_9_1_1, FDOM_state_succ, planning_problem_def, state_succ_2_def]
);

val graph_plan_lemma_1_1_1_9_2_1_1 = store_thm("graph_plan_lemma_1_1_1_9_2_1_1",
``!h' pfx as s. rem_condless_act (s,h'::pfx,as) = h'::rem_condless_act (state_succ_2 s h',pfx,as)``,
Induct_on`as`
THEN SRW_TAC[][rem_condless_act_def, exec_plan_def, state_succ_2_def] 
);

val graph_plan_lemma_1_1_1_9_2_1 = store_thm("graph_plan_lemma_1_1_1_9_2_1",
``! h h' as as' s. h'::as' ≼ rem_condless_act (s,[h],as) ==> (as'<<=  rem_condless_act (state_succ_2 s h,[],as) /\ (h' = h))``,
Induct_on`as`
THEN SRW_TAC[][rem_condless_act_def, exec_plan_def]
THEN FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_1_1_1_9_2_1_1]);


val graph_plan_lemma_1_1_1_9_2 = store_thm("graph_plan_lemma_1_1_1_9_2",
``!as PROB s. ( planning_problem(PROB) /\ (FDOM s = FDOM PROB.I) 	   
	  /\ (set as SUBSET PROB.A)) ==>
	  (∀as'. (as' ≠ [] ∧ as' ≼ rem_condless_act(s, [], as)) ⇒ (FST (LAST as') ⊑ LAST (state_list (s,as'))))``,
Induct_on`as`
THEN SRW_TAC[][rem_condless_act_def, exec_plan_def]
THENL
[
	`as' = []` by METIS_TAC[IS_PREFIX_NIL]
	,
	Cases_on`as'`
	THEN1 SRW_TAC[][rem_condless_act_def, exec_plan_def, state_list_def]
	THEN Cases_on`t`
	THENL
	[
		`h = h'` by METIS_TAC[graph_plan_lemma_1_1_1_9_2_1]
		THEN SRW_TAC[][state_list_def]
		,
		`LAST (h'::h''::t') = LAST (h''::t') ` by METIS_TAC[graph_plan_lemma_1_1_1_9_2_1, planning_problem_def, LAST_CONS, state_list_def]
		THEN `LAST (state_list (s,h'::h''::t')) = LAST (state_list (state_succ_2 s h',h''::t'))` by METIS_TAC[graph_plan_lemma_1_1_1_9_2_1, planning_problem_def, LAST_CONS, state_list_def]
		THEN `(h''::t' ≼ rem_condless_act (state_succ_2 s h,[],as))/\ (h' = h)` by METIS_TAC[graph_plan_lemma_1_1_1_9_2_1]		
		THEN `h''::t' ≠ []` by SRW_TAC[][]
		THEN `FDOM (state_succ_2 s h) = FDOM PROB.I` by METIS_TAC[graph_plan_lemma_1_1_1_9_2_1, planning_problem_def, LAST_CONS, state_list_def, FDOM_state_succ]
		THEN `state_succ_2 s h' = state_succ_2 s h` by SRW_TAC[][]
		THEN `FST (LAST (h''::t')) ⊑ LAST (state_list (state_succ_2 s h',h''::t'))` by METIS_TAC[]
		THEN METIS_TAC[]
	]
	,
	METIS_TAC[]	
]);


val graph_plan_lemma_1_1_1_9_3 = store_thm("graph_plan_lemma_1_1_1_9_3",
``!as PROB s. ( planning_problem(PROB) /\ (FDOM s = FDOM PROB.I) 	   
	  /\ (set as SUBSET PROB.A)) ==>
	  (LENGTH (rem_condless_act(s, [], as)) <= LENGTH as)``,
Induct_on`as`
THEN SRW_TAC[][rem_condless_act_def, exec_plan_def]
THENL
[
	FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_1_1_1_9_2_1_1]
	THEN SRW_TAC[][graph_plan_lemma_1_1_1_9_2_1_1]
	THEN `FDOM (state_succ_2 s h) = FDOM PROB.I` by METIS_TAC[graph_plan_lemma_1_1_1_9_2_1_1, FDOM_state_succ, planning_problem_def]
	THEN METIS_TAC[]
	,
	`LENGTH (rem_condless_act (s,[],as)) ≤ (LENGTH as)` by METIS_TAC[]
	THEN DECIDE_TAC
]);

val graph_plan_lemma_1_1_1_9_4 = store_thm("graph_plan_lemma_1_1_1_9_4",
``!as PROB s. ( planning_problem(PROB) /\ (FDOM s = FDOM PROB.I) 	   
	  /\ (set as SUBSET PROB.A)) ==>
	  (set (rem_condless_act (s,[],as)) SUBSET PROB.A )``,
Induct_on`as`
THEN SRW_TAC[][rem_condless_act_def, exec_plan_def]
THEN FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_1_1_1_9_2_1_1]
THEN METIS_TAC[graph_plan_lemma_1_1_1_9_2_1_1, FDOM_state_succ, planning_problem_def]);





val graph_plan_lemma_1_1_1_9_5 = store_thm("graph_plan_lemma_1_1_1_9_5",
``!as PROB s. ( planning_problem(PROB) /\ (FDOM s = FDOM PROB.I) 	   
	  /\ (set as SUBSET PROB.A)) ==>
	  (LENGTH (rem_condless_act (s,[],as)) <= LENGTH as )``,
Induct_on`as`
THEN SRW_TAC[][rem_condless_act_def, exec_plan_def]
THENL
[
	FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_1_1_1_9_2_1_1]
	THEN METIS_TAC[graph_plan_lemma_1_1_1_9_2_1_1, FDOM_state_succ, planning_problem_def]
	,
	`LENGTH (rem_condless_act (s,[],as)) ≤ (LENGTH as)` by METIS_TAC[]
	THEN DECIDE_TAC
]);


val graph_plan_lemma_1_1_1_9_6 = store_thm("graph_plan_lemma_1_1_1_9_6",
``!as PROB s P. ( planning_problem(PROB) /\ (FDOM s = FDOM PROB.I) 	   
	  /\ (set as SUBSET PROB.A)) ==>
	  (LENGTH (FILTER P (rem_condless_act (s,[],as)))  <= LENGTH (FILTER P as) )``,
Induct_on`as`
THEN SRW_TAC[][rem_condless_act_def, exec_plan_def]
THENL
[
	FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_1_1_1_9_2_1_1]
	THEN METIS_TAC[graph_plan_lemma_1_1_1_9_2_1_1, FDOM_state_succ, planning_problem_def]
	,
	FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_1_1_1_9_2_1_1]
	THEN METIS_TAC[graph_plan_lemma_1_1_1_9_2_1_1, FDOM_state_succ, planning_problem_def]
	,
	`LENGTH (FILTER P (rem_condless_act (s,[],as))) <= (LENGTH (FILTER P as))` by METIS_TAC[]
	THEN DECIDE_TAC
	,
	`LENGTH (FILTER P (rem_condless_act (s,[],as))) <= (LENGTH (FILTER P as))` by METIS_TAC[]
]);


val graph_plan_lemma_1_1_1_9 = store_thm("graph_plan_lemma_1_1_1_9",
``!as PROB s. (planning_problem(PROB) /\ (FDOM s = FDOM PROB.I) 	   
	  /\ (set as SUBSET PROB.A)) ==>
	  ((exec_plan(s, as) = exec_plan(s, rem_condless_act(s, [], as))) /\ (∀as'. (as' ≠ [] ∧ as' ≼ rem_condless_act(s, [], as)) ⇒ (FST (LAST as') ⊑ LAST (state_list (s, as')))) /\ (LENGTH (rem_condless_act(s, [], as)) <= LENGTH as) /\ (set (rem_condless_act (s,[],as)) SUBSET PROB.A )) /\ (LENGTH (rem_condless_act (s,[],as)) <= LENGTH as )
	  /\ (!P. (LENGTH (FILTER P (rem_condless_act (s,[],as)))  <= LENGTH (FILTER P as) ))``,
METIS_TAC[graph_plan_lemma_1_1_1_9_1, graph_plan_lemma_1_1_1_9_2, graph_plan_lemma_1_1_1_9_3, graph_plan_lemma_1_1_1_9_4, graph_plan_lemma_1_1_1_9_5, graph_plan_lemma_1_1_1_9_6]);


val graph_plan_lemma_1_1_1_10_1 = store_thm("graph_plan_lemma_1_1_1_10_1",
``! f1 f2 as1 as2 p. (as1 ++ as2 =
       FILTER f1 (MAP f2  p)) ==>
	      ?p_1 p_2. (p_1 ++ p_2 = p) /\ (as1 = FILTER f1 (MAP f2 p_1)) /\ (as2 = FILTER f1 (MAP f2 p_2))``,
Induct_on`p`
THEN SRW_TAC[][]
THENL
[
	Cases_on`as1`
	THENL
	[
		FULL_SIMP_TAC(srw_ss())[]
		THEN Q.EXISTS_TAC `[]`
		THEN Q.EXISTS_TAC `h::p`
		THEN SRW_TAC[][]
		,
		FULL_SIMP_TAC(srw_ss())[]
		THEN `∃p_1 p_2.
          	   (p_1 ++ p_2 = p) /\ (as2 = FILTER f1 (MAP f2 p_2)) /\ (t = FILTER f1 (MAP f2 p_1))` by METIS_TAC[]
		THEN Q.EXISTS_TAC `h::p_1`
		THEN Q.EXISTS_TAC `p_2`
		THEN SRW_TAC[][]
	]
	,	
	`∃p_1 p_2.
          (p_1 ++ p_2 = p) /\ (as2 = FILTER f1 (MAP f2 p_2)) /\ (as1 = FILTER f1 (MAP f2 p_1))` by METIS_TAC[]
	THEN Q.EXISTS_TAC `h::p_1`
	THEN Q.EXISTS_TAC `p_2`
	THEN SRW_TAC[][]
]);



val graph_plan_lemma_1_1_1_10 = store_thm("graph_plan_lemma_1_1_1_10",
``! f1 f2 as1 as2 as3 p. (as1 ++ as2 ++ as3 =
       FILTER f1 (MAP f2  p)) ==>
	      ?p_1 p_2 p_3. (p_1 ++ p_2 ++ p_3 = p) /\ (as1 = FILTER f1 (MAP f2 p_1)) /\ (as2 = FILTER f1 (MAP f2 p_2)) /\ (as3 = FILTER f1 (MAP f2 p_3))``,
SRW_TAC[][]
THEN `∃p_1 p_2.
          (p_1 ++ p_2 = p) /\ ((as1) = FILTER f1 (MAP f2 p_1)) /\ (as2++as3 = FILTER f1 (MAP f2 p_2))` by METIS_TAC[graph_plan_lemma_1_1_1_10_1, APPEND_ASSOC] 

THEN `∃p_a p_b.
          (p_a ++ p_b = p_2) /\ ((as2) = FILTER f1 (MAP f2 p_a)) /\ (as3 = FILTER f1 (MAP f2 p_b))` by METIS_TAC[graph_plan_lemma_1_1_1_10_1] 
THEN Q.EXISTS_TAC `p_1`
THEN Q.EXISTS_TAC `p_a`
THEN Q.EXISTS_TAC `p_b`
THEN SRW_TAC[][]);


val graph_plan_lemma_1_1_1_11_1_3 = store_thm("graph_plan_lemma_1_1_1_11_1_3",
``!x s s' vs. (DRESTRICT s vs = DRESTRICT s' vs) /\ (x ⊑ s) ==> ((DRESTRICT x vs) SUBMAP s')``,
SRW_TAC[][DRESTRICT_DEF, SUBMAP_DEF]
THEN `FDOM (DRESTRICT s vs) = FDOM  (DRESTRICT s' vs)` by FULL_SIMP_TAC(srw_ss())[]
THENL
[
	FULL_SIMP_TAC(srw_ss())[DRESTRICT_DEF, SUBMAP_DEF, INTER_DEF, EXTENSION]
	THEN METIS_TAC[SPECIFICATION]
	,
	`!x. (DRESTRICT s vs) ' x =  (DRESTRICT s' vs) ' x` by FULL_SIMP_TAC(srw_ss())[]
	THEN FULL_SIMP_TAC(srw_ss())[DRESTRICT_DEF, SUBMAP_DEF, INTER_DEF, EXTENSION]
	THEN METIS_TAC[]	
]);



val graph_plan_lemma_1_1_1_11_1_2 = store_thm("graph_plan_lemma_1_1_1_11_1_2",
``!x s vs. (x ⊑ s) ==> ((DRESTRICT x vs) SUBMAP s)``,
SRW_TAC[][DRESTRICT_DEF, SUBMAP_DEF]
THEN `FDOM (DRESTRICT s vs) = FDOM  (DRESTRICT s' vs)` by FULL_SIMP_TAC(srw_ss())[]
);



val graph_plan_lemma_1_1_1_11_1_1 = store_thm("graph_plan_lemma_1_1_1_11_1_1",
``∀s s' a vs.
     (FST a ⊑ s ∧ vs ⊆ FDOM s  ∧
     varset_action (a,vs) /\ (DRESTRICT s vs = DRESTRICT s' vs) )⇒
     (DRESTRICT (state_succ_2 s' (DRESTRICT (FST a) vs,SND a)) vs =
      DRESTRICT (state_succ_2 s a) vs)``,
  SRW_TAC[][state_succ_2_def]
  THEN `FDOM (DRESTRICT s vs) = FDOM  (DRESTRICT s' vs)` by FULL_SIMP_TAC(srw_ss())[]
  THEN `FDOM (DRESTRICT (SND a ⊌ s') vs) = FDOM (DRESTRICT (SND a ⊌ s) vs)` by (FULL_SIMP_TAC(srw_ss())[FDOM_DRESTRICT, DRESTRICT_DEF, UNION_DEF, INTER_DEF, EXTENSION, varset_action_def, SUBSET_DEF]
       THEN  METIS_TAC[])
  THEN `!x. (DRESTRICT s vs) ' x =  (DRESTRICT s' vs) ' x` by FULL_SIMP_TAC(srw_ss())[]
  THEN `!x. (DRESTRICT (SND a ⊌ s') vs) ' x = (DRESTRICT (SND a ⊌ s) vs) ' x` by (FULL_SIMP_TAC(srw_ss())[FDOM_DRESTRICT, DRESTRICT_DEF, UNION_DEF, INTER_DEF, EXTENSION, varset_action_def, SUBSET_DEF, FUNION_DEF]
       THEN METIS_TAC[])
  THEN1 METIS_TAC[fmap_EQ_THM]
  THEN  METIS_TAC[graph_plan_lemma_1_1_1_11_1_3]);





val graph_plan_lemma_1_1_1_11_1_4 = store_thm("graph_plan_lemma_1_1_1_11_1_4",
``∀vs h.
    (varset_action(h, vs)) ⇒
     (DRESTRICT (state_succ_2 (DRESTRICT s vs) h) vs =
     		state_succ_2 (DRESTRICT s vs) h)``,
SRW_TAC[][state_succ_2_def]
THEN `FDOM (DRESTRICT (SND h ⊌ DRESTRICT s vs) vs) = FDOM (SND h ⊌ DRESTRICT s vs)` by (FULL_SIMP_TAC(srw_ss())[FDOM_DRESTRICT, varset_action_def, FUNION_DEF, dep_var_set_def, dep_def, SUBSET_DEF, EXTENSION, planning_problem_def]
     THEN METIS_TAC[])
THEN `!x. (DRESTRICT (SND h ⊌ DRESTRICT s vs) vs) ' x = (SND h ⊌ DRESTRICT s vs) ' x` by (FULL_SIMP_TAC(srw_ss())[FDOM_DRESTRICT, varset_action_def, FUNION_DEF, dep_var_set_def, dep_def, SUBSET_DEF, EXTENSION, planning_problem_def, DRESTRICT_IDEMPOT]
     THEN (SRW_TAC[][FUNION_DEF]
 	  THENL
	  [
		Cases_on`x IN vs`
	  	THEN1  SRW_TAC[][DRESTRICT_DEF, FUNION_DEF, DRESTRICT_IDEMPOT]
	  	THEN METIS_TAC[DRESTRICT_DEF]	
		,
		Cases_on`x IN vs`
     	  	THEN SRW_TAC[][DRESTRICT_DEF, FUNION_DEF, DRESTRICT_IDEMPOT]
	  ]))  
THEN METIS_TAC[fmap_EQ_THM]);

val graph_plan_lemma_1_1_1_11_1_5 = store_thm("graph_plan_lemma_1_1_1_11_1_5",
``!fm1 fm2 vs.  (fm2 SUBMAP fm1) 
       ==> ((DRESTRICT fm2 vs) SUBMAP (fm1) )``,
SRW_TAC[][SUBSET_DEF, SUBMAP_DEF]
THEN FULL_SIMP_TAC(srw_ss())[SUBSET_DEF, SUBMAP_DEF, FDOM_DRESTRICT, DRESTRICT_DEF]
);



val graph_plan_lemma_1_1_1_11_1_6_1 = store_thm("graph_plan_lemma_1_1_1_11_1_6_1",
``!x s vs. (DRESTRICT x vs  ⊑ s) <=> ( DRESTRICT x vs SUBMAP DRESTRICT s vs)``,
SRW_TAC[][DRESTRICT_DEF, SUBMAP_DEF]
THEN EQ_TAC
THEN METIS_TAC[]);


val graph_plan_lemma_1_1_1_11_1_6 = store_thm ("graph_plan_lemma_1_1_1_11_1_6",
``!s a vs. ( vs SUBSET FDOM s /\ (FDOM (SND a) SUBSET FDOM s) /\ varset_action(a,vs)) ==> 
     (state_succ_2 (DRESTRICT s vs) (DRESTRICT (FST a) vs,SND a) =
     		   DRESTRICT (state_succ_2 s (DRESTRICT (FST a) vs,SND a)) vs)``,
  SRW_TAC[][state_succ_2_def]
  THEN METIS_TAC[graph_plan_lemma_1_1_1_2_3_1, graph_plan_lemma_1_1_1_2_3_2, graph_plan_lemma_1_1_1_11_1_2, graph_plan_lemma_1_1_1_11_1_6_1]
);


val graph_plan_lemma_1_1_1_11_1_7 = store_thm ("graph_plan_lemma_1_1_1_11_1_7",
``!s a vs. ( (FST a) SUBMAP s ) ==> 
     (state_succ_2 (s ) (DRESTRICT (FST a) vs,SND a) =
     		   (state_succ_2 s (a)) )``,
  SRW_TAC[][state_succ_2_def]
  THEN METIS_TAC[graph_plan_lemma_1_1_1_2_3_1, graph_plan_lemma_1_1_1_2_3_2, graph_plan_lemma_1_1_1_11_1_2]
);


val graph_plan_lemma_1_1_1_11_1 = store_thm("graph_plan_lemma_1_1_1_11_1",
``∀PROB s as vs.
     ( planning_problem PROB ∧ set as ⊆ PROB.A ∧ (FDOM s = FDOM PROB.I) /\
     vs ⊆ FDOM PROB.I ∧ dep_var_set (PROB,FDOM PROB.I DIFF vs,vs) ∧
     ¬dep_var_set (PROB,vs,FDOM PROB.I DIFF vs)
     /\ (∀as'. (as' ≠ [] ∧ as' ≼ as) ⇒ (FST (LAST as') ⊑ LAST (state_list (s,as'))))) ⇒ 
     (DRESTRICT (exec_plan(DRESTRICT s vs, (FILTER (λa. varset_action (a,vs))(MAP (λa. (DRESTRICT (FST a) vs,SND a)) as)))) vs 
	   = exec_plan(DRESTRICT s vs, (FILTER (λa. varset_action (a,vs))(MAP (λa. (DRESTRICT (FST a) vs,SND a)) as))))``,
Induct_on `as`
THEN SRW_TAC[][exec_plan_def]
THENL
[
       Cases_on `as = []`
       THENL[
		FULL_SIMP_TAC(srw_ss())[exec_plan_def]
		THEN SRW_TAC[][]
		THEN METIS_TAC[graph_plan_lemma_1_1_1_11_1_4]
		,
		`(state_succ_2 (DRESTRICT s vs) (DRESTRICT (FST h) vs,SND h)) = (DRESTRICT (state_succ_2 s (DRESTRICT (FST h) vs,SND h)) vs)` by 
			       (FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_1_1_1_2_3, graph_plan_lemma_1_1_1_2_4, planning_problem_def, varset_action_def]
  		THEN `FST h SUBMAP s` by METIS_TAC[graph_plan_lemma_1_1_1_11_1_5, graph_plan_lemma_1_1_1_2_4]
		THEN `varset_action(h, vs)` by SRW_TAC[][varset_action_def]
		THEN `FDOM( SND h) SUBSET FDOM s` by SRW_TAC[][]
		THEN METIS_TAC[graph_plan_lemma_1_1_1_11_1_6])
       		THEN `FDOM (state_succ_2 s (DRESTRICT (FST h) vs,SND h)) = FDOM PROB.I` by (SRW_TAC[][FDOM_state_succ, planning_problem_def]
     	  	     THEN `FDOM (SND(DRESTRICT (FST h) vs,SND h)) SUBSET FDOM PROB.I` by FULL_SIMP_TAC(srw_ss())[planning_problem_def]  
	  	     THEN METIS_TAC[FDOM_state_succ])
       		THEN `(∀as'. (as' ≠ [] ∧ as' ≼ as) ⇒ (FST (LAST as') ⊑ LAST (state_list ((state_succ_2 s (DRESTRICT (FST h) vs,SND h)),as'))))` by (SRW_TAC[][] 
     	   	     THEN `(∀as'. (as' ≠ [] ∧ as' ≼ as) ⇒ (FST (LAST as') ⊑ LAST (state_list ((state_succ_2 s h),as'))))` by METIS_TAC[graph_plan_lemma_1_1_1_2_1_1]
       	   	     THEN `FST h SUBMAP s` by METIS_TAC[graph_plan_lemma_1_1_1_11_1_5, graph_plan_lemma_1_1_1_2_4]
	   	     THEN METIS_TAC[graph_plan_lemma_1_1_1_11_1_7])
		THEN METIS_TAC[]	  
	]
	,
	`~varset_action(h, vs)` by FULL_SIMP_TAC(srw_ss())[varset_action_def]
	THEN `(DRESTRICT (state_succ_2 s h) vs = DRESTRICT s vs)` by METIS_TAC[graph_plan_lemma_1_1_1_2_5]
	THEN Cases_on `as = []`
	THEN1 FULL_SIMP_TAC(srw_ss())[exec_plan_def]
	THEN `(∀as'. (as' ≠ [] ∧ as' ≼ as) ⇒ (FST (LAST as') ⊑ LAST (state_list ((state_succ_2 s h),as'))))` by METIS_TAC[graph_plan_lemma_1_1_1_2_1_1]
	THEN METIS_TAC[FDOM_state_succ, planning_problem_def]
]);

val graph_plan_lemma_1_1_1_11_2 = store_thm("graph_plan_lemma_1_1_1_11_2",
``∀PROB s as vs.
     (planning_problem PROB ∧ set as ⊆ PROB.A ∧ (FDOM s = FDOM PROB.I) /\
     vs ⊆ FDOM PROB.I) ⇒ 
        (DRESTRICT (exec_plan(DRESTRICT s vs, (FILTER (λa. varset_action (a,vs))(MAP (λa. (DRESTRICT (FST a) vs,SND a)) as)))) vs 
		   = DRESTRICT (exec_plan(s, (FILTER (λa. varset_action (a,vs))(MAP (λa. (DRESTRICT (FST a) vs,SND a)) as)))) vs)``,
Induct_on `as`
THEN SRW_TAC[][exec_plan_def]
THENL
[	
	`varset_action(h, vs)` by FULL_SIMP_TAC(srw_ss())[varset_action_def]
	THEN `state_succ_2 (DRESTRICT s vs) (DRESTRICT (FST h) vs,SND h) = DRESTRICT (state_succ_2 ( s ) (DRESTRICT (FST h) vs,SND h)) vs` by METIS_TAC[graph_plan_lemma_1_1_1_11_1_6, planning_problem_def]
	THEN `FDOM (state_succ_2 ( s ) (DRESTRICT (FST h) vs,SND h)) = FDOM PROB.I` by FULL_SIMP_TAC(srw_ss())[planning_problem_def, FDOM_state_succ]
	THEN METIS_TAC[]
	,
	METIS_TAC[]
]);


val graph_plan_lemma_1_1_1_11 = store_thm("graph_plan_lemma_1_1_1_11",
``∀PROB s as vs.
     ( planning_problem PROB ∧ set as ⊆ PROB.A ∧ (FDOM s = FDOM PROB.I) /\
     vs ⊆ FDOM PROB.I ∧ dep_var_set (PROB,FDOM PROB.I DIFF vs,vs) ∧
     ¬dep_var_set (PROB,vs,FDOM PROB.I DIFF vs)
        /\ (∀as'. (as' ≠ [] ∧ as' ≼ as) ⇒ (FST (LAST as') ⊑ LAST (state_list (s,as'))))) ⇒ 
        (DRESTRICT (exec_plan( s, (FILTER (λa. varset_action (a,vs))(MAP (λa. (DRESTRICT (FST a) vs,SND a)) as)))) vs = exec_plan(DRESTRICT s vs, (FILTER (λa. varset_action (a,vs))(MAP (λa. (DRESTRICT (FST a) vs,SND a)) as))))``,
SRW_TAC[][]
THEN METIS_TAC[graph_plan_lemma_1_1_1_11_2, graph_plan_lemma_1_1_1_11_1]);



val graph_plan_lemma_1_1_1_12 = store_thm("graph_plan_lemma_1_1_1_12",
``∀as s PROB vs. set as ⊆ PROB.A ∧ planning_problem PROB ∧ (FDOM s = FDOM PROB.I) ⇒ (FDOM (exec_plan (s,FILTER (λa. varset_action (a,vs))(MAP (λa. (DRESTRICT (FST a) vs,SND a)) as))) = FDOM PROB.I)``,
Induct_on `as`
THEN SRW_TAC[][exec_plan_def]
THEN FULL_SIMP_TAC(srw_ss())[SPECIFICATION, planning_problem_def]
THEN `FDOM (state_succ_2 s (DRESTRICT (FST h) vs,SND h)) = FDOM PROB.I` by  FULL_SIMP_TAC(srw_ss())[FDOM_state_succ]
THEN METIS_TAC[]);







val graph_plan_lemma_1_1_1_13 = store_thm("graph_plan_lemma_1_1_1_13",
``∀PROB s as vs.
     (planning_problem PROB ∧ set as ⊆ PROB.A ∧ (FDOM s = FDOM PROB.I) /\
     vs ⊆ FDOM PROB.I ∧ dep_var_set (PROB,FDOM PROB.I DIFF vs,vs) ∧
     ¬dep_var_set (PROB,vs,FDOM PROB.I DIFF vs)
     /\ (∀as'. (as' ≠ [] ∧ as' ≼ as) ⇒ (FST (LAST as') ⊑ LAST (state_list (s,as'))))) ⇒ 
        (DRESTRICT (exec_plan(s, (FILTER (λa. varset_action (a,vs))(MAP (λa. (DRESTRICT (FST a) vs,SND a)) as)))) vs = DRESTRICT (exec_plan(s,  as)) vs)``,
SRW_TAC[][]
THEN `(DRESTRICT
        (exec_plan
           (s,
            FILTER (λa. varset_action (a,vs))
              (MAP (λa. (DRESTRICT (FST a) vs,SND a)) as))) vs =
      exec_plan
        (DRESTRICT s vs,
         FILTER (λa. varset_action (a,vs))
           (MAP (λa. (DRESTRICT (FST a) vs,SND a)) as)))` by METIS_TAC[graph_plan_lemma_1_1_1_11]
THEN `?s'. (FDOM s' = FDOM PROB.I) /\ (exec_plan (DRESTRICT s vs, FILTER (λa. varset_action (a,vs)) (MAP (λa. (DRESTRICT (FST a) vs,SND a)) as)) = DRESTRICT s' vs)` by (SRW_TAC[][]
     	   THEN  Q.EXISTS_TAC `(exec_plan(s, FILTER (λa. varset_action (a,vs)) (MAP (λa. (DRESTRICT (FST a) vs,SND a)) as)))`
	   THEN SRW_TAC[][]
	   THEN1 METIS_TAC[graph_plan_lemma_1_1_1_12]
	   THEN METIS_TAC[graph_plan_lemma_1_1_1_11])

THEN `DRESTRICT s' vs = DRESTRICT (exec_plan(s,as)) vs` by METIS_TAC[Q.SPEC `as`( Q.SPEC `vs`( Q.SPEC `s'`( Q.SPEC `s` (Q.SPEC `PROB` graph_plan_lemma_1_1_1_2))))]
THEN METIS_TAC[]
);



val graph_plan_lemma_1_1_1_14_1 = store_thm("graph_plan_lemma_1_1_1_14_1",
``!PROB vs as s s'. 
      (planning_problem PROB ∧ set as ⊆ PROB.A /\ (FDOM s = FDOM PROB.I) /\ (FDOM s' = FDOM PROB.I) 
      ∧ vs ⊆ FDOM s ∧ (dep_var_set(PROB, (FDOM PROB.I) DIFF vs, vs)) /\ ~(dep_var_set(PROB, vs,  (FDOM PROB.I) DIFF vs)) /\
      (DRESTRICT s vs = DRESTRICT s' vs) /\
      ∀as'. as' ≠ [] ∧ as' ≼ as ⇒  FST (LAST as') ⊑ LAST (state_list (s,as')))
      ==> 
      (!as'. as' <> [] /\ as' ≼ FILTER (λa. varset_action (a,vs)) (MAP (λa. (DRESTRICT (FST a) vs,SND a)) as)
      	  ==> FST (LAST as') ⊑ LAST (state_list (s', as')))``,
Induct_on `as`
THEN SRW_TAC[][exec_plan_def]
THEN1 METIS_TAC[rich_listTheory.IS_PREFIX_NIL]
THENL[
Cases_on `as = []`
THENL[
	Cases_on `as'`
	THEN1 SRW_TAC[][]
	THEN FULL_SIMP_TAC(srw_ss())[]
	THEN SRW_TAC[][]
	THEN FULL_SIMP_TAC(srw_ss())[state_list_def]
	THEN `t= []` by METIS_TAC[rich_listTheory.IS_PREFIX_NIL]
	THEN `[h] <<= [h]` by SRW_TAC[][]
	THEN `(FST (LAST [h])) SUBMAP LAST ( state_list (s,[h]))` by SRW_TAC[][state_list_def]
	THEN FULL_SIMP_TAC(srw_ss())[state_list_def]
	THEN SRW_TAC[][]
	THEN METIS_TAC[graph_plan_lemma_1_1_1_11_1_3]	
	,
	`∀as'. (as' ≠ [] ∧ as' ≼ as) ⇒ FST (LAST as') ⊑ LAST (state_list (state_succ_2 s h,as'))` by METIS_TAC[graph_plan_lemma_1_1_1_2_1_1]
	THEN Cases_on `as'`
	THEN1 SRW_TAC[][]
	THEN FULL_SIMP_TAC(srw_ss())[]
	THEN SRW_TAC[][]
	THEN Cases_on `t <> []`
	THENL
	[
	     SRW_TAC[][LAST_DEF, state_list_def]
	     THEN1 METIS_TAC[empty_state_list_lemma]
	     THEN `DRESTRICT (state_succ_2 s h) vs  = DRESTRICT (state_succ_2 s' (DRESTRICT (FST h) vs,SND h)) vs` by(
	     	  `FST h SUBMAP s` by METIS_TAC[graph_plan_lemma_1_1_1_2_4]
		  THEN `varset_action(h, vs)` by FULL_SIMP_TAC(srw_ss())[varset_action_def]
		  THEN METIS_TAC[Q.SPEC`vs`( Q.SPEC `h`( Q.SPEC `s'` ( Q.SPEC `s` (graph_plan_lemma_1_1_1_11_1_1))))])
	     THEN `FDOM (state_succ_2 s h) = FDOM PROB.I` by METIS_TAC[FDOM_state_succ, planning_problem_def]
	     THEN `FDOM (state_succ_2 s' (DRESTRICT (FST h) vs,SND h)) = FDOM PROB.I` by( 
		  `FDOM( SND (DRESTRICT (FST h) vs,SND h)) SUBSET FDOM s'` by FULL_SIMP_TAC(srw_ss())[planning_problem_def]
		  THEN METIS_TAC[FDOM_state_succ])
	     THEN METIS_TAC[] 
	     ,
	     FULL_SIMP_TAC(srw_ss())[]
	     THEN SRW_TAC[][state_list_def]
	     THEN `FST h SUBMAP s` by METIS_TAC[graph_plan_lemma_1_1_1_2_4]
	     THEN METIS_TAC[graph_plan_lemma_1_1_1_11_1_3]	
	]
]
,
Cases_on `as = []`
THENL[
	Cases_on `as'`
	THEN1 SRW_TAC[][]
	THEN FULL_SIMP_TAC(srw_ss())[]
	THEN SRW_TAC[][]
	THEN FULL_SIMP_TAC(srw_ss())[state_list_def]
	THEN `t= []` by METIS_TAC[rich_listTheory.IS_PREFIX_NIL]
	THEN `[h] <<= [h]` by SRW_TAC[][]
	THEN `(FST (LAST [h])) SUBMAP LAST ( state_list (s,[h]))` by SRW_TAC[][state_list_def]
	THEN FULL_SIMP_TAC(srw_ss())[state_list_def]
	THEN SRW_TAC[][]
	THEN METIS_TAC[graph_plan_lemma_1_1_1_11_1_3]	
	,
	`∀as'. (as' ≠ [] ∧ as' ≼ as) ⇒ FST (LAST as') ⊑ LAST (state_list (state_succ_2 s h,as'))` by METIS_TAC[graph_plan_lemma_1_1_1_2_1_1]
	THEN `DRESTRICT (state_succ_2 s h) vs = DRESTRICT s vs` by 
	     (`~varset_action(h,vs)` by FULL_SIMP_TAC(srw_ss())[varset_action_def, planning_problem_def]
	     THEN METIS_TAC[graph_plan_lemma_1_1_1_2_5])
	THEN `FDOM (state_succ_2 s h) = FDOM PROB.I` by FULL_SIMP_TAC(srw_ss())[FDOM_state_succ, planning_problem_def]
	THEN METIS_TAC[]
]
]);

val graph_plan_lemma_1_1_1_14 = store_thm("graph_plan_lemma_1_1_1_14",
``! PROB as s vs . planning_problem(PROB) /\ (set as SUBSET PROB.A) /\ (FDOM s = FDOM PROB.I) /\ (vs SUBSET FDOM(s)) /\ (∀as'. (as' ≠ [] ∧ as' ≼ as) ⇒ (FST (LAST as') ⊑ LAST (state_list (s,as')))) /\ (dep_var_set(PROB, (FDOM PROB.I) DIFF vs, vs)) /\ ~(dep_var_set(PROB, vs,  (FDOM PROB.I) DIFF vs))
==>(∀as'. (as' ≠ [] ∧ as' ≼ ( FILTER (\a. varset_action(a, vs)) (MAP (\ a. ( DRESTRICT (FST a) vs, SND a)) as))) ⇒ (FST (LAST as') ⊑ LAST (state_list (s,as'))))``,
Induct_on`as` 
THEN SRW_TAC[][exec_plan_def]
THENL
[
 Cases_on `as = []`
THENL[
	
	Cases_on `as'`
	THEN1 SRW_TAC[][]
	THEN FULL_SIMP_TAC(srw_ss())[]
	THEN SRW_TAC[][]
	THEN `[h] <<= [h]` by SRW_TAC[][]
	THEN `(FST (LAST [h])) SUBMAP LAST ( state_list (s,[h]))` by SRW_TAC[][state_list_def]
	THEN FULL_SIMP_TAC(srw_ss())[state_list_def]
	THEN `t= []` by METIS_TAC[rich_listTheory.IS_PREFIX_NIL]
	THEN SRW_TAC[][state_list_def]
	THEN METIS_TAC[graph_plan_lemma_1_1_1_11_1_5]	
	,
	`∀as'. (as' ≠ [] ∧ as' ≼ as) ⇒ FST (LAST as') ⊑ LAST (state_list (state_succ_2 s h,as'))` by METIS_TAC[graph_plan_lemma_1_1_1_2_1_1]
	THEN Cases_on `as'`
	THEN1 SRW_TAC[][]
	THEN FULL_SIMP_TAC(srw_ss())[state_list_def]
	THEN SRW_TAC[][]
	THEN Cases_on `t <> []`
	THENL
	[
	     SRW_TAC[][LAST_DEF, empty_state_list_lemma]
	     THEN1 METIS_TAC[empty_state_list_lemma]
	     THEN `FST h SUBMAP s` by METIS_TAC[graph_plan_lemma_1_1_1_2_4]
	     THEN `state_succ_2 s (DRESTRICT (FST h) vs,SND h) = state_succ_2 s h` by METIS_TAC[ graph_plan_lemma_1_1_1_11_1_7]
	     THEN `FDOM (state_succ_2 s h) = FDOM PROB.I` by METIS_TAC[FDOM_state_succ, planning_problem_def]
	     THEN METIS_TAC[]
	     ,
	     FULL_SIMP_TAC(srw_ss())[]
	     THEN SRW_TAC[][state_list_def]
	     THEN `FST h SUBMAP s` by METIS_TAC[graph_plan_lemma_1_1_1_2_4]
	     THEN METIS_TAC[graph_plan_lemma_1_1_1_11_1_5]
	]	
]
,
Cases_on `as = []`
THENL[
	
	FULL_SIMP_TAC(srw_ss())[]
	THEN SRW_TAC[][]
	THEN `as'= []` by METIS_TAC[rich_listTheory.IS_PREFIX_NIL]
	,
	`∀as'. (as' ≠ [] ∧ as' ≼ as) ⇒ FST (LAST as') ⊑ LAST (state_list (state_succ_2 s h,as'))` by METIS_TAC[graph_plan_lemma_1_1_1_2_1_1]
	THEN `FST (LAST as') ⊑ LAST (state_list (state_succ_2 s h,as'))` by (
	     `FDOM (state_succ_2 s h) = FDOM PROB.I` by METIS_TAC[FDOM_state_succ, planning_problem_def]
	     THEN METIS_TAC[])
	THEN `DRESTRICT (state_succ_2 s h) vs = DRESTRICT s vs` by(
	     `~varset_action(h,vs)` by FULL_SIMP_TAC(srw_ss())[varset_action_def, planning_problem_def]
	     THEN METIS_TAC[graph_plan_lemma_1_1_1_2_5])
	THEN `FDOM (state_succ_2 s h) = FDOM PROB.I` by FULL_SIMP_TAC(srw_ss())[FDOM_state_succ, planning_problem_def]
	THEN METIS_TAC[(Q.SPEC `s`(Q.SPEC `state_succ_2 s h`( Q.SPEC `as`( Q.SPEC `vs`(Q.SPEC `PROB` graph_plan_lemma_1_1_1_14_1)))))]
     ]
]);



val graph_plan_lemma_1_1_1_15_1 = store_thm("graph_plan_lemma_1_1_1_15_1",
``! PROB as s vs . planning_problem(PROB) /\ (set as SUBSET PROB.A) /\ (FDOM s = FDOM PROB.I) 
    /\ (vs SUBSET FDOM(s)) 
    /\ (∀as'. (as' ≠ [] ∧ as' ≼ ( FILTER (\a. varset_action(a, vs)) (MAP (\ a. ( DRESTRICT (FST a) vs, SND a)) as)))
	   ⇒ (FST (LAST as') ⊑ LAST (state_list (s,as')))) 
    /\ (dep_var_set(PROB, (FDOM PROB.I) DIFF vs, vs)) /\ ~(dep_var_set(PROB, vs,  (FDOM PROB.I) DIFF vs))
==>  (∀as'. (as' ≠ [] ∧ as' ≼ ( FILTER (\a. varset_action(a, vs)) (MAP (\ a. ( DRESTRICT (FST a) vs, SND a)) as)))
	   ⇒ (FST (LAST as') ⊑ LAST (state_list (DRESTRICT s vs,as'))))``,
Induct_on`as` 
THEN SRW_TAC[][exec_plan_def]
THEN1 METIS_TAC[rich_listTheory.IS_PREFIX_NIL]
THENL
[
 Cases_on `FILTER (λa. varset_action (a,vs)) (MAP (λa. (DRESTRICT (FST a) vs,SND a)) as) = []`
 THENL[
	Cases_on `as'`
	THEN1 SRW_TAC[][]
	THEN FULL_SIMP_TAC(srw_ss())[]
	THEN SRW_TAC[][]
	THEN `[(DRESTRICT (FST h) vs,SND h)] <<= [(DRESTRICT (FST h) vs,SND h)]` by SRW_TAC[][]
	THEN `(FST (LAST [(DRESTRICT (FST h) vs,SND h)])) SUBMAP LAST ( state_list (s,[(DRESTRICT (FST h) vs,SND h)]))` by SRW_TAC[][state_list_def]
	THEN FULL_SIMP_TAC(srw_ss())[state_list_def]
	THEN `t= []` by METIS_TAC[rich_listTheory.IS_PREFIX_NIL]
	THEN SRW_TAC[][state_list_def]
	THEN METIS_TAC[graph_plan_lemma_1_1_1_11_1_6_1]	
	,
	`∀as'. (as' ≠ [] ∧ as' ≼ FILTER (λa. varset_action (a,vs))
             (MAP (λa. (DRESTRICT (FST a) vs,SND a)) as)) ⇒ FST (LAST as') ⊑ LAST (state_list (state_succ_2 s (DRESTRICT (FST h) vs,SND h),as'))` 
	     	  by METIS_TAC[ graph_plan_lemma_1_1_1_2_1_1]
	THEN Cases_on `as'`
	THEN1 SRW_TAC[][]
	THEN FULL_SIMP_TAC(srw_ss())[state_list_def]
	THEN SRW_TAC[][]
	THEN Cases_on `t <> []`
	THENL
	[
 	     SRW_TAC[][LAST_DEF, empty_state_list_lemma]
	     THEN1 METIS_TAC[empty_state_list_lemma]
	     THEN `FST (DRESTRICT (FST h) vs,SND h) SUBMAP s` by METIS_TAC[graph_plan_lemma_1_1_1_2_4]
	     THEN `FDOM (state_succ_2 s (DRESTRICT (FST h) vs,SND h)) = FDOM PROB.I` by FULL_SIMP_TAC(srw_ss())[FDOM_state_succ, planning_problem_def]
	     THEN `DRESTRICT (state_succ_2 s (DRESTRICT (FST h) vs,SND h)) vs = (state_succ_2 (DRESTRICT s vs) (DRESTRICT (FST h) vs,SND h))`
	     	  by( `varset_action(h,vs)` by FULL_SIMP_TAC(srw_ss())[varset_action_def, planning_problem_def]
		     THEN METIS_TAC[graph_plan_lemma_1_1_1_11_1_6, planning_problem_def])
	     THEN METIS_TAC[]
	     ,
	     FULL_SIMP_TAC(srw_ss())[]
	     THEN SRW_TAC[][state_list_def]
	     THEN `FST(DRESTRICT (FST h) vs,SND h)SUBMAP s` by METIS_TAC[graph_plan_lemma_1_1_1_2_4]
	     THEN FULL_SIMP_TAC(srw_ss())[]
	     THEN METIS_TAC[graph_plan_lemma_1_1_1_11_1_6_1]
	]	
]
,
METIS_TAC[]
]);


val graph_plan_lemma_1_1_1_15 = store_thm("graph_plan_lemma_1_1_1_15",
``! PROB as s vs . planning_problem(PROB) /\ (set as SUBSET PROB.A) /\ (FDOM s = FDOM PROB.I) 
    /\ (vs SUBSET FDOM(s)) 
    /\ (∀as'. (as' ≠ [] ∧ as' ≼ as) ⇒ (FST (LAST as') ⊑ LAST (state_list (s,as')))) 
    /\ (dep_var_set(PROB, (FDOM PROB.I) DIFF vs, vs)) /\ ~(dep_var_set(PROB, vs,  (FDOM PROB.I) DIFF vs))
==>(∀as'. (as' ≠ [] ∧ as' ≼ ( FILTER (\a. varset_action(a, vs)) (MAP (\ a. ( DRESTRICT (FST a) vs, SND a)) as)))
	   ⇒ (FST (LAST as') ⊑ LAST (state_list (DRESTRICT s vs,as'))))``,
METIS_TAC[graph_plan_lemma_1_1_1_15_1, graph_plan_lemma_1_1_1_14]
);


val graph_plan_lemma_1_1_1_16_1 = store_thm("graph_plan_lemma_1_1_1_16_1",
``!x. SND ((λa. (DRESTRICT (FST a) vs,SND a)) x) = SND x``,
SRW_TAC[][]
);

val graph_plan_lemma_1_1_1_16_2 = store_thm("graph_plan_lemma_1_1_1_16_2",
``!x y. (SND (x) = SND y)
     ==> ((\a. varset_action(a, vs)) x = (\a. varset_action(a, vs)) y)``,
SRW_TAC[][varset_action_def]
);
val graph_plan_lemma_1_1_1_16 = store_thm("graph_plan_lemma_1_1_1_16",
``!l f1 f2 x. MEM x (MAP f1 l) /\ f2 x /\ (!g. SND (f1 g) = SND g) /\ (!g h. (SND (g) = SND h) ==> (f2 g = f2 h))
     ==>
     ?y. MEM y (l) /\ f2 y``,
SRW_TAC[][]
THEN `?z. MEM z l /\ (x = f1 z)` by METIS_TAC[MEM_MAP ]
THEN METIS_TAC[]
);

val graph_plan_lemma_1_1_1_17_1 = store_thm("graph_plan_lemma_1_1_1_17_1",
``!l1 l2 l3 P. LENGTH (FILTER P l3) < LENGTH (FILTER P l2)
      ==> LENGTH (FILTER P (l1++l3)) < LENGTH (FILTER P (l1++l2))``,
METIS_TAC[LENGTH_APPEND, FILTER_APPEND_DISTRIB, LT_ADD_LCANCEL]);

val graph_plan_lemma_1_1_1_17_2= store_thm("graph_plan_lemma_1_1_1_17_2",
``!l1 l2 l3 P. LENGTH (FILTER P l3) < LENGTH (FILTER P l2)
      ==> LENGTH (FILTER P (l3++l1)) < LENGTH (FILTER P (l2++l1))``,
SRW_TAC[][LENGTH_APPEND, FILTER_APPEND_DISTRIB, LT_ADD_LCANCEL, ADD_SYM]);

val graph_plan_lemma_1_1_1_17 = store_thm("graph_plan_lemma_1_1_1_17",
``!l1 l2 l3 l4 P. LENGTH (FILTER P l2) < LENGTH (FILTER P l3)
      ==> LENGTH (FILTER P (l1++l2++l4)) < LENGTH (FILTER P (l1++l3++l4))``,
SRW_TAC[][LENGTH_APPEND, FILTER_APPEND_DISTRIB, LT_ADD_LCANCEL, ADD_SYM, ADD_ASSOC, graph_plan_lemma_1_1_1_17_1, graph_plan_lemma_1_1_1_17_2]);



val child_parent_lemma_1_1 = store_thm("child_parent_lemma_1_1",
``! a vs. varset_action (a,vs) ==>  (DRESTRICT (SND a) vs = SND a )``,
SRW_TAC[][varset_action_def]
THEN SRW_TAC[][graph_plan_lemma_1_1_1_3_3_2_7]);

val child_parent_lemma_1_2 = store_thm("child_parent_lemma_1_2",
``! PROB a vs. (planning_problem PROB ∧ a IN PROB.A /\ vs ⊆ FDOM PROB.I 
     ∧ dep_var_set (PROB,FDOM PROB.I DIFF vs,vs) ∧¬dep_var_set (PROB,vs,FDOM PROB.I DIFF vs) 
     /\ (FDOM (SND a) <> EMPTY) )
     ==>
     (varset_action(a, vs) <=> ~varset_action(a, FDOM PROB.I DIFF vs))``,
SRW_TAC[][varset_action_def, dep_var_set_def, dep_def, SUBSET_DEF, DISJOINT_DEF, INTER_DEF, EXTENSION, planning_problem_def, SPECIFICATION]
THEN METIS_TAC[]);

val child_parent_lemma_1_3 = store_thm("child_parent_lemma_1_3",
``!x vs. FDOM (DRESTRICT x vs) <> EMPTY  ==> (FDOM  x) <> EMPTY``,
SRW_TAC[][FDOM_DRESTRICT, INTER_DEF, EXTENSION]
THEN METIS_TAC[]);

val child_parent_lemma_1_3 = store_thm("child_parent_lemma_1_3",
``!x vs. FDOM (DRESTRICT x vs) <> EMPTY  ==> (FDOM  x) <> EMPTY``,
SRW_TAC[][FDOM_DRESTRICT, INTER_DEF, EXTENSION]
THEN METIS_TAC[]);

val as_proj_child_parent_def = Define `as_proj_child_parent(as, vs) = 
    (FILTER (λa. varset_action (a,vs) /\ (FDOM (SND a)) <> EMPTY )(MAP (λa. (DRESTRICT (FST a) vs,SND a)) as))`; 


val child_parent_lemma_1 = store_thm("child_parent_lemma_1",
``∀PROB as vs.
     (planning_problem PROB ∧ set as ⊆ PROB.A /\ vs ⊆ FDOM PROB.I 
     ∧ dep_var_set (PROB,FDOM PROB.I DIFF vs,vs) ∧¬dep_var_set (PROB,vs,FDOM PROB.I DIFF vs))
       		   ==>
     (as_proj_child_parent(as,vs) = as_proj(as,vs))``,
Induct_on `as`
THEN SRW_TAC[][as_proj_child_parent_def, as_proj_def]
THENL
[
	FULL_SIMP_TAC(srw_ss())[child_parent_lemma_1_1, varset_action_def]
	,
	METIS_TAC[as_proj_child_parent_def, as_proj_def]
	,
	FULL_SIMP_TAC(srw_ss())[child_parent_lemma_1_1, varset_action_def]	
	,
	FULL_SIMP_TAC(srw_ss())[]
     	THEN `~varset_action(h,vs)` by FULL_SIMP_TAC(srw_ss())[varset_action_def, planning_problem_def]
     	THEN METIS_TAC[graph_plan_lemma_1_1_1_1_1_1, graph_plan_lemma_1_1_1_1_1_4, DISJOINT_DEF, FDOM_DRESTRICT, child_parent_lemma_1_3]
	,
	METIS_TAC[as_proj_child_parent_def, as_proj_def]
]);




val child_parent_lemma_2_1_1_1_1_1_1 = store_thm("child_parent_lemma_2_1_1_1_1_1_1",
``!PROB a vs. ((vs SUBSET FDOM(PROB.I)) /\ dep_var_set(PROB, FDOM(PROB.I) DIFF vs, vs) /\ ~dep_var_set(PROB, vs, FDOM(PROB.I) DIFF vs)) /\ (a IN PROB.A) /\ ~(DISJOINT (FDOM (SND a)) (FDOM(PROB.I) DIFF vs))
==> (DISJOINT  (FDOM (SND a)) vs)``,
SRW_TAC[][dep_var_set_def, dep_def, DISJOINT_DEF, INTER_DEF, EXTENSION]
THEN METIS_TAC[]
);

val child_parent_lemma_2_1_1_1_1_1_3 = store_thm("child_parent_lemma_2_1_1_1_1_1_3",
``!PROB a vs as. ((as <> []) /\  planning_problem(PROB) /\ (vs SUBSET FDOM(PROB.I)) /\ (a IN PROB.A) /\ (MEM a (FILTER (\a. ~varset_action (a,vs)) as)))
    ==> ~(DISJOINT (FDOM (SND a)) (FDOM(PROB.I) DIFF vs))``,
Induct_on`as`
THEN FULL_SIMP_TAC(srw_ss())[DISJOINT_DEF, INTER_DEF, varset_action_def, EXTENSION,FILTER, planning_problem_def, MEM, SUBSET_DEF]
THEN SRW_TAC[][]
THEN1 METIS_TAC[]
THEN Cases_on`as = []`
THEN SRW_TAC[][]
THEN  FULL_SIMP_TAC(srw_ss())[MEM]
THEN METIS_TAC[planning_problem_def]);

val child_parent_lemma_2_1_1_1_1_1_4 = store_thm("child_parent_lemma_2_1_1_1_1_1_4",
``!PROB a vs. (planning_problem(PROB) /\ (vs SUBSET FDOM(PROB.I)) /\ (a IN PROB.A) /\ ( ~varset_action (a,vs)))
    ==> ~(DISJOINT (FDOM (SND a)) (FDOM(PROB.I) DIFF vs))``,
FULL_SIMP_TAC(srw_ss())[DISJOINT_DEF, INTER_DEF, varset_action_def, EXTENSION,FILTER, planning_problem_def, MEM, SUBSET_DEF]
THEN SRW_TAC[][]
THEN METIS_TAC[]);

val child_parent_lemma_2_1_1_1_1_1 = store_thm("child_parent_lemma_2_1_1_1_1_1",
``!PROB s vs a. (planning_problem(PROB) /\ (FDOM s = FDOM PROB.I) /\ (vs SUBSET FDOM PROB.I) /\ (dep_var_set(PROB, (FDOM PROB.I) DIFF vs, vs)) /\ ~(dep_var_set(PROB, vs,  (FDOM PROB.I) DIFF vs)) /\  ¬varset_action (a,vs) /\ (a IN PROB.A))
==> (DRESTRICT (state_succ_2 s a) vs = (DRESTRICT s vs))``,
METIS_TAC[child_parent_lemma_2_1_1_1_1_1_4, graph_plan_lemma_1_1_1_3_3_11_1_1, child_parent_lemma_2_1_1_1_1_1_1]
);

val child_parent_lemma_2_1_1_1_1_2 = store_thm("child_parent_lemma_2_1_1_1_1_2",
``! PROB x y as vs. (planning_problem(PROB) /\ (set as SUBSET PROB.A)  /\ (FDOM x =  FDOM (PROB.I)) /\ (FDOM y = FDOM (PROB.I)) /\ (vs SUBSET FDOM(PROB.I)) /\ dep_var_set (PROB,FDOM PROB.I DIFF vs,vs) /\  ¬dep_var_set (PROB,vs,FDOM PROB.I DIFF vs) /\ (DRESTRICT (x) vs = DRESTRICT y vs)) ==>
(DRESTRICT (exec_plan (x,FILTER (λa. ¬varset_action (a,vs)) as)) vs = DRESTRICT (exec_plan (y ,FILTER (λa. ¬varset_action (a,vs)) as)) vs) ``,
Induct_on`as`
THEN  SRW_TAC [] [exec_plan_def]
THEN `FDOM (state_succ_2 x h) = FDOM (PROB.I)` by METIS_TAC[planning_problem_def, FDOM_state_succ]
THEN `FDOM (state_succ_2 y h) = FDOM (PROB.I)` by METIS_TAC[planning_problem_def, FDOM_state_succ]
THEN METIS_TAC[child_parent_lemma_2_1_1_1_1_1]
);


val child_parent_lemma_2_1_1_1_1_3 = store_thm("child_parent_lemma_2_1_1_1_1_3",
``! PROB s as vs. (planning_problem(PROB) /\ (set as SUBSET PROB.A)  /\ (FDOM s =  FDOM (PROB.I)) /\ (vs SUBSET FDOM(PROB.I)) 
    	      	  /\ dep_var_set (PROB,FDOM PROB.I DIFF vs,vs) /\  ¬dep_var_set (PROB,vs,FDOM PROB.I DIFF vs)) 
	==>
	((DRESTRICT s vs) = (DRESTRICT (exec_plan (s,FILTER (λa. ¬varset_action (a,vs)) as)) vs))``,
Induct_on`as`
THEN  SRW_TAC [] [exec_plan_def]
THEN METIS_TAC[child_parent_lemma_2_1_1_1_1_1_4, graph_plan_lemma_1_1_1_3_3_11_1_1, child_parent_lemma_2_1_1_1_1_1_1, child_parent_lemma_2_1_1_1_1_2, planning_problem_def, FDOM_state_succ] 
);


val child_parent_lemma_2_1_1_1_1 = store_thm("child_parent_lemma_2_1_1_1_1",
``!PROB s as vs. (planning_problem(PROB) /\ (FDOM s = FDOM PROB.I) /\ (set as SUBSET PROB.A) /\ (vs SUBSET FDOM PROB.I) 
	    /\ (dep_var_set(PROB, (FDOM PROB.I) DIFF vs, vs)) /\ ~(dep_var_set(PROB, vs,  (FDOM PROB.I) DIFF vs))
	    /\ ((DRESTRICT s vs) = (DRESTRICT (exec_plan(s,as)) vs))) 
     	    ==>
            ((DRESTRICT (exec_plan(s,as)) vs) = (DRESTRICT (exec_plan (s,FILTER (\a. ~varset_action (a,vs)) as)) vs))``,
METIS_TAC[child_parent_lemma_2_1_1_1_1_3]);



val child_parent_lemma_2_1_1_1_2 = store_thm("child_parent_lemma_2_1_1_1_2",
``!P l. (?x. MEM x l /\ P x) 
==> LENGTH(FILTER (\x. ~ (P x)) l) < LENGTH(l)``,
Induct_on`l`
THEN SRW_TAC[][]
THEN ASSUME_TAC (Q.SPEC `l` (Q.SPEC `(λx. ¬P x)` rich_listTheory.LENGTH_FILTER_LEQ))
THENL
[
	METIS_TAC[]
	,
	METIS_TAC[]
	,
	DECIDE_TAC
	,
	DECIDE_TAC
]);

val child_parent_lemma_2_1_1_1_3_1 = store_thm("child_parent_lemma_2_1_1_1_3_1",
``!P l. LENGTH (FILTER (\a. P a) (FILTER (\a. ~P a)  l  )) = 0``,
Induct_on`l`
THEN  SRW_TAC[][]
);

val child_parent_lemma_2_1_1_1_3 = store_thm("child_parent_lemma_2_1_1_1_3",
``!P l. (?a. (MEM a l /\ P a )) ==> 
LENGTH (FILTER (\a. P a) (FILTER (\a. ~P a)  l  )) < LENGTH ((FILTER (\a. P a)  l  ))``,
Induct_on`l`
THEN SRW_TAC[][]
THENL
[
	METIS_TAC[]
	,
	METIS_TAC[]
	,
	METIS_TAC[]
	,
	METIS_TAC[]
	,
	Q_TAC SUFF_TAC `LENGTH (FILTER (λa. ~P a) (FILTER (λa. P a) l)) < SUC (LENGTH (FILTER (λa. P a) l))` 
	THEN1 METIS_TAC[FILTER_COMM]
	THEN 
	`LENGTH (FILTER (λa. ¬P a) (FILTER (λa. P a) l)) <= LENGTH (FILTER (λa. P a) l)` by METIS_TAC[rich_listTheory.LENGTH_FILTER_LEQ]
	THEN `!x y. x <= y ==> x < SUC y` by DECIDE_TAC 
	THEN METIS_TAC[]
	,
	`!x y. x< y ==> x <  SUC y` by DECIDE_TAC
	THEN METIS_TAC[]
]);


val child_parent_lemma_2_1_1_1 = store_thm("child_parent_lemma_2_1_1_1",
``!PROB s as vs. (planning_problem(PROB) /\ (FDOM s = FDOM PROB.I) /\ (set as SUBSET PROB.A) /\ (vs SUBSET FDOM PROB.I) 
	    /\ (dep_var_set(PROB, (FDOM PROB.I) DIFF vs, vs)) /\ ~(dep_var_set(PROB, vs,  (FDOM PROB.I) DIFF vs))
	    /\ ((DRESTRICT s vs) = (DRESTRICT (exec_plan(s,as)) vs))
	    /\ (?a. MEM a as /\ ((\a. varset_action(a,vs)) a))) 
     	    ==>
            ( ((DRESTRICT (exec_plan(s,as)) vs) = (DRESTRICT (exec_plan (s,FILTER (\a. ~varset_action (a,vs)) as)) vs)) /\ (LENGTH( FILTER (\a. varset_action(a,vs)) (FILTER (\a. ~(\a.varset_action(a,vs)) a)  as)) < LENGTH(FILTER (\a. varset_action(a,vs)) as)) )``,
METIS_TAC[child_parent_lemma_2_1_1_1_1, (Q.SPEC `as` (Q.ISPEC `(\a. varset_action(a,vs))` child_parent_lemma_2_1_1_1_3))]);



val child_parent_lemma_2_1_1_** =  (" child_parent_lemma_2_1_1_**", (* previously graph_plan_lemma_1_1_1_5_5*)
``!PROB as vs. (plan_2(PROB, as) 
  /\ sat_precond_as(PROB.I, as) 
 /\ (vs SUBSET FDOM(PROB.I)) /\ dep_var_set(PROB, (FDOM PROB.I) DIFF vs, vs  )  /\ ~dep_var_set(PROB, vs, (FDOM PROB.I) DIFF vs))
==> plan_2(prob_proj(PROB,vs), as_proj_child_parent(as, vs) )``,
METIS_TAC[child_parent_lemma_1, plan_def_2, graph_plan_lemma_1_1_1_3_3_ , sat_precond_as_def]);


val child_parent_lemma_2_1_1 = store_thm("child_parent_lemma_2_1_1",
``!PROB vs as s.
	  (planning_problem(PROB) /\ (FDOM s = FDOM PROB.I) 	   
	  /\ (set as SUBSET PROB.A) /\ (vs SUBSET FDOM PROB.I)
	  /\ (dep_var_set(PROB, (FDOM PROB.I) DIFF vs, vs)) /\ ~(dep_var_set(PROB, vs,  (FDOM PROB.I) DIFF vs)))
	  ==>
	  (?as'. (exec_plan(s, as') = exec_plan(s, as))
	  /\ (LENGTH( FILTER (\a. varset_action(a, vs)) as')) <= (2**CARD(vs)))``,
SRW_TAC[][]
THEN `(∀p.
      (λas''. (exec_plan (s,as'') = exec_plan (s,as)) ∧ set as'' ⊆ PROB.A)  p ∧

      (λas''. LENGTH (FILTER (λa. varset_action (a,vs)) as'')) p > 2 ** CARD vs
       ⇒
      ∃p'.
        (λas''.
           (exec_plan (s,as'') = exec_plan (s,as)) ∧ set as'' ⊆ PROB.A) p' ∧
	   
        (λas''. LENGTH (FILTER (λa. varset_action (a,vs)) as'')) p' < 
	  (λas''. LENGTH (FILTER (λa. varset_action (a,vs)) as'')) p)` by
      (SRW_TAC[][]
      THEN `(exec_plan (s,p) = exec_plan (s,rem_condless_act (s,[],p))) ∧ 
      (∀as'. as' ≠ [] ∧ as' ≼ rem_condless_act (s,[],p) ⇒FST (LAST as') ⊑ LAST (state_list (s,as'))) ∧
      LENGTH (rem_condless_act (s,[],p)) ≤ LENGTH p ∧
      set (rem_condless_act (s,[],p)) ⊆ PROB.A
      /\ LENGTH (rem_condless_act (s,[],p)) ≤ LENGTH p
      /\ ∀P. LENGTH (FILTER P (rem_condless_act (s,[],p))) ≤ LENGTH (FILTER P p)` by (SRW_TAC[][] THEN METIS_TAC[Q.SPEC `s`( Q.SPEC `PROB` (Q.SPEC `p` graph_plan_lemma_1_1_1_9))])
      THEN Cases_on `LENGTH (FILTER (λa. varset_action (a,vs)) ( (rem_condless_act (s,[],p)))) > 2 ** CARD(vs)` 
      THENL
      [
	      `(∃as1 as2 as3. 
	      	   (as1++as2++as3=(FILTER (\a. varset_action(a, vs)) (MAP (\ a. ( DRESTRICT (FST a) vs, SND a)) (rem_condless_act (s,[],p))))) 
	      	   ∧((exec_plan((prob_proj(PROB with <|G := exec_plan (s,(rem_condless_act (s,[],p))); I := s|>, vs)).I,as1 ++ as2) 
		   		= exec_plan ((prob_proj(PROB with <|G := exec_plan (s,(rem_condless_act (s,[],p))); I := s|>, vs)).I,
				  	    as1)) ∧ (as2 ≠ [])))` by
		   (`LENGTH (FILTER (λa. varset_action (a,vs)) (MAP (λa. (DRESTRICT (FST a) vs,SND a)) (rem_condless_act (s,[],p)))) > 2 ** CARD(vs)` by METIS_TAC[graph_plan_lemma_1_1_1_4]
		   THEN `plan_2(PROB with <|G := exec_plan (s,rem_condless_act (s,[],p)); I := s|>, rem_condless_act (s,[],p))` by METIS_TAC[ (Q.SPEC`s`(Q.SPEC `PROB`(Q.SPEC `(rem_condless_act (s,[],p))` graph_plan_lemma_1_1_1_8)))]   	    
	      	   THEN `vs SUBSET FDOM ((PROB with <|G := exec_plan (s,(rem_condless_act (s,[],p))); I := s|>).I)` by SRW_TAC[][]
     	      	   THEN `dep_var_set (PROB with <|G := exec_plan (s,(rem_condless_act (s,[],p))); I := s|>,FDOM (PROB with <|G := exec_plan (s,(rem_condless_act (s,[],p))); I := s|>).I DIFF vs,vs)` by 
	      	   	(FULL_SIMP_TAC(srw_ss())[dep_var_set_def, dep_def] 
 	      	   	THEN METIS_TAC[])
 	      	   THEN `¬dep_var_set (PROB with <|G := exec_plan (s,(rem_condless_act (s,[],p))); I := s|>,vs,FDOM (PROB with <|G := exec_plan (s,(rem_condless_act (s,[],p))); I := s|>).I DIFF vs)` by 
	      	   	(FULL_SIMP_TAC(srw_ss())[dep_var_set_def, dep_def] 
 	      	   	THEN METIS_TAC[])
		   THEN SRW_TAC[][graph_plan_lemma_1_1_1_3])	      
     	      THEN `(exec_plan ((exec_plan(DRESTRICT s vs, as1)), as2) = (exec_plan(DRESTRICT s vs, as1)) )`by	
	      	   (`exec_plan((prob_proj (PROB with <|G := exec_plan (s,(rem_condless_act (s,[],p))); I := s|>,vs)). I,as1 ++ as2)
	              = exec_plan (DRESTRICT s vs, as1 ++as2)`     by FULL_SIMP_TAC(srw_ss())[prob_proj_def]
	      	    THEN `exec_plan((prob_proj (PROB with <|G := exec_plan (s,(rem_condless_act (s,[],p))); I := s|>,vs)). I,as1) = (exec_plan(DRESTRICT s vs, as1)) ` by FULL_SIMP_TAC(srw_ss())[prob_proj_def]
	      	    THEN `(exec_plan (DRESTRICT s vs, as1 ++as2) = (exec_plan(DRESTRICT s vs, as1)) )`by FULL_SIMP_TAC(srw_ss())[prob_proj_def]
	      	    THEN FULL_SIMP_TAC(srw_ss())[exec_plan_Append])
	      THEN `?p_1 p_2 p_3. (p_1 ++ p_2 ++ p_3 = (rem_condless_act (s,[],p))) /\ (as2 = FILTER (\a. varset_action(a, vs)) (MAP (\ a. ( DRESTRICT (FST a) vs, SND a)) p_2)) /\ (as1 = FILTER (\a. varset_action(a, vs)) (MAP (\ a. ( DRESTRICT (FST a) vs, SND a)) p_1))` by METIS_TAC[graph_plan_lemma_1_1_1_10]
	      THEN `set (p_1) SUBSET PROB.A` by( FULL_SIMP_TAC(srw_ss())[] THEN SRW_TAC[][] THEN METIS_TAC[LIST_TO_SET_APPEND, APPEND_ASSOC, UNION_SUBSET])
	      THEN `set (p_2) SUBSET PROB.A` by (SRW_TAC[][] THEN FULL_SIMP_TAC(srw_ss())[] THEN METIS_TAC[LIST_TO_SET_APPEND, APPEND_ASSOC, UNION_SUBSET])
 	      THEN `set (p_3) SUBSET PROB.A` by (SRW_TAC[][] THEN FULL_SIMP_TAC(srw_ss())[] THEN METIS_TAC[LIST_TO_SET_APPEND, APPEND_ASSOC, UNION_SUBSET])
	      THEN `∀as'. as' ≠ [] ∧ as' ≼ p_1++p_2++p_3 ⇒ FST (LAST as') ⊑ LAST(state_list(s, as'))` by FULL_SIMP_TAC(srw_ss())[] 	    
	      THEN `(∀as'. as' ≠ [] ∧ as' ≼ p_1  ⇒ FST (LAST as') ⊑ LAST (state_list (s, as'))) /\
	      	   (∀as'. as' ≠ [] ∧ as' ≼ p_2++p_3  ⇒ FST (LAST as') ⊑ LAST (state_list (exec_plan(s, p_1),as')))` by 
	      	   (`(p_1 ++ p_2 ++ p_3) <> [] ` by (SRW_TAC[][MAP_EQ_NIL, FILTER_NEQ_NIL]
		   	  	      THEN `p_2 <> []` by (SRW_TAC[][MAP_EQ_NIL, FILTER_NEQ_NIL] THEN METIS_TAC[MAP_EQ_NIL, FILTER_NEQ_NIL, NOT_NULL_MEM, NULL_DEF])
			  	      THEN METIS_TAC[])
		   THEN METIS_TAC[graph_plan_lemma_1_1_1_2_1, APPEND_ASSOC])
	      THEN `∀as'. as' ≠ [] ∧ as' ≼ p_2  ⇒ FST (LAST as') ⊑ LAST (state_list (exec_plan(s, p_1),as'))` by 
	      	   (`(p_2 ++ p_3) <> [] ` by (SRW_TAC[][MAP_EQ_NIL, FILTER_NEQ_NIL]
		   	 THEN `p_2 <> []` by (SRW_TAC[][MAP_EQ_NIL, FILTER_NEQ_NIL] THEN METIS_TAC[MAP_EQ_NIL, FILTER_NEQ_NIL, NOT_NULL_MEM, NULL_DEF])
			 THEN METIS_TAC[])
		   THEN METIS_TAC[graph_plan_lemma_1_1_1_2_1, APPEND_ASSOC])   
	      THEN `(exec_plan (DRESTRICT (exec_plan (s,as1)) vs,as2)) = DRESTRICT (exec_plan (s,as1)) vs` by METIS_TAC[graph_plan_lemma_1_1_1_11]
  	      THEN `FDOM( exec_plan (s,as1)) = FDOM s` by(METIS_TAC[graph_plan_lemma_1_1_1_12])		  
	      THEN `(∀as'. as' ≠ [] ∧ as' ≼ as2 ⇒ FST (LAST as') ⊑ LAST (state_list ( (exec_plan(s, p_1)) ,as')))` by 
				    (`FDOM( exec_plan (s,p_1)) = FDOM s` by( METIS_TAC[graph_plan_lemma_1_1_1_8_1])
				    THEN `DRESTRICT (exec_plan(s, as1)) vs = DRESTRICT (exec_plan(s, p_1)) vs` by METIS_TAC[graph_plan_lemma_1_1_1_13]
				    THEN METIS_TAC[graph_plan_lemma_1_1_1_15, graph_plan_lemma_1_1_1_14])	    	     
	      THEN `exec_plan (DRESTRICT (exec_plan (s,p_1)) vs,as2) =  DRESTRICT (exec_plan (s,p_1)) vs` by METIS_TAC[graph_plan_lemma_1_1_1_13]
 	      THEN `FDOM(exec_plan (s,p_1)) = FDOM s` by (METIS_TAC[graph_plan_lemma_1_1_1_8_1])
	      THEN `DRESTRICT(exec_plan ( (exec_plan (s,p_1)) ,p_2)) vs =  DRESTRICT (exec_plan (s,p_1)) vs` by 
		   	(METIS_TAC[Q.SPEC `p_2`( Q.SPEC `vs` ( Q.SPEC `(exec_plan (s,p_1))` ( Q.SPEC `(exec_plan (s,p_1))` ( Q.SPEC `PROB` graph_plan_lemma_1_1_1_2))))])
	      THEN `(DRESTRICT (exec_plan (exec_plan (s,p_1),p_2)) vs = DRESTRICT (exec_plan (exec_plan (s,p_1),FILTER (λa. ¬varset_action (a,vs)) p_2)) vs)
	      	   /\ LENGTH ( FILTER (λa. varset_action (a,vs)) (FILTER (λa. ¬varset_action (a,vs)) p_2)) < LENGTH (FILTER (λa. varset_action (a,vs)) p_2)` by 
		   	(`(∃a. MEM a p_2 ∧ (λa. varset_action (a,vs)) a)` by 
			       (`(∃a. MEM a (MAP (λa. (DRESTRICT (FST a) vs,SND a)) p_2) ∧ (λa. varset_action (a,vs)) a) ` by METIS_TAC[Q.SPEC `(MAP (λa. (DRESTRICT (FST a) vs,SND a)) p_2)` ( Q.ISPEC `(λa. varset_action (a,vs))` FILTER_NEQ_NIL) ]
			       THEN METIS_TAC[Q.SPEC`a`( Q.ISPEC `(\a. varset_action(a,vs))` ( Q.ISPEC `(λa. (DRESTRICT (FST a) vs,SND a))` ( Q.SPEC `p_2` graph_plan_lemma_1_1_1_16))), graph_plan_lemma_1_1_1_16_1, graph_plan_lemma_1_1_1_16_2])
			THEN METIS_TAC[graph_plan_lemma_1_1_1_1])
	      THEN `LENGTH (FILTER (λa. varset_action (a,vs)) ( p_1 ++ (FILTER (λa. ¬varset_action (a,vs)) p_2) ++ p_3)) < LENGTH (FILTER (λa. varset_action (a,vs)) (p_1 ++ p_2 ++ p_3))` by METIS_TAC[graph_plan_lemma_1_1_1_17]
	      THEN `set (( p_1 ++ (FILTER (λa. ¬varset_action (a,vs)) p_2) ++ p_3)) SUBSET PROB.A` by SRW_TAC[][graph_plan_lemma_1_1_1_8_2]
    	      THEN `(DRESTRICT (exec_plan (exec_plan (s,p_1),p_2)) (FDOM s DIFF vs) = DRESTRICT (exec_plan (exec_plan (s,p_1),FILTER (λa. ¬varset_action (a,vs)) p_2)) (FDOM s DIFF vs))` by SRW_TAC[][graph_plan_lemma_1_1_1_6]
	      THEN `exec_plan (exec_plan (s,p_1), p_2) = exec_plan (exec_plan (s,p_1),FILTER (λa. ¬varset_action (a,vs)) p_2)` by 
	      	   	(`FDOM(exec_plan (exec_plan(s, p_1), p_2)) = FDOM s` by SRW_TAC[][graph_plan_lemma_1_1_1_8_1]
			THEN `FDOM(exec_plan (exec_plan(s, p_1),FILTER (λa. ¬varset_action (a,vs)) p_2)) = FDOM s` by SRW_TAC[][graph_plan_lemma_1_1_1_8_1, graph_plan_lemma_1_1_1_8_2]
			THEN METIS_TAC[graph_plan_lemma_1_1_1_7])
	      THEN `exec_plan (s,rem_condless_act (s,[],p)) = exec_plan (s,p_1 ++ FILTER (λa. ¬varset_action (a,vs)) p_2 ++ p_3)` by  
	      	   (`exec_plan (s,p_1++ p_2++p_3) = exec_plan (s,p_1 ++ FILTER (λa. ¬varset_action (a,vs)) p_2 ++ p_3)` by FULL_SIMP_TAC(srw_ss())[exec_plan_Append]
		   THEN SRW_TAC[][] THEN METIS_TAC[])
	      THEN `exec_plan (s,p) = exec_plan (s,p_1 ++ FILTER (λa. ¬varset_action (a,vs)) p_2 ++ p_3)` by (
	      	   `exec_plan (s,p_1++ p_2++p_3) = exec_plan (s,p_1 ++ FILTER (λa. ¬varset_action (a,vs)) p_2 ++ p_3)` by FULL_SIMP_TAC(srw_ss())[exec_plan_Append]
	      	   THEN `exec_plan (s,rem_condless_act (s,[],p)) = exec_plan (s,p_1 ++ FILTER (λa. ¬varset_action (a,vs)) p_2 ++ p_3)` by (SRW_TAC[][] THEN METIS_TAC[])
		   THEN SRW_TAC[][] THEN METIS_TAC[])
	      THEN `LENGTH (FILTER (λa. varset_action (a,vs)) (p_1 ++ p_2 ++ p_3)) <= LENGTH (FILTER (λa. varset_action (a,vs)) (p))` by SRW_TAC[][]
	      THEN `LENGTH (FILTER (λa. varset_action (a,vs)) (p_1 ++ FILTER (λa. ¬varset_action (a,vs)) p_2 ++ p_3))
	      	    < LENGTH (FILTER (λa. varset_action (a,vs)) (p))` by
		    (`LENGTH (FILTER (λa. varset_action (a,vs)) (p_1 ++ p_2 ++ p_3)) <= LENGTH (FILTER (λa. varset_action (a,vs)) (p))` by SRW_TAC[][]
		    THEN DECIDE_TAC)
	      THEN METIS_TAC[]
	      ,
	      `(LENGTH (FILTER (λa. varset_action (a,vs)) (rem_condless_act (s,[],p))) <= 2 ** CARD vs)` by DECIDE_TAC
	      THEN `LENGTH (FILTER (λa. varset_action (a,vs)) (rem_condless_act (s,[],p))) < LENGTH (FILTER (λa. varset_action (a,vs)) p)` by DECIDE_TAC
	      THEN METIS_TAC[]                  
	      ])
THEN ASSUME_TAC(Q.SPEC  `2 ** CARD vs` (Q.ISPEC `(λas''. LENGTH (FILTER (λa. varset_action (a,vs)) as''))` ( Q.ISPEC `(λas''. (exec_plan (s,as'') = exec_plan (s,as)) ∧ set as'' ⊆ PROB.A)` general_theorem)))
THEN METIS_TAC[]
);  


Q.SPEC  `(2**CARD((FDOM PROB.I) DIFF vs))` (Q.ISPEC `(λas''. LENGTH (FILTER (λa. varset_action (a,vs)) as''))` ( Q.ISPEC `(λas''. (exec_plan (s,as'') = exec_plan (s,as)) ∧ set as'' ⊆ PROB.A /\ (!a. MEM a as ==> varset_action(a, (FDOM PROB.I) DIFF vs)))` general_theorem))

val child_parent_lemma_2_1_2 = store_thm("child_parent_lemma_2_1_2",
``!PROB vs as s.
	  (planning_problem(PROB) /\ (FDOM s = FDOM PROB.I) 	   
	  /\ (set as SUBSET PROB.A) /\ (vs SUBSET FDOM PROB.I)
	  /\ (dep_var_set(PROB, (FDOM PROB.I) DIFF vs, vs)) /\ ~(dep_var_set(PROB, vs,  (FDOM PROB.I) DIFF vs))
	  /\ (!a. MEM a as ==> varset_action(a, (FDOM PROB.I) DIFF vs)))
	  ==>
	  (?as'. (exec_plan(s, as') = exec_plan(s, as))
	  /\ (LENGTH(as') <= (2**CARD((FDOM PROB.I) DIFF vs))))``,
SRW_TAC[][]
THEN `(∀p.
      (λas''.
         (exec_plan (s,as'') = exec_plan (s,as)) ∧ set as'' ⊆ PROB.A ∧
         ∀a. MEM a as ⇒ varset_action (a,FDOM PROB.I DIFF vs)) p ∧
      (λas''. LENGTH (FILTER (λa. varset_action (a,vs)) as'')) p >
      2 ** CARD (FDOM PROB.I DIFF vs) ⇒
      ∃p'.
        (λas''.
           (exec_plan (s,as'') = exec_plan (s,as)) ∧ set as'' ⊆ PROB.A ∧
           ∀a. MEM a as ⇒ varset_action (a,FDOM PROB.I DIFF vs)) p' ∧
        (λas''. LENGTH (FILTER (λa. varset_action (a,vs)) as'')) p' <
        (λas''. LENGTH (FILTER (λa. varset_action (a,vs)) as'')) p)` by REWRITE_TAC[]
      (SRW_TAC[][]
      THEN `(exec_plan (s,p) = exec_plan (s,rem_condless_act (s,[],p))) ∧ 
      (∀as'. as' ≠ [] ∧ as' ≼ rem_condless_act (s,[],p) ⇒FST (LAST as') ⊑ LAST (state_list (s,as'))) ∧
      LENGTH (rem_condless_act (s,[],p)) ≤ LENGTH p ∧
      set (rem_condless_act (s,[],p)) ⊆ PROB.A
      /\ LENGTH (rem_condless_act (s,[],p)) ≤ LENGTH p
      /\ ∀P. LENGTH (FILTER P (rem_condless_act (s,[],p))) ≤ LENGTH (FILTER P p)` by (SRW_TAC[][] THEN METIS_TAC[Q.SPEC `s`( Q.SPEC `PROB` (Q.SPEC `p` graph_plan_lemma_1_1_1_9))])
      THEN Cases_on `LENGTH (FILTER (λa. varset_action (a,vs)) ( (rem_condless_act (s,[],p)))) > 2 ** CARD (FDOM PROB.I DIFF vs)` 
      THENL
      [
	      `(∃as1 as2 as3. 
	      	   (as1++as2++as3=(FILTER (\a. varset_action(a, vs)) (MAP (\ a. ( DRESTRICT (FST a) vs, SND a)) (rem_condless_act (s,[],p))))) 
	      	   ∧((exec_plan((prob_proj(PROB with <|G := exec_plan (s,(rem_condless_act (s,[],p))); I := s|>, vs)).I,as1 ++ as2) 
		   		= exec_plan ((prob_proj(PROB with <|G := exec_plan (s,(rem_condless_act (s,[],p))); I := s|>, vs)).I,
				  	    as1)) ∧ (as2 ≠ [])))` by REWRITE_TAC[]
		   (`LENGTH (FILTER (λa. varset_action (a,vs)) (MAP (λa. (DRESTRICT (FST a) vs,SND a)) (rem_condless_act (s,[],p)))) > 2 ** CARD (FDOM PROB.I DIFF vs)` by METIS_TAC[graph_plan_lemma_1_1_1_4]
		   THEN `plan_2(PROB with <|G := exec_plan (s,rem_condless_act (s,[],p)); I := s|>, rem_condless_act (s,[],p))` by METIS_TAC[ (Q.SPEC`s`(Q.SPEC `PROB`(Q.SPEC `(rem_condless_act (s,[],p))` graph_plan_lemma_1_1_1_8)))]
	      	   THEN `(FDOM PROB.I DIFF vs) SUBSET FDOM ((PROB with <|G := exec_plan (s,(rem_condless_act (s,[],p))); I := s|>).I)` by SRW_TAC[][]
     	      	   THEN `dep_var_set (PROB with <|G := exec_plan (s,(rem_condless_act (s,[],p))); I := s|>,FDOM (PROB with <|G := exec_plan (s,(rem_condless_act (s,[],p))); I := s|>).I DIFF vs,vs)` by 
	      	   	(FULL_SIMP_TAC(srw_ss())[dep_var_set_def, dep_def] 
 	      	   	THEN METIS_TAC[])
 	      	   THEN `¬dep_var_set (PROB with <|G := exec_plan (s,(rem_condless_act (s,[],p))); I := s|>,vs,FDOM (PROB with <|G := exec_plan (s,(rem_condless_act (s,[],p))); I := s|>).I DIFF vs)` by 
	      	   	(FULL_SIMP_TAC(srw_ss())[dep_var_set_def, dep_def] 
 	      	   	THEN METIS_TAC[])
		   THEN SRW_TAC[][graph_plan_lemma_1_1_1_3])	      
     	      THEN `(exec_plan ((exec_plan(DRESTRICT s vs, as1)), as2) = (exec_plan(DRESTRICT s vs, as1)) )`by	
	      	   (`exec_plan((prob_proj (PROB with <|G := exec_plan (s,(rem_condless_act (s,[],p))); I := s|>,vs)). I,as1 ++ as2)
	              = exec_plan (DRESTRICT s vs, as1 ++as2)`     by FULL_SIMP_TAC(srw_ss())[prob_proj_def]
	      	    THEN `exec_plan((prob_proj (PROB with <|G := exec_plan (s,(rem_condless_act (s,[],p))); I := s|>,vs)). I,as1) = (exec_plan(DRESTRICT s vs, as1)) ` by FULL_SIMP_TAC(srw_ss())[prob_proj_def]
	      	    THEN `(exec_plan (DRESTRICT s vs, as1 ++as2) = (exec_plan(DRESTRICT s vs, as1)) )`by FULL_SIMP_TAC(srw_ss())[prob_proj_def]
	      	    THEN FULL_SIMP_TAC(srw_ss())[exec_plan_Append])
	      THEN `?p_1 p_2 p_3. (p_1 ++ p_2 ++ p_3 = (rem_condless_act (s,[],p))) /\ (as2 = FILTER (\a. varset_action(a, vs)) (MAP (\ a. ( DRESTRICT (FST a) vs, SND a)) p_2)) /\ (as1 = FILTER (\a. varset_action(a, vs)) (MAP (\ a. ( DRESTRICT (FST a) vs, SND a)) p_1))` by METIS_TAC[graph_plan_lemma_1_1_1_10]
	      THEN `set (p_1) SUBSET PROB.A` by( FULL_SIMP_TAC(srw_ss())[] THEN SRW_TAC[][] THEN METIS_TAC[LIST_TO_SET_APPEND, APPEND_ASSOC, UNION_SUBSET])
	      THEN `set (p_2) SUBSET PROB.A` by (SRW_TAC[][] THEN FULL_SIMP_TAC(srw_ss())[] THEN METIS_TAC[LIST_TO_SET_APPEND, APPEND_ASSOC, UNION_SUBSET])
 	      THEN `set (p_3) SUBSET PROB.A` by (SRW_TAC[][] THEN FULL_SIMP_TAC(srw_ss())[] THEN METIS_TAC[LIST_TO_SET_APPEND, APPEND_ASSOC, UNION_SUBSET])
	      THEN `∀as'. as' ≠ [] ∧ as' ≼ p_1++p_2++p_3 ⇒ FST (LAST as') ⊑ LAST(state_list(s, as'))` by FULL_SIMP_TAC(srw_ss())[] 	    
	      THEN `(∀as'. as' ≠ [] ∧ as' ≼ p_1  ⇒ FST (LAST as') ⊑ LAST (state_list (s, as'))) /\
	      	   (∀as'. as' ≠ [] ∧ as' ≼ p_2++p_3  ⇒ FST (LAST as') ⊑ LAST (state_list (exec_plan(s, p_1),as')))` by 
	      	   (`(p_1 ++ p_2 ++ p_3) <> [] ` by (SRW_TAC[][MAP_EQ_NIL, FILTER_NEQ_NIL]
		   	  	      THEN `p_2 <> []` by (SRW_TAC[][MAP_EQ_NIL, FILTER_NEQ_NIL] THEN METIS_TAC[MAP_EQ_NIL, FILTER_NEQ_NIL, NOT_NULL_MEM, NULL_DEF])
			  	      THEN METIS_TAC[])
		   THEN METIS_TAC[graph_plan_lemma_1_1_1_2_1, APPEND_ASSOC])
	      THEN `∀as'. as' ≠ [] ∧ as' ≼ p_2  ⇒ FST (LAST as') ⊑ LAST (state_list (exec_plan(s, p_1),as'))` by 
	      	   (`(p_2 ++ p_3) <> [] ` by (SRW_TAC[][MAP_EQ_NIL, FILTER_NEQ_NIL]
		   	 THEN `p_2 <> []` by (SRW_TAC[][MAP_EQ_NIL, FILTER_NEQ_NIL] THEN METIS_TAC[MAP_EQ_NIL, FILTER_NEQ_NIL, NOT_NULL_MEM, NULL_DEF])
			 THEN METIS_TAC[])
		   THEN METIS_TAC[graph_plan_lemma_1_1_1_2_1, APPEND_ASSOC])   
	      THEN `(exec_plan (DRESTRICT (exec_plan (s,as1)) vs,as2)) = DRESTRICT (exec_plan (s,as1)) vs` by METIS_TAC[graph_plan_lemma_1_1_1_11]
  	      THEN `FDOM( exec_plan (s,as1)) = FDOM s` by(METIS_TAC[graph_plan_lemma_1_1_1_12])		  
	      THEN `(∀as'. as' ≠ [] ∧ as' ≼ as2 ⇒ FST (LAST as') ⊑ LAST (state_list ( (exec_plan(s, p_1)) ,as')))` by 
				    (`FDOM( exec_plan (s,p_1)) = FDOM s` by( METIS_TAC[graph_plan_lemma_1_1_1_8_1])
				    THEN `DRESTRICT (exec_plan(s, as1)) vs = DRESTRICT (exec_plan(s, p_1)) vs` by METIS_TAC[graph_plan_lemma_1_1_1_13]
				    THEN METIS_TAC[graph_plan_lemma_1_1_1_15, graph_plan_lemma_1_1_1_14])	    	     
	      THEN `exec_plan (DRESTRICT (exec_plan (s,p_1)) vs,as2) =  DRESTRICT (exec_plan (s,p_1)) vs` by METIS_TAC[graph_plan_lemma_1_1_1_13]
 	      THEN `FDOM(exec_plan (s,p_1)) = FDOM s` by (METIS_TAC[graph_plan_lemma_1_1_1_8_1])
	      THEN `DRESTRICT(exec_plan ( (exec_plan (s,p_1)) ,p_2)) vs =  DRESTRICT (exec_plan (s,p_1)) vs` by 
		   	(METIS_TAC[Q.SPEC `p_2`( Q.SPEC `vs` ( Q.SPEC `(exec_plan (s,p_1))` ( Q.SPEC `(exec_plan (s,p_1))` ( Q.SPEC `PROB` graph_plan_lemma_1_1_1_2))))])
	      THEN `(DRESTRICT (exec_plan (exec_plan (s,p_1),p_2)) vs = DRESTRICT (exec_plan (exec_plan (s,p_1),FILTER (λa. ¬varset_action (a,vs)) p_2)) vs)
	      	   /\ LENGTH ( FILTER (λa. varset_action (a,vs)) (FILTER (λa. ¬varset_action (a,vs)) p_2)) < LENGTH (FILTER (λa. varset_action (a,vs)) p_2)` by 
		   	(`(∃a. MEM a p_2 ∧ (λa. varset_action (a,vs)) a)` by 
			       (`(∃a. MEM a (MAP (λa. (DRESTRICT (FST a) vs,SND a)) p_2) ∧ (λa. varset_action (a,vs)) a) ` by METIS_TAC[Q.SPEC `(MAP (λa. (DRESTRICT (FST a) vs,SND a)) p_2)` ( Q.ISPEC `(λa. varset_action (a,vs))` FILTER_NEQ_NIL) ]
			       THEN METIS_TAC[Q.SPEC`a`( Q.ISPEC `(\a. varset_action(a,vs))` ( Q.ISPEC `(λa. (DRESTRICT (FST a) vs,SND a))` ( Q.SPEC `p_2` graph_plan_lemma_1_1_1_16))), graph_plan_lemma_1_1_1_16_1, graph_plan_lemma_1_1_1_16_2])
			THEN METIS_TAC[graph_plan_lemma_1_1_1_1])
	      THEN `LENGTH (FILTER (λa. varset_action (a,vs)) ( p_1 ++ (FILTER (λa. ¬varset_action (a,vs)) p_2) ++ p_3)) < LENGTH (FILTER (λa. varset_action (a,vs)) (p_1 ++ p_2 ++ p_3))` by METIS_TAC[graph_plan_lemma_1_1_1_17]
	      THEN `set (( p_1 ++ (FILTER (λa. ¬varset_action (a,vs)) p_2) ++ p_3)) SUBSET PROB.A` by SRW_TAC[][graph_plan_lemma_1_1_1_8_2]
    	      THEN `(DRESTRICT (exec_plan (exec_plan (s,p_1),p_2)) (FDOM s DIFF vs) = DRESTRICT (exec_plan (exec_plan (s,p_1),FILTER (λa. ¬varset_action (a,vs)) p_2)) (FDOM s DIFF vs))` by SRW_TAC[][graph_plan_lemma_1_1_1_6]
	      THEN `exec_plan (exec_plan (s,p_1), p_2) = exec_plan (exec_plan (s,p_1),FILTER (λa. ¬varset_action (a,vs)) p_2)` by 
	      	   	(`FDOM(exec_plan (exec_plan(s, p_1), p_2)) = FDOM s` by SRW_TAC[][graph_plan_lemma_1_1_1_8_1]
			THEN `FDOM(exec_plan (exec_plan(s, p_1),FILTER (λa. ¬varset_action (a,vs)) p_2)) = FDOM s` by SRW_TAC[][graph_plan_lemma_1_1_1_8_1, graph_plan_lemma_1_1_1_8_2]
			THEN METIS_TAC[graph_plan_lemma_1_1_1_7])
	      THEN `exec_plan (s,rem_condless_act (s,[],p)) = exec_plan (s,p_1 ++ FILTER (λa. ¬varset_action (a,vs)) p_2 ++ p_3)` by  
	      	   (`exec_plan (s,p_1++ p_2++p_3) = exec_plan (s,p_1 ++ FILTER (λa. ¬varset_action (a,vs)) p_2 ++ p_3)` by FULL_SIMP_TAC(srw_ss())[exec_plan_Append]
		   THEN SRW_TAC[][] THEN METIS_TAC[])
	      THEN `exec_plan (s,p) = exec_plan (s,p_1 ++ FILTER (λa. ¬varset_action (a,vs)) p_2 ++ p_3)` by (
	      	   `exec_plan (s,p_1++ p_2++p_3) = exec_plan (s,p_1 ++ FILTER (λa. ¬varset_action (a,vs)) p_2 ++ p_3)` by FULL_SIMP_TAC(srw_ss())[exec_plan_Append]
	      	   THEN `exec_plan (s,rem_condless_act (s,[],p)) = exec_plan (s,p_1 ++ FILTER (λa. ¬varset_action (a,vs)) p_2 ++ p_3)` by (SRW_TAC[][] THEN METIS_TAC[])
		   THEN SRW_TAC[][] THEN METIS_TAC[])
	      THEN `LENGTH (FILTER (λa. varset_action (a,vs)) (p_1 ++ p_2 ++ p_3)) <= LENGTH (FILTER (λa. varset_action (a,vs)) (p))` by SRW_TAC[][]
	      THEN `LENGTH (FILTER (λa. varset_action (a,vs)) (p_1 ++ FILTER (λa. ¬varset_action (a,vs)) p_2 ++ p_3))
	      	    < LENGTH (FILTER (λa. varset_action (a,vs)) (p))` by
		    (`LENGTH (FILTER (λa. varset_action (a,vs)) (p_1 ++ p_2 ++ p_3)) <= LENGTH (FILTER (λa. varset_action (a,vs)) (p))` by SRW_TAC[][]
		    THEN DECIDE_TAC)
	      THEN METIS_TAC[]
	      ,
	      `(LENGTH (FILTER (λa. varset_action (a,vs)) (rem_condless_act (s,[],p))) <= 2 ** CARD vs)` by DECIDE_TAC
	      THEN `LENGTH (FILTER (λa. varset_action (a,vs)) (rem_condless_act (s,[],p))) < LENGTH (FILTER (λa. varset_action (a,vs)) p)` by DECIDE_TAC
	      THEN METIS_TAC[]                  
	      ])
THEN ASSUME_TAC(Q.SPEC  `2 ** CARD vs` (Q.ISPEC `(λas''. LENGTH (FILTER (λa. varset_action (a,vs)) as''))` ( Q.ISPEC `(λas''. (exec_plan (s,as'') = exec_plan (s,as)) ∧ set as'' ⊆ PROB.A)` general_theorem)))
THEN METIS_TAC[]
);


val child_parent_lemma_2_1_3 = store_thm("child_parent_lemma_2_1_3",
``!l P1 P2 P3 k1 k2. ((! x. MEM x l ==> (P1 x /\ ~P2 x) \/ (~P1 x /\ P2 x)) /\ LENGTH (FILTER P1 l) < k1
     /\ (!l'.  (?pfx sfx. pfx ++ l' ++ sfx = l) /\ (! x. MEM x l' ==> (P2 x)) ==> LENGTH l' < k2 ))
     ==>
     LENGTH(l) < k1 ** k2``

);


val graph_plan_lemma_1_1_1___1_1 = store_thm("graph_plan_lemma_1_1_1___1_1",
``!PROB a vs s. (dep_var_set(PROB, (FDOM PROB.I) DIFF vs, vs  )  /\ ~dep_var_set(PROB, vs, (FDOM PROB.I) DIFF vs)  /\  ¬varset_action ((DRESTRICT (FST a) vs,SND a),vs) /\ a IN PROB.A /\ vs SUBSET FDOM(PROB.I) /\ (FDOM s = FDOM PROB.I) /\ planning_problem(PROB))
==> (DRESTRICT (state_succ_2 s (DRESTRICT (FST a) vs,SND a)) vs = DRESTRICT s vs)``,
SRW_TAC[][varset_action_def, dep_var_set_def, dep_def, SUBSET_DEF, planning_problem_def]
THEN `!x. DRESTRICT (state_succ_2 s (DRESTRICT (FST a) vs,SND a)) vs ' x = DRESTRICT s vs ' x` by (SRW_TAC[][state_succ_2_def]
     THEN REWRITE_TAC[DRESTRICT_DEF]
     THEN FULL_SIMP_TAC(srw_ss())[SUBSET_DEF,FUNION_DEF,UNION_DEF, EXTENSION, DRESTRICT_DEF, DISJOINT_DEF, INTER_DEF]
     THEN SRW_TAC[][]
     THEN METIS_TAC[SPECIFICATION])

THEN `FDOM(DRESTRICT (state_succ_2 s (DRESTRICT (FST a) vs,SND a)) vs) = FDOM(DRESTRICT s vs)` by 
     (`FDOM (SND (DRESTRICT (FST a) vs,SND a)) SUBSET FDOM s` by SRW_TAC[][]
     THEN METIS_TAC[FDOM_state_succ, SUBSET_DEF, FDOM_DRESTRICT])
THEN METIS_TAC[fmap_EQ_THM]
);







val graph_plan_lemma_1_1_1___1 = store_thm("graph_plan_lemma_1_1_1___1",
``∀PROB s as vs.
     ( planning_problem PROB ∧ set as ⊆ PROB.A ∧ (FDOM s = FDOM PROB.I) /\
     vs ⊆ FDOM PROB.I ∧ dep_var_set (PROB,FDOM PROB.I DIFF vs,vs) ∧
     ¬dep_var_set (PROB,vs,FDOM PROB.I DIFF vs)
     /\ (∀as'. (as' ≠ [] ∧ as' ≼ (FILTER (λa. varset_action (a,vs))(MAP (λa. (DRESTRICT (FST a) vs,SND a)) as))) ⇒ (FST (LAST as') ⊑ LAST (state_list (s,as'))))) ⇒ 
     (DRESTRICT (exec_plan(DRESTRICT s vs, (FILTER (λa. varset_action (a,vs))(MAP (λa. (DRESTRICT (FST a) vs,SND a)) as)))) vs 
	   = exec_plan(DRESTRICT s vs, (FILTER (λa. varset_action (a,vs))(MAP (λa. (DRESTRICT (FST a) vs,SND a)) as))))``,
Induct_on `as`
THEN SRW_TAC[][exec_plan_def]
THENL
[
       Cases_on `(FILTER (λa. varset_action (a,vs))(MAP (λa. (DRESTRICT (FST a) vs,SND a)) as)) = []`
       THENL[
		FULL_SIMP_TAC(srw_ss())[exec_plan_def]
		THEN SRW_TAC[][]
		THEN METIS_TAC[graph_plan_lemma_1_1_1_11_1_4]
		,
		`(state_succ_2 (DRESTRICT s vs) (DRESTRICT (FST h) vs,SND h)) = (DRESTRICT (state_succ_2 s (DRESTRICT (FST h) vs,SND h)) vs)` by 
		     (FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_1_1_1_2_3, graph_plan_lemma_1_1_1_2_4, planning_problem_def, varset_action_def]
		     THEN `FST (DRESTRICT (FST h) vs,SND h) SUBMAP s` by METIS_TAC[graph_plan_lemma_1_1_1_11_1_5, graph_plan_lemma_1_1_1_2_4]
		     THEN `varset_action((DRESTRICT (FST h) vs,SND h), vs)` by SRW_TAC[][varset_action_def]
		     THEN `FDOM( SND (DRESTRICT (FST h) vs,SND h)) SUBSET FDOM s` by SRW_TAC[][]
		     THEN `(\a. (DRESTRICT (FST a) vs,SND a)) (DRESTRICT (FST h) vs,SND h) = (DRESTRICT (FST h) vs,SND h) ` by SRW_TAC[][] 
		     THEN METIS_TAC[graph_plan_lemma_1_1_1_11_1_6])
       		THEN `FDOM (state_succ_2 s (DRESTRICT (FST h) vs,SND h)) = FDOM PROB.I` by (SRW_TAC[][FDOM_state_succ, planning_problem_def]
     	  	     THEN `FDOM (SND(DRESTRICT (FST h) vs,SND h)) SUBSET FDOM PROB.I` by FULL_SIMP_TAC(srw_ss())[planning_problem_def]  
	  	     THEN METIS_TAC[FDOM_state_succ])
       		THEN `(∀as'. (as' ≠ [] ∧ as' ≼ (FILTER (λa. varset_action (a,vs))(MAP (λa. (DRESTRICT (FST a) vs,SND a)) as))) ⇒ (FST (LAST as') ⊑ LAST (state_list ((state_succ_2 s (DRESTRICT (FST h) vs,SND h)),as'))))` by METIS_TAC[graph_plan_lemma_1_1_1_2_1_1]		     
		THEN METIS_TAC[]	  
	]
	,
	METIS_TAC[FDOM_state_succ, planning_problem_def]
]);



val graph_plan_lemma_1_1_1___2 = store_thm("graph_plan_lemma_1_1_1___2",
``! vs as. FILTER (λa. varset_action (a,vs))(MAP (λa. (DRESTRICT (FST a) vs,SND a)) as) =  FILTER (λa. varset_action (a,vs))(MAP (λa. (DRESTRICT (FST a) vs,SND a)) (FILTER (λa. varset_action (a,vs))(MAP (λa. (DRESTRICT (FST a) vs,SND a)) as)))``,
Induct_on`as`
THEN SRW_TAC[][]
);

val graph_plan_lemma_1_1_1__ = store_thm("graph_plan_lemma_1_1_1__",
``∀PROB s as vs.
     (planning_problem PROB ∧ set as ⊆ PROB.A ∧ (FDOM s = FDOM PROB.I) /\
     vs ⊆ FDOM PROB.I ∧ dep_var_set (PROB,FDOM PROB.I DIFF vs,vs) ∧
     ¬dep_var_set (PROB,vs,FDOM PROB.I DIFF vs)
        /\ (∀as'. (as' ≠ [] ∧ as' ≼ (FILTER (λa. varset_action (a,vs)) (MAP (λa. (DRESTRICT (FST a) vs,SND a)) as))) ⇒ (FST (LAST as') ⊑ LAST (state_list (s,as'))))) ⇒ 
        (DRESTRICT (exec_plan( s, (FILTER (λa. varset_action (a,vs))(MAP (λa. (DRESTRICT (FST a) vs,SND a)) as)))) vs = exec_plan(DRESTRICT s vs, (FILTER (λa. varset_action (a,vs))(MAP (λa. (DRESTRICT (FST a) vs,SND a)) as))))``,
SRW_TAC[][]
THEN METIS_TAC[graph_plan_lemma_1_1_1___1, graph_plan_lemma_1_1_1_11_2])



val _ = export_theory();




