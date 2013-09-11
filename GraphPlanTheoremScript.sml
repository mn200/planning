open HolKernel Parse boolLib bossLib;

open finite_mapTheory
open arithmeticTheory
open pred_setTheory
open FM_planTheory
open rich_listTheory
open listTheory;							 
open utilsTheory;
val _ = new_theory "GraphPlanTheorem";
val dep_def = Define`dep(PROB, v1, v2) <=>  (?a. (a IN PROB.A) /\ (((v1 IN (FDOM (FST a))) /\ (v2 IN (FDOM (SND a))) ) \/ ((v1 IN (FDOM (SND a))) /\ (v2 IN (FDOM (SND a))) )) ) `;


val dep_var_set_def  = Define`dep_var_set (PROB, vs1, vs2) <=> ? v1 v2. (v1 IN vs1) /\ (v2 IN vs2) /\ (DISJOINT vs1 vs2) /\ dep(PROB, v1, v2)`;

val prob_proj_def = Define`prob_proj(PROB, vs) = ((PROB with I := DRESTRICT PROB.I vs) with G := DRESTRICT PROB.G vs) with A := IMAGE (\a. (DRESTRICT (FST a) vs, DRESTRICT (SND a) vs) ) PROB.A`;

val action_proj_def = Define `action_proj(a, vs) = (DRESTRICT (FST a) vs,DRESTRICT (SND a) vs)` ;

val as_proj_def = Define `(as_proj(a::as, vs) =  if (FDOM (DRESTRICT (SND a) vs) <> EMPTY) then
    	action_proj(a,vs) ::as_proj(as, vs)
else
	(as_proj(as, vs)))
/\ (as_proj([], vs) = [])`;



val varset_action_def = Define ` varset_action(a:('a state # 'a state), varset) <=>  ((FDOM (SND a)) SUBSET varset)`;

val sat_precond_as_def = 
    Define `(sat_precond_as(s, a::as) = (FST a SUBMAP s /\ sat_precond_as(state_succ s a, as))) 
    /\ (sat_precond_as(s, []) = T)`; 

val rem_effectless_act_def 
   = Define `(rem_effectless_act(a::as)
	         = if (FDOM(SND a) <> EMPTY) then a::rem_effectless_act(as)
	     	   else rem_effectless_act(as))
	   /\ (rem_effectless_act([]) = [])`;


val no_effectless_act_def
    = Define `(no_effectless_act(a::as)
		= ((FDOM (SND a) <> EMPTY) /\ no_effectless_act(as)))
	    /\ (no_effectless_act([]) = T)` ;




val graph_plan_lemma_1_1_1 = store_thm("graph_plan_lemma_1_1_1",
``!fm1 fm2 vs.  (fm2 SUBMAP fm1) 
       ==> ((DRESTRICT fm2 vs) SUBMAP (DRESTRICT fm1 vs) )``,
SRW_TAC[][SUBSET_DEF, SUBMAP_DEF]
THEN FULL_SIMP_TAC(srw_ss())[SUBSET_DEF, SUBMAP_DEF, FDOM_DRESTRICT, DRESTRICT_DEF]
);



val graph_plan_lemma_1_1 = store_thm ("graph_plan_lemma_1_1",
``!s a vs. ((FST a) SUBMAP s ) ==> 
     (state_succ (DRESTRICT s vs) (action_proj(a,vs)) = DRESTRICT (state_succ s a) vs)``,
SRW_TAC[][state_succ_def, action_proj_def]
THEN `FDOM(DRESTRICT (SND a) vs ⊌ DRESTRICT s vs) = FDOM(DRESTRICT (SND a ⊌ s) vs)`
     by (SRW_TAC[][FDOM_DRESTRICT]
     THEN FULL_SIMP_TAC(srw_ss())[INTER_DEF, UNION_DEF, EXTENSION, SUBSET_DEF, SPECIFICATION, SUBMAP_DEF]
     THEN METIS_TAC[])
THEN `!x. (DRESTRICT (SND a) vs ⊌ DRESTRICT s vs) ' x = (DRESTRICT (SND a ⊌ s) vs) ' x`      
     by (SRW_TAC[][]
     THEN REWRITE_TAC[DRESTRICT_DEF]
     THEN FULL_SIMP_TAC(srw_ss())[SUBSET_DEF,FUNION_DEF, UNION_DEF, EXTENSION, DRESTRICT_DEF]
     THEN SRW_TAC[][]
     THEN METIS_TAC[SPECIFICATION])
THEN METIS_TAC[fmap_EQ_THM, graph_plan_lemma_1_1_1]
);


val graph_plan_lemma_1_2_1 = store_thm("graph_plan_lemma_1_2_1",
``!fm1 fm2 vs. (vs ⊆ FDOM fm1) /\ (fm2 = fm1) 
       ==> ((DRESTRICT fm2 vs) = (DRESTRICT fm1 vs) )``,
SRW_TAC[][SUBSET_DEF, SUBMAP_DEF]
);


val graph_plan_lemma_1_2_2 = store_thm("graph_plan_lemma_1_2_2",
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


val graph_plan_lemma_1_2 = store_thm("graph_plan_lemma_1_2",
``!a vs s. (DISJOINT  (FDOM (SND a)) vs)
==> ((DRESTRICT s vs) = (DRESTRICT (state_succ s  a) vs))``,
SRW_TAC[][]
THEN SRW_TAC[][dep_var_set_def, dep_def, DISJOINT_DEF, DRESTRICT_DEF, INTER_DEF, EXTENSION, planning_problem_def]
THEN SRW_TAC[][state_succ_def, FUNION_DEF]
THEN METIS_TAC[graph_plan_lemma_1_2_2]
);
val graph_plan_lemma_1_3 = store_thm("graph_plan_lemma_1_3",
``!x vs. (FDOM (DRESTRICT (x) vs) = EMPTY)
<=>DISJOINT (FDOM x) vs``,
SRW_TAC[][DISJOINT_DEF, FDOM_DRESTRICT]
);



val graph_plan_lemma_1 = store_thm("graph_plan_lemma_1",
``! s vs as. sat_precond_as(s, as)
	  ==>  (exec_plan((DRESTRICT s vs), as_proj(as, vs))  =  ((DRESTRICT (exec_plan(s,as)) vs) ))``,
Induct_on`as`
THEN SRW_TAC[][exec_plan_def, sat_precond_as_def, as_proj_def]
THENL
[
	`state_succ (DRESTRICT s vs) (action_proj (h,vs)) =
     		 DRESTRICT (state_succ s h) vs` 
		 	   by METIS_TAC[graph_plan_lemma_1_1]
	THEN METIS_TAC[]
	,
	FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_1_3]
	THEN `DRESTRICT s vs = DRESTRICT (state_succ s h) vs` by METIS_TAC[graph_plan_lemma_1_2]
	THEN SRW_TAC[][]
	THEN METIS_TAC[FDOM_state_succ, planning_problem_def]
]);




val graph_plan_lemma_2_1 = store_thm("graph_plan_lemma_2_1",
``!PROB vs. (* (vs SUBSET FDOM(PROB.I) )
==> *) FINITE vs ==>
(CARD( FDOM((prob_proj(PROB, vs)).I)) <= CARD(vs))``,
SRW_TAC[][prob_proj_def, FDOM_DRESTRICT]
THEN METIS_TAC[CARD_INTER_LESS_EQ, INTER_COMM ,SUBSET_INTER_ABSORPTION]
);


val graph_plan_lemma_2_2 = store_thm("graph_plan_lemma_2_2",
``!PROB vs. planning_problem(PROB) 
	==> planning_problem(prob_proj(PROB,vs))``,
SRW_TAC[][prob_proj_def, plan_def, exec_plan_def, planning_problem_def]
THEN SRW_TAC[][prob_proj_def, plan_def, exec_plan_def, planning_problem_def]
THEN REWRITE_TAC[DRESTRICT_DEF]
THEN REWRITE_TAC[INTER_DEF] 
THEN FULL_SIMP_TAC(srw_ss())[SUBSET_DEF]
THEN METIS_TAC[SPECIFICATION]);



val graph_plan_lemma_2_3_1 = store_thm("graph_plan_lemma_2_3_1",
``!PROB vs. plan(PROB,[])  ==> plan(prob_proj (PROB,vs), [])``,
SRW_TAC[][prob_proj_def, plan_def, exec_plan_def, planning_problem_def]
THEN SRW_TAC[][prob_proj_def, plan_def, exec_plan_def, planning_problem_def]
THEN REWRITE_TAC[DRESTRICT_DEF]
THEN REWRITE_TAC[INTER_DEF] 
THEN FULL_SIMP_TAC(srw_ss())[SUBSET_DEF]
THEN METIS_TAC[SPECIFICATION]
);



val graph_plan_lemma_2_3_7_1 = store_thm("graph_plan_lemma_2_3_7_1",
``!h s vs. (FDOM(SND h) SUBSET FDOM s) ==> ( FDOM(state_succ s (action_proj(h,vs))) =
       		     FDOM (state_succ s h))``,
SRW_TAC[][action_proj_def, state_succ_def, FUNION_DEF, FDOM_DRESTRICT, INTER_DEF, SUBSET_DEF, UNION_DEF, EXTENSION, SUBMAP_DEF]
THEN METIS_TAC[]
);

val graph_plan_lemma_2_3_7_2_1 = store_thm("graph_plan_lemma_2_3_7_2_1",
``!x vs y. x IN vs ==> (x IN FDOM (DRESTRICT (y) vs) <=> (x ∈ FDOM (y)))``,
SRW_TAC[][DRESTRICT_DEF]);

val graph_plan_lemma_2_3_7_2 = store_thm("graph_plan_lemma_2_3_7_2",
``!h s vs. ((FST h) SUBMAP s) /\ (FDOM(SND h) SUBSET FDOM s) ==> (DRESTRICT (state_succ s (action_proj(h,vs))) vs =
       		     DRESTRICT (state_succ s h) vs)``,
SRW_TAC[][]
THEN `FDOM(DRESTRICT (state_succ s (action_proj(h,vs))) vs) = FDOM (DRESTRICT (state_succ s h) vs)` by
     SRW_TAC[][graph_plan_lemma_2_3_7_1, FDOM_DRESTRICT]
THEN `!x. (DRESTRICT (state_succ s (action_proj(h,vs))) vs) ' x = (DRESTRICT (state_succ s h) vs) ' x` by
     (FULL_SIMP_TAC(srw_ss())[action_proj_def, state_succ_def, FUNION_DEF, DRESTRICT_DEF, SUBSET_DEF, INTER_DEF, EXTENSION]
     THEN SRW_TAC[][]
     THENL
     [
	FULL_SIMP_TAC(srw_ss())[FUNION_DEF]
     	THEN SRW_TAC[][]
     	THEN1 FULL_SIMP_TAC(srw_ss())[DRESTRICT_DEF]
     	THEN METIS_TAC[graph_plan_lemma_2_3_7_2_1]
	,
	FULL_SIMP_TAC(srw_ss())[FUNION_DEF]
     	THEN SRW_TAC[][]
     	THEN1 FULL_SIMP_TAC(srw_ss())[DRESTRICT_DEF]
     	THEN METIS_TAC[graph_plan_lemma_2_3_7_2_1]
	,
	FULL_SIMP_TAC(srw_ss())[FUNION_DEF]
     	THEN SRW_TAC[][]
     	THEN1 FULL_SIMP_TAC(srw_ss())[DRESTRICT_DEF]
     	THEN METIS_TAC[graph_plan_lemma_2_3_7_2_1]
	,
	FULL_SIMP_TAC(srw_ss())[FUNION_DEF, SUBMAP_DEF, FDOM_DRESTRICT, INTER_DEF, DRESTRICT_DEF]
     	THEN METIS_TAC[graph_plan_lemma_2_3_7_2_1]
	,
	FULL_SIMP_TAC(srw_ss())[FUNION_DEF, SUBMAP_DEF, FDOM_DRESTRICT, INTER_DEF, DRESTRICT_DEF]
     	THEN METIS_TAC[graph_plan_lemma_2_3_7_2_1]	
     ])
THEN METIS_TAC[fmap_EQ_THM]
);

val graph_plan_lemma_2_3_7 = store_thm("graph_plan_lemma_2_3_7",
``! PROB vs h as.
h IN PROB.A /\ planning_problem(PROB) /\ FST h SUBMAP PROB.I /\ (plan(prob_proj (PROB with I:=state_succ PROB.I h,vs),as))
    ==>
(plan(prob_proj (PROB with I:=state_succ PROB.I (action_proj(h,vs)),vs),as))``,
FULL_SIMP_TAC(srw_ss())[plan_def]
THEN SRW_TAC[][]
THENL
[
	FULL_SIMP_TAC(srw_ss())[prob_proj_def, planning_problem_def]
	THEN SRW_TAC[][]
	THEN SRW_TAC[][pairTheory.SND]
	THEN `FDOM (state_succ PROB.I (action_proj(h,vs)) ) = FDOM PROB.I` by 
       	      (`FDOM (state_succ PROB.I h) = FDOM PROB.I` by METIS_TAC[FDOM_state_succ]
    	THEN METIS_TAC[graph_plan_lemma_2_3_7_1])
	THEN FULL_SIMP_TAC(srw_ss())[FDOM_DRESTRICT, INTER_DEF, SUBSET_DEF, EXTENSION] 
	THEN METIS_TAC[graph_plan_lemma_2_3_7_1, FDOM_DRESTRICT]
	,
	`(prob_proj(PROB with I := state_succ PROB.I (action_proj (h,vs)),vs))
		 = (prob_proj(PROB with I := state_succ PROB.I h,vs))` by(
		 FULL_SIMP_TAC(srw_ss())[prob_proj_def, graph_plan_lemma_2_3_7_2_1, planning_problem_def]
		 THEN SRW_TAC[][graph_plan_lemma_2_3_7_2])
	THEN SRW_TAC[][]
	,
	FULL_SIMP_TAC(srw_ss())[prob_proj_def]	
]);





val graph_plan_lemma_2_3_8_1 = store_thm("graph_plan_lemma_2_3_8_1",
``!s vs a . FST a SUBMAP s ==> (state_succ (DRESTRICT s vs) (action_proj(a, vs))=
     	DRESTRICT (state_succ s a) vs)``,
SRW_TAC[][state_succ_def,action_proj_def]
THEN `FDOM (DRESTRICT (SND a) vs ⊌ DRESTRICT s vs) = FDOM (DRESTRICT (SND a ⊌ s) vs)` by
     (SRW_TAC[][FDOM_DRESTRICT]
     THEN FULL_SIMP_TAC(srw_ss())[INTER_DEF, UNION_DEF, EXTENSION, SUBSET_DEF, SPECIFICATION]
     THEN METIS_TAC[])
THEN `!x. (DRESTRICT (SND a) vs ⊌ DRESTRICT s vs) ' x = (DRESTRICT (SND a ⊌ s) vs) ' x` by (SRW_TAC[][]
     THEN REWRITE_TAC[DRESTRICT_DEF]
     THEN FULL_SIMP_TAC(srw_ss())[SUBSET_DEF,FUNION_DEF, UNION_DEF, EXTENSION, DRESTRICT_DEF]
     THEN SRW_TAC[][]
     THEN METIS_TAC[SPECIFICATION])
THEN METIS_TAC[fmap_EQ_THM, FDOM_FUNION, graph_plan_lemma_1_1_1]);


val graph_plan_lemma_2_3_8_2 = store_thm("graph_plan_lemma_2_3_8_2",
``! as PROB vs a. FST a ⊑ PROB.I ==>( exec_plan ((prob_proj (PROB,vs)).I,action_proj(a,vs)::as) =   exec_plan((prob_proj (PROB with I := state_succ PROB.I a,vs)).I,as))``,
Induct_on`as`
THEN SRW_TAC[][exec_plan_def, prob_proj_def] 
THEN METIS_TAC[graph_plan_lemma_2_3_8_1]
);


val graph_plan_lemma_2_3_8_3 = store_thm("graph_plan_lemma_2_3_8_3",
``!x y vs. (FDOM x SUBSET FDOM y ) ==> (FDOM (DRESTRICT (x) vs) ⊆ FDOM (DRESTRICT y vs))``,
SRW_TAC[][FDOM_DRESTRICT]
THEN FULL_SIMP_TAC(srw_ss())[SUBSET_DEF, INTER_DEF]
);



val graph_plan_lemma_2_3_8_4 = store_thm("graph_plan_lemma_2_3_8_4",
``!PROB vs. (FDOM PROB.I = FDOM PROB.G)
	==> (FDOM (prob_proj (PROB,vs)).G = FDOM (prob_proj (PROB,vs)).I)``,
SRW_TAC[][prob_proj_def]
THEN SRW_TAC[][DRESTRICT_DEF]
);

val graph_plan_lemma_2_3_8_5= store_thm("graph_plan_lemma_2_3_8_5",
``!x vs. FDOM(x) SUBSET vs ==> (DRESTRICT x vs = x) ``,
SRW_TAC[][]     
THEN `FDOM x = FDOM(DRESTRICT x vs)` by METIS_TAC[FDOM_DRESTRICT, SUBSET_INTER_ABSORPTION]
THEN METIS_TAC[fmap_EQ_THM, DRESTRICT_DEF]
);

val graph_plan_lemma_2_3_8_6= store_thm("graph_plan_lemma_2_3_8_6",
``∀PROB h as vs . 
     ((prob_proj(PROB,vs)).G = (prob_proj(PROB with I := state_succ PROB.I h, vs)).G)``,
     SRW_TAC[][prob_proj_def]);


val graph_plan_lemma_2_3_8 = store_thm("graph_plan_lemma_2_3_8",
``!PROB as a vs. ((FST a) SUBMAP PROB.I)  /\ planning_problem(PROB) /\ (a IN PROB.A) /\ plan(prob_proj(PROB with I:= state_succ PROB.I a, vs), as)
==> plan(prob_proj (PROB,vs),action_proj(a, vs)::as)``,
Cases_on`as`
THENL
[
	SRW_TAC[][]
	THEN FULL_SIMP_TAC(srw_ss())[ plan_def]
	THEN SRW_TAC[][]
	THENL
	[
		FULL_SIMP_TAC(srw_ss())[planning_problem_def]
		THEN SRW_TAC[][]
		THENL
		[
			FULL_SIMP_TAC(srw_ss())[prob_proj_def] 
			THEN SRW_TAC[][]
			THEN METIS_TAC[graph_plan_lemma_2_3_8_3]
			,
			FULL_SIMP_TAC(srw_ss())[prob_proj_def] 
			THEN SRW_TAC[][]
			THEN METIS_TAC[graph_plan_lemma_2_3_8_3]
			,
			METIS_TAC[graph_plan_lemma_2_3_8_4]			
		]
		,
		FULL_SIMP_TAC(srw_ss())[exec_plan_def]
		THEN FULL_SIMP_TAC(srw_ss())[prob_proj_def]
		THEN METIS_TAC[graph_plan_lemma_2_3_8_1]
		,
		FULL_SIMP_TAC(srw_ss())[prob_proj_def, action_proj_def]
		THEN METIS_TAC[]
	]
	,
	SRW_TAC[][plan_def]
	THENL
	[
		FULL_SIMP_TAC(srw_ss())[planning_problem_def]
		THEN SRW_TAC[][]
		THENL
		[
			FULL_SIMP_TAC(srw_ss())[prob_proj_def] 
			THEN SRW_TAC[][]
			THEN METIS_TAC[graph_plan_lemma_2_3_8_3]
			,
			FULL_SIMP_TAC(srw_ss())[prob_proj_def] 
			THEN SRW_TAC[][]
			THEN METIS_TAC[graph_plan_lemma_2_3_8_3]
			, 
			METIS_TAC[graph_plan_lemma_2_3_8_4]			
		]
		,
		METIS_TAC[graph_plan_lemma_2_3_8_2, graph_plan_lemma_2_3_8_6]
		,
		FULL_SIMP_TAC(srw_ss())[prob_proj_def,action_proj_def]
		THEN METIS_TAC[graph_plan_lemma_2_3_8_5]
		,
		FULL_SIMP_TAC(srw_ss())[prob_proj_def, action_proj_def]
		THEN METIS_TAC[graph_plan_lemma_2_3_8_5]
		,
		FULL_SIMP_TAC(srw_ss())[prob_proj_def, action_proj_def]
	]
])

val graph_plan_lemma_2_3_9 = store_thm("graph_plan_lemma_2_3_9",
``!as a vs. FDOM (DRESTRICT (SND a) vs) <> ∅ ==>
     ((as_proj (a::as,vs)) =  (action_proj(a, vs)::as_proj(as,vs))) ``,
SRW_TAC[][action_proj_def, as_proj_def]);

val graph_plan_lemma_2_3_10 = store_thm("graph_plan_lemma_2_3_10",
``!as a vs. (FDOM (DRESTRICT (SND a) vs) = ∅) ==>
      (as_proj (a::as,vs) = as_proj(as,vs))``,
SRW_TAC[][action_proj_def, as_proj_def]);


val graph_plan_lemma_2_3_11_1 = store_thm("graph_plan_lemma_2_3_11_1",
``!s a vs. (FDOM (DRESTRICT (SND a) vs) = ∅) ==>
       (DRESTRICT (state_succ s (action_proj (a,vs))) vs = DRESTRICT s vs)``,
SRW_TAC[][action_proj_def]
THEN `FDOM (DRESTRICT (DRESTRICT (SND a) vs) vs) = EMPTY` by FULL_SIMP_TAC(srw_ss())[DRESTRICT_IDEMPOT]
THEN FULL_SIMP_TAC(srw_ss())[Once FDOM_DRESTRICT]
THEN `DISJOINT (FDOM (DRESTRICT (SND (DRESTRICT (FST a) vs,DRESTRICT (SND a) vs)) vs)) vs` by SRW_TAC[][DISJOINT_DEF]
THEN FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_1_2]); 

val graph_plan_lemma_2_3_11 = store_thm("graph_plan_lemma_2_3_11",
``!PROB a vs. (FDOM (DRESTRICT (SND a) vs) = ∅) ==>
       (prob_proj(PROB with I := state_succ PROB.I (action_proj (a,vs)),vs)
		  = prob_proj(PROB, vs))``,
SRW_TAC[][prob_proj_def, graph_plan_lemma_2_3_11_1]);

val graph_plan_lemma_2_3 = store_thm("graph_plan_lemma_2_3",
``!PROB as vs. (plan(PROB, as) 
  /\ sat_precond_as(PROB.I, as))
==> plan(prob_proj(PROB,vs), as_proj(as, vs))``,
Induct_on`as`
THEN1 SRW_TAC[][graph_plan_lemma_2_3_1, as_proj_def] 
THEN SRW_TAC[][]
THEN `plan (PROB with I:=state_succ PROB.I h,as)` by METIS_TAC[lemma_1_1]
THEN `h IN PROB.A` by FULL_SIMP_TAC(srw_ss())[plan_def]
THEN `(FDOM PROB.I DIFF vs) SUBSET FDOM(PROB.I)` by SRW_TAC[][]
THEN Cases_on`as <> []`
THENL
[
	FULL_SIMP_TAC(srw_ss())[sat_precond_as_def]
	THEN SRW_TAC[][]
	THEN `plan(prob_proj (PROB with I:=state_succ PROB.I h,vs),as_proj(as,vs))` by FULL_SIMP_TAC(srw_ss())[FDOM_state_succ, plan_def, planning_problem_def]
	THEN `plan(prob_proj (PROB with I:=state_succ PROB.I (action_proj(h,vs)),vs),as_proj(as,vs))` by 
	     (SRW_TAC[][]
	     THEN METIS_TAC[graph_plan_lemma_2_3_7, planning_problem_def, plan_def])
	THEN Cases_on `(FDOM (DRESTRICT (SND h) vs) <> ∅)`
	THEN FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_2_3_9, graph_plan_lemma_2_3_10]
	THEN METIS_TAC[graph_plan_lemma_2_3_8, plan_def, graph_plan_lemma_2_3_11]
	,
	SRW_TAC[][as_proj_def]
	THENL
	[
		SRW_TAC[][MAP_EQ_NIL]
		THEN SRW_TAC[][GSYM action_proj_def]
		THEN `plan(prob_proj (PROB with I:=state_succ PROB.I h,vs),[])` by METIS_TAC[graph_plan_lemma_2_3_1]
		THEN `plan(prob_proj (PROB with I:=state_succ PROB.I (action_proj(h,vs)),vs),[])` by 
		     (SRW_TAC[][]
		     THEN FULL_SIMP_TAC(srw_ss())[sat_precond_as_def]
	     	     THEN METIS_TAC[graph_plan_lemma_2_3_7, planning_problem_def, plan_def])
		THEN FULL_SIMP_TAC(srw_ss())[sat_precond_as_def]
		THEN SRW_TAC[][]
		THEN FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_2_3_8, plan_def]		
		,
		FULL_SIMP_TAC(srw_ss())[sat_precond_as_def]
		THEN SRW_TAC[][]
		THEN `prob_proj (PROB with I := state_succ PROB.I (action_proj (h,vs)),vs) = (prob_proj (PROB,vs))` 
	     	     by FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_2_3_11]
		THEN SRW_TAC[][]
		THEN `plan(prob_proj (PROB with I:=state_succ PROB.I h,vs),as_proj ([],vs))` by FULL_SIMP_TAC(srw_ss())[FDOM_state_succ, plan_def, planning_problem_def]
		THEN `plan(prob_proj (PROB with I:=state_succ PROB.I (action_proj(h,vs)),vs),as_proj([],vs))` by 
	     	     (SRW_TAC[][]
	     	     THEN METIS_TAC[graph_plan_lemma_2_3_7, planning_problem_def, plan_def])
		THEN METIS_TAC[]
	]	
]);


val graph_plan_lemma_2 = store_thm("graph_plan_lemma_2",
``!PROB vs as.
	  (plan(PROB,as) 
	   /\ (FINITE vs)
	  /\ LENGTH(as_proj(as, vs)) > (2**(CARD(vs)))  
	  /\ sat_precond_as(PROB.I, as))
	  ==>
	  (∃as1 as2 as3. (as1 ++ as2 ++ as3 = as_proj(as, vs)) ∧
       	  ((exec_plan((prob_proj(PROB, vs)).I,as1 ++ as2) = exec_plan ((prob_proj(PROB, vs)).I,as1)) ∧ (as2 ≠ [])))``,
SRW_TAC[][]
THEN `CARD (FDOM (prob_proj(PROB, vs)).I) <= CARD(vs)` by METIS_TAC[graph_plan_lemma_2_1]
THEN `plan(prob_proj (PROB,vs), as_proj(as, vs))` by FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_2_3]
THEN `planning_problem(prob_proj(PROB,vs))` by METIS_TAC[graph_plan_lemma_2_2, plan_def] 
THEN `LENGTH (as_proj(as, vs)) > 2 ** CARD (FDOM (prob_proj (PROB,vs)).I) ` by 
     (SRW_TAC[][]
     THEN `2 ** (CARD (FDOM (prob_proj (PROB,vs)).I)) ≤ 2 ** (CARD vs)` by SRW_TAC[][]
     THEN DECIDE_TAC)
THEN METIS_TAC[lemma_2]);




val as_proj_child_def = Define `as_proj_child(as, vs) = 
    (FILTER (λa. varset_action (a,vs) /\ (FDOM (SND a)) <> EMPTY )(MAP (λa. (DRESTRICT (FST a) vs,SND a)) as))`; 


val graph_plan_lemma_3 = store_thm("graph_plan_lemma_3",
``!vs as: ('a state # 'a state) list. 
no_effectless_act(as) ==>
( LENGTH(FILTER (\a. varset_action(a, vs) ) as) 
      	  = LENGTH(as_proj_child(as, vs)))``,
Induct_on`as`
THEN SRW_TAC[][FILTER, as_proj_child_def, no_effectless_act_def]
THEN FULL_SIMP_TAC(srw_ss())[LENGTH_MAP, varset_action_def]
);


val graph_plan_lemma_4_1 = store_thm("graph_plan_lemma_4_1",
``!s s' vs a a'. ((DRESTRICT s vs = DRESTRICT s' vs) /\ (FST a ⊑ s = FST a' ⊑ s') /\ 
     (DRESTRICT (SND a) vs = DRESTRICT (SND a') vs))
	      ==> (DRESTRICT (state_succ s a) vs = DRESTRICT (state_succ s' a') vs)``,
SRW_TAC[][]
THEN `FDOM(DRESTRICT (state_succ s a) vs) = FDOM(DRESTRICT (state_succ s' a') vs)`
     	by (SRW_TAC[][FDOM_DRESTRICT, state_succ_def]
	THEN `FDOM (DRESTRICT s vs) = FDOM (DRESTRICT s' vs)` by METIS_TAC[fmap_EQ_THM]
	THEN `FDOM (DRESTRICT (SND a) vs) = FDOM (DRESTRICT (SND a') vs)` by METIS_TAC[fmap_EQ_THM]
	THEN FULL_SIMP_TAC(srw_ss())[INTER_DEF, UNION_DEF, EXTENSION, SUBSET_DEF, SPECIFICATION, SUBMAP_DEF, FDOM_DRESTRICT, EXTENSION, GSPEC_ETA]
	THEN SRW_TAC[][]
     	THEN METIS_TAC[])

THEN `!x. (DRESTRICT (state_succ s a) vs) ' x = (DRESTRICT (state_succ s' a') vs) ' x`      
     	by (SRW_TAC[][FDOM_DRESTRICT, state_succ_def]
	THEN `!x. (DRESTRICT s vs) ' x = (DRESTRICT s' vs) ' x` by METIS_TAC[fmap_EQ_THM]
	THEN `!x. (DRESTRICT (SND a) vs) ' x = (DRESTRICT (SND a') vs) ' x` by METIS_TAC[fmap_EQ_THM]
	THEN FULL_SIMP_TAC(srw_ss())[INTER_DEF, UNION_DEF, EXTENSION, SUBSET_DEF, SPECIFICATION, SUBMAP_DEF, FDOM_DRESTRICT, EXTENSION, GSPEC_ETA, FUNION_DEF, fmap_EXT, DRESTRICT_DEF]
	THEN SRW_TAC[][FUNION_DEF]
	THEN METIS_TAC[])
THEN METIS_TAC[fmap_EQ_THM]);



val graph_plan_lemma_4 = store_thm("graph_plan_lemma_4",
``!s s' as vs P. ((!a. (MEM a as /\ P a) ==> DISJOINT (FDOM (SND a)) vs)
	    /\ sat_precond_as(s, as)
	    /\ sat_precond_as(s', FILTER (\a. ~(P a)) as)
	    /\ (DRESTRICT s vs = DRESTRICT s' vs)) 
     	    ==>
            ((DRESTRICT (exec_plan(s,as)) (vs)) = (DRESTRICT (exec_plan (s',FILTER (\a. ~(P a)) as)) (vs)))``,
Induct_on`as`
THEN SRW_TAC[][exec_plan_def]
THENL
[
	FULL_SIMP_TAC(srw_ss())[sat_precond_as_def] 	
	THEN `DRESTRICT (state_succ s h) vs = DRESTRICT (state_succ s' h) vs` by SRW_TAC[][graph_plan_lemma_4_1]
	THEN METIS_TAC[]
	,
	FULL_SIMP_TAC(srw_ss())[sat_precond_as_def] 	
	THEN `DRESTRICT (state_succ s h) (vs) = DRESTRICT s (vs)` by METIS_TAC[GSYM graph_plan_lemma_1_2]
	THEN METIS_TAC[]
]);


val graph_plan_lemma_5 = store_thm("graph_plan_lemma_5",
``!s s' vs. ((DRESTRICT s ((FDOM s) DIFF vs)) = (DRESTRICT s' ((FDOM s') DIFF vs)))
	    /\ ((DRESTRICT s vs) = (DRESTRICT s' vs))   
     	    ==>
            (s = s')``,
SRW_TAC[][]
THEN `FDOM s = FDOM s'` by 
      (FULL_SIMP_TAC(srw_ss())[FDOM_DRESTRICT, fmap_EXT, INTER_DEF] 
      THEN FULL_SIMP_TAC(srw_ss())[EXTENSION]	       	      
      THEN METIS_TAC[])
THEN `!x. s ' x = s' ' x` by
     (FULL_SIMP_TAC(srw_ss())[fmap_EXT, DRESTRICT_DEF]
     THEN Cases_on `x IN vs`
     THEN Cases_on `x ∈ FDOM s'`
     THEN FULL_SIMP_TAC(srw_ss())[]
     THEN METIS_TAC[NOT_FDOM_FAPPLY_FEMPTY])
THEN SRW_TAC[][GSYM fmap_EQ_THM]);

val graph_plan_lemma_6_1 = store_thm("graph_plan_lemma_6_1",
``! as s PROB. ((set as) SUBSET (PROB.A) /\ planning_problem(PROB) /\ (FDOM s = FDOM PROB.I) ) ==> 
    (FDOM(exec_plan(s, as)) = (FDOM PROB.I)  )``,
Induct_on `as`
THEN SRW_TAC[][exec_plan_def]
THEN FULL_SIMP_TAC(srw_ss())[SPECIFICATION, planning_problem_def]
THEN METIS_TAC[FDOM_state_succ, planning_problem_def]
);


val graph_plan_lemma_6_2 = store_thm("graph_plan_lemma_6_2",
``!P l s. set(l) SUBSET s ==>
       	  set(FILTER P l) SUBSET s``,
 METIS_TAC [LIST_TO_SET_FILTER, INTER_SUBSET, SUBSET_TRANS]);


val graph_plan_lemma_6 = store_thm("graph_plan_lemma_6",
``! as PROB s. (planning_problem(PROB) /\ (FDOM s = FDOM PROB.I) 	   
	  /\ (set as SUBSET PROB.A)) ==> plan((PROB with I:=s) with G:=exec_plan(s,as), as)``,
SRW_TAC[][plan_def, planning_problem_def] 
THEN SRW_TAC[][]
THEN METIS_TAC[graph_plan_lemma_6_1,planning_problem_def]
);



val rem_condless_act_def 
   = Define `(rem_condless_act(s:'a state, pfx_a:(('a state # 'a state) list),  a::as:(('a state # 'a state) list) )	         = if ((FST a) SUBMAP exec_plan(s, pfx_a)) then rem_condless_act(s, pfx_a++[a], as)
	     else rem_condless_act(s, pfx_a, as))
	   /\ (rem_condless_act(s:'a state, pfx_a:(('a state # 'a state) list), [] ) = pfx_a)`;


val graph_plan_lemma_7_1_1 = store_thm("graph_plan_lemma_7_1_1",
``!s h as pfx. exec_plan (s,rem_condless_act (s,h:: pfx,as)) = exec_plan (state_succ s h,rem_condless_act (state_succ s h ,pfx,as))``,
Induct_on`as`
THEN SRW_TAC[][rem_condless_act_def, exec_plan_def, state_succ_def] 
);

val graph_plan_lemma_7_1 = store_thm("graph_plan_lemma_7_1",
``!as s. (exec_plan(s, as) = exec_plan(s, rem_condless_act(s, [], as)))``,
Induct_on`as`
THEN SRW_TAC[][rem_condless_act_def, exec_plan_def]
THEN METIS_TAC[graph_plan_lemma_7_1_1, FDOM_state_succ, planning_problem_def, state_succ_def]
);

val graph_plan_lemma_7_2_1_1 = store_thm("graph_plan_lemma_7_2_1_1",
``!h' pfx as s. rem_condless_act (s,h'::pfx,as) = h'::rem_condless_act (state_succ s h',pfx,as)``,
Induct_on`as`
THEN SRW_TAC[][rem_condless_act_def, exec_plan_def, state_succ_def] 
);

val graph_plan_lemma_7_2_1 = store_thm("graph_plan_lemma_7_2_1",
``! h h' as as' s. h'::as' ≼ rem_condless_act (s,[h],as) ==> (as'<<=  rem_condless_act (state_succ s h,[],as) /\ (h' = h))``,
Induct_on`as`
THEN SRW_TAC[][rem_condless_act_def, exec_plan_def]
THEN FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_7_2_1_1]);


val graph_plan_lemma_7_2 = store_thm("graph_plan_lemma_7_2",
``!as s.  sat_precond_as(s, rem_condless_act (s,[],as))``,
Induct_on`as`
THEN SRW_TAC[][rem_condless_act_def, exec_plan_def, sat_precond_as_def, graph_plan_lemma_7_2_1_1]);


val graph_plan_lemma_7_3 = store_thm("graph_plan_lemma_7_3",
``!as s. (LENGTH (rem_condless_act(s, [], as)) <= LENGTH as)``,
Induct_on`as`
THEN SRW_TAC[][rem_condless_act_def, exec_plan_def]
THENL
[
	FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_7_2_1_1]
	THEN SRW_TAC[][graph_plan_lemma_7_2_1_1]
	THEN `FDOM (state_succ s h) = FDOM PROB.I` by METIS_TAC[graph_plan_lemma_7_2_1_1, FDOM_state_succ, planning_problem_def]
	THEN METIS_TAC[]
	,
	`LENGTH (rem_condless_act (s,[],as)) ≤ (LENGTH as)` by METIS_TAC[]
	THEN DECIDE_TAC
]);

val graph_plan_lemma_7_4 = store_thm("graph_plan_lemma_7_4",
``!as A s. (set as SUBSET A) ==>
	  (set (rem_condless_act (s,[],as)) SUBSET A )``,
Induct_on`as`
THEN SRW_TAC[][rem_condless_act_def, exec_plan_def]
THEN FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_7_2_1_1]
THEN METIS_TAC[graph_plan_lemma_7_2_1_1, FDOM_state_succ, planning_problem_def]);


val graph_plan_lemma_7_6 = store_thm("graph_plan_lemma_7_6",
``!as s P. (LENGTH (FILTER P (rem_condless_act (s,[],as)))  <= LENGTH (FILTER P as) )``,
Induct_on`as`
THEN SRW_TAC[][rem_condless_act_def, exec_plan_def]
THENL
[
	FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_7_2_1_1]
	THEN METIS_TAC[graph_plan_lemma_7_2_1_1, FDOM_state_succ, planning_problem_def]
	,
	FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_7_2_1_1]
	THEN METIS_TAC[graph_plan_lemma_7_2_1_1, FDOM_state_succ, planning_problem_def]
	,
	`LENGTH (FILTER P (rem_condless_act (s,[],as))) <= (LENGTH (FILTER P as))` by METIS_TAC[]
	THEN DECIDE_TAC
]);


val graph_plan_lemma_7_7 = store_thm("graph_plan_lemma_7_7",
``!s P as as2. (EVERY P as /\ EVERY P as2)==> EVERY (P) (rem_condless_act (s,as2,as))``,
Induct_on `as`
THEN SRW_TAC[][rem_condless_act_def]);



val graph_plan_lemma_7 = store_thm("graph_plan_lemma_7",
``!as A s. (exec_plan(s, as) = exec_plan(s, rem_condless_act(s, [], as)))
	  /\ sat_precond_as(s, rem_condless_act(s, [], as))
	  /\ (LENGTH (rem_condless_act(s, [], as)) <= LENGTH as) 
	  /\ ((set as SUBSET A) ==> (set (rem_condless_act (s,[],as)) SUBSET A ))
	  /\ (!P. (LENGTH (FILTER P (rem_condless_act (s,[],as)))  <= LENGTH (FILTER P as) ))``,
METIS_TAC[graph_plan_lemma_7_1, graph_plan_lemma_7_2, graph_plan_lemma_7_3, graph_plan_lemma_7_4, graph_plan_lemma_7_6]);


val graph_plan_lemma_8_1_1 = store_thm("graph_plan_lemma_8_1_1",
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



val graph_plan_lemma_8_1 = store_thm("graph_plan_lemma_8_1",
``! f1 f2 as1 as2 as3 p. (as1 ++ as2 ++ as3 =
       FILTER f1 (MAP f2  p)) ==>
	      ?p_1 p_2 p_3. (p_1 ++ p_2 ++ p_3 = p) /\ (as1 = FILTER f1 (MAP f2 p_1)) /\ (as2 = FILTER f1 (MAP f2 p_2)) /\ (as3 = FILTER f1 (MAP f2 p_3))``,
SRW_TAC[][]
THEN `∃p_1 p_2.
          (p_1 ++ p_2 = p) /\ ((as1) = FILTER f1 (MAP f2 p_1)) /\ (as2++as3 = FILTER f1 (MAP f2 p_2))` by METIS_TAC[graph_plan_lemma_8_1_1, APPEND_ASSOC] 

THEN `∃p_a p_b.
          (p_a ++ p_b = p_2) /\ ((as2) = FILTER f1 (MAP f2 p_a)) /\ (as3 = FILTER f1 (MAP f2 p_b))` by METIS_TAC[graph_plan_lemma_8_1_1] 
THEN Q.EXISTS_TAC `p_1`
THEN Q.EXISTS_TAC `p_a`
THEN Q.EXISTS_TAC `p_b`
THEN SRW_TAC[][]);


val graph_plan_lemma_8_2 = store_thm("graph_plan_lemma_8_2",
``!as vs. (as_proj(as, vs)) =  (FILTER (\a. FDOM (SND a) <> EMPTY) (MAP (\ a. (DRESTRICT (FST a) vs, DRESTRICT (SND a) vs)) as))``,
Induct_on `as` 
THEN SRW_TAC[][as_proj_def, action_proj_def]);



val graph_plan_lemma_8 = store_thm("graph_plan_lemma_8",
``!as1 as2 as3 p vs. (as1++as2++as3 = as_proj(p, vs)) ==>
?p_1 p_2 p_3. (p_1 ++ p_2 ++ p_3 = p) /\ (as2 = as_proj(p_2, vs)) /\ (as1 = as_proj(p_1, vs))``,
METIS_TAC[graph_plan_lemma_8_1, graph_plan_lemma_8_2]);

val graph_plan_lemma_9_1_1_1 = store_thm("graph_plan_lemma_9_1_1_1",
``!x s vs. (DRESTRICT x vs  ⊑ s) <=> ( DRESTRICT x vs SUBMAP DRESTRICT s vs)``,
SRW_TAC[][DRESTRICT_DEF, SUBMAP_DEF]
THEN EQ_TAC
THEN METIS_TAC[]);


val graph_plan_lemma_9_1_1 = store_thm("graph_plan_lemma_9_1_1",
``!a s vs. (state_succ (DRESTRICT s vs) (action_proj (a,vs)) =
      DRESTRICT (state_succ s (action_proj (a,vs))) vs)``,
SRW_TAC[][state_succ_def, action_proj_def]
THEN1 (`FDOM(DRESTRICT (SND a) vs ⊌ DRESTRICT s vs) = FDOM(DRESTRICT (DRESTRICT (SND a) vs ⊌ s) vs)`
     by (SRW_TAC[][FDOM_DRESTRICT]
     THEN FULL_SIMP_TAC(srw_ss())[INTER_DEF, UNION_DEF, EXTENSION, SUBSET_DEF, SPECIFICATION, SUBMAP_DEF]
     THEN METIS_TAC[])
THEN `!x. (DRESTRICT (SND a) vs ⊌ DRESTRICT s vs) ' x = (DRESTRICT (DRESTRICT (SND a) vs ⊌ s) vs) ' x`      
     by (SRW_TAC[][]
     THEN REWRITE_TAC[DRESTRICT_DEF]
     THEN FULL_SIMP_TAC(srw_ss())[SUBSET_DEF,FUNION_DEF, UNION_DEF, EXTENSION, DRESTRICT_DEF]
     THEN SRW_TAC[][]
     THEN METIS_TAC[SPECIFICATION])
THEN METIS_TAC[fmap_EQ_THM, graph_plan_lemma_1_1_1])
THEN METIS_TAC[graph_plan_lemma_9_1_1_1]);


val graph_plan_lemma_9_1 = store_thm("graph_plan_lemma_9_1",
``∀s as vs.(DRESTRICT (exec_plan(DRESTRICT s vs, as_proj(as, vs))) vs 
	   = exec_plan(DRESTRICT s vs, as_proj(as, vs)))``,
Induct_on `as`
THEN SRW_TAC[][exec_plan_def, as_proj_def]
THEN METIS_TAC[graph_plan_lemma_9_1_1] 
);



val graph_plan_lemma_9_2 = store_thm("graph_plan_lemma_9_2",
``∀s as vs. (DRESTRICT (exec_plan(DRESTRICT s vs, as_proj(as, vs))) vs 
		   = DRESTRICT (exec_plan(s, as_proj(as, vs))) vs)``,
Induct_on `as`
THEN SRW_TAC[][exec_plan_def, as_proj_def]
THEN SRW_TAC[][graph_plan_lemma_9_1_1]);


val graph_plan_lemma_9 = store_thm("graph_plan_lemma_9",
``∀s as vs. (DRESTRICT (exec_plan( s, as_proj(as, vs))) vs = exec_plan(DRESTRICT s vs,as_proj(as, vs)))``,
SRW_TAC[][]
THEN METIS_TAC[graph_plan_lemma_9_2, graph_plan_lemma_9_1]);


val graph_plan_lemma_10_1 = store_thm("graph_plan_lemma_10_1",
``!a vs. FDOM (SND(action_proj (a,vs))) SUBSET FDOM (SND a)``,
SRW_TAC[][action_proj_def, FDOM_DRESTRICT]);


val graph_plan_lemma_10 = store_thm("graph_plan_lemma_10",
``∀as s PROB vs.  set as ⊆ PROB.A ∧ planning_problem PROB ∧ (FDOM s = FDOM PROB.I) ⇒ 
(FDOM (exec_plan (s,as_proj(as, vs))) = FDOM PROB.I)``,
Induct_on `as`
THEN SRW_TAC[][exec_plan_def, as_proj_def, graph_plan_lemma_10_1]
THEN `FDOM (state_succ s (action_proj(h, vs))) = FDOM PROB.I` by
     (FULL_SIMP_TAC(srw_ss())[FDOM_state_succ, planning_problem_def, SUBSET_TRANS, graph_plan_lemma_10_1]
     THEN METIS_TAC[SUBSET_TRANS, FDOM_state_succ, graph_plan_lemma_10_1])
THEN METIS_TAC[SUBSET_TRANS, FDOM_state_succ, graph_plan_lemma_10_1]);







val graph_plan_lemma_11 = store_thm("graph_plan_lemma_11",
``∀s as vs. sat_precond_as(s, as) ==>
        (DRESTRICT (exec_plan(s, as_proj(as, vs))) vs = DRESTRICT (exec_plan(s,  as)) vs)``,
SRW_TAC[][]
THEN `(DRESTRICT (exec_plan (s,as_proj(as,vs))) vs =
      		 exec_plan (DRESTRICT s vs, as_proj(as, vs)))` by METIS_TAC[graph_plan_lemma_9]
THEN `?s'. (exec_plan (DRESTRICT s vs, as_proj(as, vs)) = DRESTRICT s' vs)` by 
     	   (SRW_TAC[][]
     	   THEN Q.EXISTS_TAC `(exec_plan(s, as_proj(as, vs)))`
	   THEN SRW_TAC[][])
THEN `DRESTRICT s' vs = DRESTRICT (exec_plan(s,as)) vs` by METIS_TAC[graph_plan_lemma_1]
THEN METIS_TAC[]
);




val graph_plan_lemma_12_1 = store_thm("graph_plan_lemma_12_1",
``!s s' vs x.
(DRESTRICT (s) vs = DRESTRICT (s') vs) ==>
(DRESTRICT (x) vs ⊑ s <=> DRESTRICT (x) vs ⊑ s')``,
SRW_TAC[][SUBMAP_DEF]
THEN EQ_TAC
THEN SRW_TAC[][]
THEN `FDOM(DRESTRICT s vs) = FDOM(DRESTRICT s' vs)` by SRW_TAC[][]
THEN FULL_SIMP_TAC(srw_ss())[FDOM_DRESTRICT, INTER_DEF, EXTENSION, fmap_EXT, DRESTRICT_DEF]
THEN METIS_TAC[FDOM_DRESTRICT]
);


val graph_plan_lemma_12_2 = store_thm("graph_plan_lemma_12_2",
``!a vs. (action_proj(action_proj(a, vs), vs)) = (action_proj(a, vs))``,
SRW_TAC[][action_proj_def]
);
val graph_plan_lemma_12_3 = store_thm("graph_plan_lemma_12_3",
``!s a vs. (FDOM (DRESTRICT (SND a) vs) = ∅) ==>
       (DRESTRICT (state_succ s a) vs = DRESTRICT s vs)``,
SRW_TAC[][action_proj_def]
THEN `FDOM (DRESTRICT (DRESTRICT (SND a) vs) vs) = EMPTY` by FULL_SIMP_TAC(srw_ss())[DRESTRICT_IDEMPOT]
THEN FULL_SIMP_TAC(srw_ss())[Once FDOM_DRESTRICT]
THEN `DISJOINT (FDOM (SND a)) vs` by FULL_SIMP_TAC(srw_ss())[FDOM_DRESTRICT, DISJOINT_DEF]
THEN METIS_TAC[graph_plan_lemma_1_2]); 

val graph_plan_lemma_12_4 = store_thm("graph_plan_lemma_12_4",
``!fm1 fm2 vs.  (fm2 SUBMAP fm1) 
       ==> ((DRESTRICT fm2 vs) SUBMAP (fm1) )``,
SRW_TAC[][SUBSET_DEF, SUBMAP_DEF]
THEN FULL_SIMP_TAC(srw_ss())[SUBSET_DEF, SUBMAP_DEF, FDOM_DRESTRICT, DRESTRICT_DEF]
);



val graph_plan_lemma_12 = store_thm("graph_plan_lemma_12",
``! as s s' vs.
sat_precond_as(s, as)  /\ (DRESTRICT s vs = DRESTRICT s' vs) 
==>sat_precond_as(s', as_proj(as, vs))``,
Induct_on`as` 
THEN SRW_TAC[][exec_plan_def, as_proj_def, sat_precond_as_def]
THEN `DRESTRICT (FST h) vs ⊑ s` by SRW_TAC[][graph_plan_lemma_12_4]
THENL
[
	SRW_TAC[][action_proj_def]
	THEN METIS_TAC[graph_plan_lemma_12_1]
	,	
	`FST (action_proj (h,vs))  ⊑ s'` by 
	     (SRW_TAC[][action_proj_def]
	     THEN  METIS_TAC[graph_plan_lemma_12_1])
	THEN `DRESTRICT (SND h) vs  = DRESTRICT (SND (action_proj(h, vs))) vs` by SRW_TAC[][action_proj_def]
	THEN `FST (action_proj(h, vs)) SUBMAP s` by SRW_TAC[][Once action_proj_def]
	THEN `DRESTRICT (state_succ s h) vs = DRESTRICT (state_succ s' (action_proj (h,vs))) vs` by METIS_TAC[graph_plan_lemma_4_1]
	THEN METIS_TAC[]
	,
	METIS_TAC[graph_plan_lemma_12_3]
]);


val graph_plan_lemma_13 = store_thm("graph_plan_lemma_13",
``!as s s' vs . sat_precond_as (s,as) ∧ (DRESTRICT s vs = DRESTRICT s' vs)
==> sat_precond_as (DRESTRICT s' vs,as_proj (as,vs))``,
Induct_on `as`
THEN SRW_TAC[][as_proj_def, sat_precond_as_def]
THEN `DRESTRICT (FST h) vs ⊑ DRESTRICT s vs` by SRW_TAC[][graph_plan_lemma_1_1_1]
THENL
[
	SRW_TAC[][action_proj_def]
	THEN METIS_TAC[]		
	,
	`FST (action_proj (h,vs))  ⊑ DRESTRICT s' vs` by 
	     (SRW_TAC[][action_proj_def]
	     THEN  METIS_TAC[graph_plan_lemma_12_1])
	THEN `DRESTRICT (SND h) vs  = DRESTRICT (SND (action_proj(h, vs))) vs` by SRW_TAC[][action_proj_def]
	THEN `FST (action_proj(h, vs)) SUBMAP s` by SRW_TAC[][Once action_proj_def, graph_plan_lemma_12_4]
	THEN `DRESTRICT (state_succ s h) vs = DRESTRICT (state_succ (DRESTRICT s' vs) (action_proj (h,vs))) vs` by 
	     METIS_TAC[graph_plan_lemma_4_1, DRESTRICT_IDEMPOT]
	THEN METIS_TAC[DRESTRICT_IDEMPOT, graph_plan_lemma_9_1_1]
	,
	METIS_TAC[graph_plan_lemma_12_3]		
]);



val graph_plan_lemma_14_1 = store_thm("graph_plan_lemma_14_1",
``!x. SND ((λa. (DRESTRICT (FST a) vs,SND a)) x) = SND x``,
SRW_TAC[][]
);

val graph_plan_lemma_14_2 = store_thm("graph_plan_lemma_14_2",
``!x y. (SND (x) = SND y)
     ==> ((\a. varset_action(a, vs)) x = (\a. varset_action(a, vs)) y)``,
SRW_TAC[][varset_action_def]
);
val graph_plan_lemma_14 = store_thm("graph_plan_lemma_14",
``!l f1 f2 x. MEM x (MAP f1 l) /\ f2 x /\ (!g. SND (f1 g) = SND g) /\ (!g h. (SND (g) = SND h) ==> (f2 g = f2 h))
     ==>
     ?y. MEM y (l) /\ f2 y``,
SRW_TAC[][]
THEN `?z. MEM z l /\ (x = f1 z)` by METIS_TAC[MEM_MAP ]
THEN METIS_TAC[]
);

val graph_plan_lemma_15_1 = store_thm("graph_plan_lemma_15_1",
``!l1 l2 l3 P. LENGTH (FILTER P l3) < LENGTH (FILTER P l2)
      ==> LENGTH (FILTER P (l1++l3)) < LENGTH (FILTER P (l1++l2))``,
METIS_TAC[LENGTH_APPEND, FILTER_APPEND_DISTRIB, LT_ADD_LCANCEL]);

val graph_plan_lemma_15_2= store_thm("graph_plan_lemma_15_2",
``!l1 l2 l3 P. LENGTH (FILTER P l3) < LENGTH (FILTER P l2)
      ==> LENGTH (FILTER P (l3++l1)) < LENGTH (FILTER P (l2++l1))``,
SRW_TAC[][LENGTH_APPEND, FILTER_APPEND_DISTRIB, LT_ADD_LCANCEL, ADD_SYM]);

val graph_plan_lemma_15 = store_thm("graph_plan_lemma_15",
``!l1 l2 l3 l4 P. LENGTH (FILTER P l2) < LENGTH (FILTER P l3)
      ==> LENGTH (FILTER P (l1++l2++l4)) < LENGTH (FILTER P (l1++l3++l4))``,
SRW_TAC[][LENGTH_APPEND, FILTER_APPEND_DISTRIB, LT_ADD_LCANCEL, ADD_SYM, ADD_ASSOC, graph_plan_lemma_15_1, graph_plan_lemma_15_2]);


val graph_plan_lemma_16_1_1 = store_thm("graph_plan_lemma_16_1_1",
``!s a.  (FDOM (SND a) = EMPTY) ==>
     	 ((state_succ s a) = s)``,
SRW_TAC[][state_succ_def, FUNION_DEF, SUBMAP_DEF, fmap_EXT]
);

val graph_plan_lemma_16_1 = store_thm("graph_plan_lemma_16_1",
``!s as. (exec_plan (s,as) = exec_plan (s,rem_effectless_act (as)))``,
Induct_on `as` 
THEN SRW_TAC[][rem_effectless_act_def, exec_plan_def, graph_plan_lemma_16_1_1]
THEN SRW_TAC[][rem_effectless_act_def, exec_plan_def, graph_plan_lemma_16_1_1]
);

val graph_plan_lemma_16_2 = store_thm("graph_plan_lemma_16_2",
``!as s. ( sat_precond_as (s, as) ==> sat_precond_as (s,rem_effectless_act (as)))``,
Induct_on`as`
THEN SRW_TAC[][sat_precond_as_def, rem_effectless_act_def]
THEN FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_16_1_1]);

val graph_plan_lemma_16_3 = store_thm("graph_plan_lemma_16_3",
``!as s. LENGTH (rem_effectless_act (as)) ≤ LENGTH as``,
Induct_on `as`
THEN SRW_TAC[][rem_effectless_act_def]
THEN ` LENGTH (rem_effectless_act as) ≤ (LENGTH as)` by SRW_TAC[][]
THEN DECIDE_TAC
);

val graph_plan_lemma_16_4 = store_thm("graph_plan_lemma_16_4",
``! A as. (set as ⊆ A ⇒ set (rem_effectless_act (as)) ⊆ A)``,
Induct_on`as`
THEN SRW_TAC[][rem_effectless_act_def]
);

val graph_plan_lemma_16_5 = store_thm("graph_plan_lemma_16_5",
``∀P as. LENGTH (FILTER P (rem_effectless_act (as))) ≤
       LENGTH (FILTER P as)``,
Induct_on`as`
THEN SRW_TAC[][rem_effectless_act_def]
THEN `LENGTH (FILTER P (rem_effectless_act as)) ≤  (LENGTH (FILTER P as))` by SRW_TAC[][]
THEN DECIDE_TAC
);
val graph_plan_lemma_16_6 = store_thm("graph_plan_lemma_16_6", 
``!as. no_effectless_act (rem_effectless_act (as))``,
Induct_on`as`
THEN SRW_TAC[][no_effectless_act_def, rem_effectless_act_def]);


val graph_plan_lemma_16_7 = store_thm("graph_plan_lemma_16_7",
``!as. no_effectless_act(as) =  EVERY (\a. FDOM(SND a) <> EMPTY) as ``,
Induct_on `as`
THEN SRW_TAC[][no_effectless_act_def, EVERY_DEF]);


val graph_plan_lemma_16_8 = store_thm("graph_plan_lemma_16_8",
``!P as. (EVERY P as)==> EVERY (P) (rem_effectless_act (as))``,
Induct_on `as`
THEN SRW_TAC[][rem_effectless_act_def]);



val graph_plan_lemma_16 = store_thm("graph_plan_lemma_16", 
`` !s A as.   (exec_plan (s,as) = exec_plan (s,rem_effectless_act (as))) ∧
     (sat_precond_as (s, as) ==> sat_precond_as (s,rem_effectless_act (as))) ∧
     LENGTH (rem_effectless_act (as)) ≤ LENGTH as ∧
     (set as ⊆ A ⇒ set (rem_effectless_act (as)) ⊆ A) ∧
     no_effectless_act (rem_effectless_act (as)) /\
     ∀P.
       LENGTH (FILTER P (rem_effectless_act (as))) ≤
       LENGTH (FILTER P as)``,
METIS_TAC[graph_plan_lemma_16_1, graph_plan_lemma_16_2, graph_plan_lemma_16_3, graph_plan_lemma_16_4, graph_plan_lemma_16_5, graph_plan_lemma_16_6]
);



val graph_plan_lemma_17 = store_thm("graph_plan_lemma_17",
``!as_1 as_2 as s. (as_1++as_2 = as) /\ sat_precond_as(s,as)
==>(sat_precond_as(s,as_1) /\ sat_precond_as( exec_plan(s, as_1),as_2))``,
Induct_on`as`
THEN SRW_TAC[][exec_plan_def]
THEN Cases_on`as_1`
THEN FULL_SIMP_TAC(srw_ss())[rich_listTheory.IS_PREFIX_NIL, isPREFIX_THM, exec_plan_def, sat_precond_as_def]
THEN SRW_TAC[][ ]
);





val graph_plan_lemma_18_1 = store_thm("graph_plan_lemma_18_1",
``!as vs. (as_proj_child(as, vs)) =  (FILTER (\a. varset_action(a, vs) /\ FDOM (SND a) ≠ ∅) (MAP (\ a. (DRESTRICT (FST a) vs, (SND a) )) as))``,
Induct_on `as` 
THEN SRW_TAC[][as_proj_child_def, action_proj_def]);

val graph_plan_lemma_18 = store_thm("graph_plan_lemma_18",
``!as vs. (as_proj_child(rem_effectless_act(as), vs)) =  FILTER (\a. varset_action(a, vs)) (MAP (\ a. (DRESTRICT (FST a) vs, (SND a) )) (rem_effectless_act(as)))``,
Induct_on `as` 
THEN FULL_SIMP_TAC(srw_ss())[as_proj_child_def, action_proj_def, rem_effectless_act_def]
THEN SRW_TAC[][]);



val graph_plan_lemma_19 = store_thm("graph_plan_lemma_19",
``!as s. set as SUBSET s ==> (!a. MEM a as ==> a IN s)``,
Induct_on `as` 
THEN SRW_TAC[][]
THEN SRW_TAC[][]);

val child_parent_rel_def 
   = Define `(child_parent_rel(PROB, vs)
     = (dep_var_set(PROB, (FDOM PROB.I) DIFF vs, vs)) /\ ~(dep_var_set(PROB, vs,  (FDOM PROB.I) DIFF vs)))`;

val graph_plan_lemma_20 = store_thm("graph_plan_lemma_20",
``!l P. EVERY P l ==> (LENGTH(FILTER P l) = LENGTH l)``,
SRW_TAC[][GSYM FILTER_EQ_ID]);

val graph_plan_lemma_21 = store_thm("graph_plan_lemma_21",
``!P1 P2 l. EVERY P1 l /\ EVERY P2 l = EVERY (\a. P1 a /\ P2 a) l``,
Induct_on `l`
THEN SRW_TAC[][]
THEN EQ_TAC
THEN SRW_TAC[][]
THEN METIS_TAC[]);




val child_parent_lemma_1_1_1 = store_thm("child_parent_lemma_1_1_1",
``! a vs. varset_action (a,vs) ==>  (DRESTRICT (SND a) vs = SND a )``,
SRW_TAC[][varset_action_def]
THEN SRW_TAC[][graph_plan_lemma_2_3_8_5]);

val child_parent_lemma_1_1_2 = store_thm("child_parent_lemma_1_1_2",
``! PROB a vs. (planning_problem PROB ∧ a IN PROB.A 
     ∧ child_parent_rel(PROB, vs) 
      /\ (FDOM (SND a) <> EMPTY))
     ==>
     (varset_action(a, vs) <=> ~varset_action(a, FDOM PROB.I DIFF vs))``,

FULL_SIMP_TAC(srw_ss())[varset_action_def, dep_var_set_def, dep_def, SUBSET_DEF, DISJOINT_DEF, INTER_DEF, EXTENSION, planning_problem_def, SPECIFICATION, child_parent_rel_def]
THEN METIS_TAC[]
);

val child_parent_lemma_1_1_3 = store_thm("child_parent_lemma_1_3_1",
``!x vs. FDOM (DRESTRICT x vs) <> EMPTY  ==> (FDOM  x) <> EMPTY``,
SRW_TAC[][FDOM_DRESTRICT, INTER_DEF, EXTENSION]
THEN METIS_TAC[]);

val child_parent_lemma_1_1_3 = store_thm("child_parent_lemma_1_3_1",
``!x vs. FDOM (DRESTRICT x vs) <> EMPTY  ==> (FDOM  x) <> EMPTY``,
SRW_TAC[][FDOM_DRESTRICT, INTER_DEF, EXTENSION]
THEN METIS_TAC[]);



val child_parent_lemma_1_1_4 = store_thm("child_parent_lemma_1_4_1",
``!PROB a vs. (child_parent_rel(PROB, vs)) /\ (a IN PROB.A) /\ ~(DISJOINT (FDOM (SND a)) (FDOM(PROB.I) DIFF vs))
==> (DISJOINT  (FDOM (SND a)) vs)``,
SRW_TAC[][dep_var_set_def, dep_def, DISJOINT_DEF, INTER_DEF, EXTENSION, child_parent_rel_def]
THEN METIS_TAC[]
);

val child_parent_lemma_1_1_5 = store_thm("child_parent_lemma_1_5_1",
``!PROB a vs. (planning_problem(PROB)  /\ (a IN PROB.A) /\ ( ~varset_action (a,vs)))
    ==> ~(DISJOINT (FDOM (SND a)) (FDOM(PROB.I) DIFF vs))``,
FULL_SIMP_TAC(srw_ss())[DISJOINT_DEF, INTER_DEF, varset_action_def, EXTENSION,FILTER, planning_problem_def, MEM, SUBSET_DEF]
THEN SRW_TAC[][]
THEN METIS_TAC[]);


val child_parent_lemma_1_1 = store_thm("child_parent_lemma_1_1",
``∀PROB as vs.
     (planning_problem PROB ∧ set as ⊆ PROB.A 
     ∧ child_parent_rel(PROB, vs))
       		   ==>
     (as_proj_child(as,vs) = as_proj(as,vs))``,
Induct_on `as`
THEN SRW_TAC[][as_proj_child_def, as_proj_def] 
THENL
[
	FULL_SIMP_TAC(srw_ss())[child_parent_lemma_1_1_1, varset_action_def, action_proj_def]	
	,
	METIS_TAC[as_proj_child_def, as_proj_def]
	,
	FULL_SIMP_TAC(srw_ss())[child_parent_lemma_1_1_1, varset_action_def]	
	,
	FULL_SIMP_TAC(srw_ss())[]
     	THEN `~varset_action(h,vs)` by FULL_SIMP_TAC(srw_ss())[varset_action_def, planning_problem_def]
     	THEN METIS_TAC[child_parent_lemma_1_1_4,  child_parent_lemma_1_1_5, DISJOINT_DEF, FDOM_DRESTRICT, child_parent_lemma_1_1_3]
	,
	METIS_TAC[as_proj_child_def, as_proj_def]
]);

val as_proj_parent_def = Define `as_proj_parent(as, vs) = 
    (FILTER (λa. ~varset_action (a,vs) /\ (FDOM (SND a)) <> EMPTY ) as)`; 

val child_parent_lemma_1_2_1_1 = store_thm("child_parent_lemma_1_2_1_1",
``!PROB vs a. (child_parent_rel(PROB, vs) /\ a IN PROB.A /\  ~ (DISJOINT (FDOM(SND a)) (FDOM(PROB.I) DIFF vs))) 
	      			==>  DISJOINT (FDOM(FST a)) vs``,
SRW_TAC[][child_parent_rel_def, dep_var_set_def, dep_def, DISJOINT_DEF, DIFF_DEF, EXTENSION]
THEN METIS_TAC[]
);

val child_parent_lemma_1_2_1 = store_thm("child_parent_lemma_1_2_1",
``!PROB vs a. (child_parent_rel(PROB, vs) /\ planning_problem(PROB) /\ a IN PROB.A /\ varset_action(a, FDOM(PROB.I) DIFF vs) 
	       /\ (FDOM (SND a) <> EMPTY))
	      			==>  (FDOM (FST(a))) SUBSET (FDOM(PROB.I) DIFF vs)``,
SRW_TAC[][planning_problem_def]
THEN `~DISJOINT (FDOM (SND a)) (FDOM PROB.I DIFF vs)` by 
     (FULL_SIMP_TAC(srw_ss())[child_parent_rel_def, dep_var_set_def, dep_def, SUBSET_DEF, DISJOINT_DEF, INTER_DEF, varset_action_def, EXTENSION]
     THEN METIS_TAC[])
THEN `DISJOINT (FDOM (FST a)) vs` by METIS_TAC[child_parent_lemma_1_2_1_1]
THEN METIS_TAC[SUBSET_DIFF]);


val child_parent_lemma_1_2 = store_thm("child_parent_lemma_1_2",
``∀PROB as vs.
     (planning_problem PROB ∧ set as ⊆ PROB.A (* /\ vs ⊆ FDOM PROB.I *)
     ∧ child_parent_rel(PROB, vs))
       		   ==>
     (as_proj_parent(as,vs) = as_proj(as,FDOM(PROB.I) DIFF vs))``,
Induct_on `as`
THEN SRW_TAC[][as_proj_parent_def, as_proj_def]
THENL
[
	`varset_action (h,FDOM PROB.I DIFF vs)` by METIS_TAC[child_parent_lemma_1_1_2]
	THEN ASSUME_TAC(child_parent_lemma_1_2_1)
	THEN SRW_TAC[][action_proj_def]
	THEN FULL_SIMP_TAC(srw_ss())[varset_action_def]
	THEN SRW_TAC[][graph_plan_lemma_2_3_8_5]
	,
	METIS_TAC[as_proj_parent_def, as_proj_def]
	,
	`varset_action (h,FDOM PROB.I DIFF vs)` by METIS_TAC[child_parent_lemma_1_1_2]
	THEN FULL_SIMP_TAC(srw_ss())[varset_action_def, FDOM_DRESTRICT, INTER_DEF, SUBSET_DEF, EXTENSION]	
	THEN METIS_TAC[]
	,
	FULL_SIMP_TAC(srw_ss())[varset_action_def, FDOM_DRESTRICT, INTER_DEF, SUBSET_DEF, EXTENSION]	
	THEN METIS_TAC[]
	,	
        FULL_SIMP_TAC(srw_ss())[as_proj_parent_def]
]);




val child_parent_lemma_1 = store_thm("child_parent_lemma_1",
``∀PROB as vs.
     (planning_problem PROB ∧ set as ⊆ PROB.A 
     ∧ child_parent_rel(PROB, vs))
       		   ==>
     ((as_proj_child(as,vs) = as_proj(as,vs))
      /\ (as_proj_parent(as,vs) = as_proj(as,FDOM(PROB.I) DIFF vs)))``,
METIS_TAC[child_parent_lemma_1_1, child_parent_lemma_1_2]);





val child_parent_lemma_xx = store_thm("child_parent_lemma_xx",
``!PROB a vs. (planning_problem(PROB) /\ child_parent_rel(PROB, vs) /\ (a IN PROB.A) /\ ~(varset_action(a, vs))) 
==> (DISJOINT  (FDOM (SND a)) vs)``,
SRW_TAC[][varset_action_def,dep_var_set_def, dep_def, DISJOINT_DEF, INTER_DEF, EXTENSION, child_parent_rel_def, planning_problem_def]
THEN FULL_SIMP_TAC(srw_ss())[SUBSET_DEF]
THEN METIS_TAC[]
);

val child_parent_lemma_xxx = store_thm("child_parent_lemma_xxx",
``!PROB a vs. (planning_problem(PROB) /\ child_parent_rel(PROB, vs) /\ (a IN PROB.A) /\ (varset_action(a, vs))) 
==> (DISJOINT  (FDOM (SND a)) ((FDOM PROB.I) DIFF vs))``,
SRW_TAC[][varset_action_def,dep_var_set_def, dep_def, DISJOINT_DEF, INTER_DEF, EXTENSION, child_parent_rel_def, planning_problem_def]
THEN FULL_SIMP_TAC(srw_ss())[SUBSET_DEF]
THEN METIS_TAC[]
);


val child_parent_lemma_xxxx = store_thm("child_parent_lemma_xxxx",
``!PROB a vs. (planning_problem(PROB) /\ child_parent_rel(PROB, vs) /\ (a IN PROB.A) /\ (varset_action(a, FDOM(PROB.I) DIFF vs))) 
==> (DISJOINT  (FDOM (SND a)) vs)``,
SRW_TAC[][varset_action_def,dep_var_set_def, dep_def, DISJOINT_DEF, INTER_DEF, EXTENSION, child_parent_rel_def, planning_problem_def]
THEN FULL_SIMP_TAC(srw_ss())[SUBSET_DEF]
THEN METIS_TAC[]
);


val child_parent_lemma_2_1_1_1_1_1 = store_thm("child_parent_lemma_2_1_1_1_1_1",
``! PROB s as vs. (planning_problem(PROB) /\ (set as SUBSET PROB.A)  /\ child_parent_rel(PROB, vs)) 
	==>
	((DRESTRICT s vs) = (DRESTRICT (exec_plan (s,as_proj_parent(as, vs))) vs))``,
Induct_on `as`
THEN SRW_TAC[][as_proj_parent_def, exec_plan_def]
THEN REWRITE_TAC[GSYM as_proj_parent_def]
THEN METIS_TAC[child_parent_lemma_1_1_5, graph_plan_lemma_1_2, child_parent_lemma_1_1_4] 
);


val child_parent_lemma_2_1_1_1_1 = store_thm("child_parent_lemma_2_1_1_1_1",
``!PROB s s' as vs. (planning_problem(PROB) /\ (set as SUBSET PROB.A) /\ child_parent_rel(PROB, vs)
	     /\ ((DRESTRICT s vs) = (DRESTRICT (exec_plan(s,as)) vs))) 
     	    ==>
            ((DRESTRICT s vs) = (DRESTRICT (exec_plan (s,as_proj_parent(as, vs))) vs))``,
METIS_TAC[child_parent_lemma_2_1_1_1_1_1]);



val child_parent_lemma_2_1_1_1_2 = store_thm("child_parent_lemma_2_1_1_1_2",
``!P l. (?x. MEM x l /\ P x) 
==> LENGTH(FILTER (\x. ~ (P x)) l) < LENGTH(l)``,
Induct_on`l`
THEN SRW_TAC[][]
THEN ASSUME_TAC (Q.SPEC `l` (Q.SPEC `(λx. ¬P x)` rich_listTheory.LENGTH_FILTER_LEQ))
THEN METIS_TAC[LESS_EQ_IMP_LESS_SUC]);

val child_parent_lemma_2_1_1_1_3_1_1 = store_thm("child_parent_lemma_2_1_1_1_3_1_1",
``!P l. LENGTH (FILTER (\a. P a) (FILTER (\a. ~P a)  l  )) = 0``,
Induct_on`l`
THEN  SRW_TAC[][]
);

val child_parent_lemma_2_1_1_1_3_1 = store_thm("child_parent_lemma_2_1_1_1_3_1",
``!P P2 l. (?a. (MEM a l /\ P a )) ==> 
LENGTH (FILTER (\a. P a) (FILTER (\a. ~P a /\ P2 a)  l  )) < LENGTH ((FILTER (\a. P a)  l  ))``,
Induct_on`l`
THEN SRW_TAC[][]
THENL
[
	METIS_TAC[]
	,
	FULL_SIMP_TAC(srw_ss())[]
	THEN `(LENGTH (FILTER (λa. P a) (FILTER (λa. ¬P a ∧ P2 a) l))) <= (LENGTH (FILTER (λa. P a) l))` by METIS_TAC[rich_listTheory.LENGTH_FILTER_LEQ, FILTER_COMM]
     	THEN DECIDE_TAC
	,	
	FULL_SIMP_TAC(srw_ss())[]
	THEN `(LENGTH (FILTER (λa. P a) (FILTER (λa. ¬P a ∧ P2 a) l))) <= (LENGTH (FILTER (λa. P a) l))` by METIS_TAC[rich_listTheory.LENGTH_FILTER_LEQ, FILTER_COMM]
     	THEN DECIDE_TAC
	,
	FULL_SIMP_TAC(srw_ss())[]
	,
	METIS_TAC[]
]);


val child_parent_lemma_2_1_1_1_3 = store_thm("child_parent_lemma_2_1_1_1_3",
``!as vs. (?a. MEM a as /\ ((\a. varset_action(a,vs)) a))
       ==> LENGTH
        (FILTER (λa. varset_action (a,vs))
           (as_proj_parent(as, vs))) <
      LENGTH (FILTER (λa. varset_action (a,vs)) as)``,
SRW_TAC[][as_proj_parent_def]
THEN METIS_TAC[Q.SPEC ` as` ( Q.SPEC  `(\a. FDOM (SND a) ≠ ∅) ` (Q.ISPEC `(\a. varset_action(a, vs))` child_parent_lemma_2_1_1_1_3_1))]);

val child_parent_lemma_2_1_1_1 = store_thm("child_parent_lemma_2_1_1_1",
``!PROB s as vs. (planning_problem(PROB) /\ (set as SUBSET PROB.A) 
	    /\ child_parent_rel(PROB, vs)
	    /\ ((DRESTRICT s vs) = (DRESTRICT (exec_plan(s,as)) vs))
	    /\ (?a. MEM a as /\ ((\a. varset_action(a,vs)) a))) 
     	    ==>
            ( ((DRESTRICT (exec_plan(s,as)) vs) = (DRESTRICT (exec_plan (s,as_proj_parent(as, vs))) vs)) /\ (LENGTH( FILTER (\a. varset_action(a,vs)) (as_proj_parent(as, vs))) < LENGTH(FILTER (\a. varset_action(a,vs)) as)) )``,
METIS_TAC[child_parent_lemma_2_1_1_1_1, child_parent_lemma_2_1_1_1_3]);




val child_parent_lemma_2_1_1_2 = store_thm("child_parent_lemma_2_1_1_2",
``!PROB s as vs. (planning_problem(PROB) /\ (set as SUBSET PROB.A)
	    /\ child_parent_rel(PROB, vs) /\ sat_precond_as (s,as))
	    ==>
	    (sat_precond_as (s,as_proj_parent(as, vs)))``,
METIS_TAC[graph_plan_lemma_12,  child_parent_lemma_1]);


val child_parent_lemma_2_1_1 = store_thm("child_parent_lemma_2_1_1",
``!PROB vs as s.
	  (planning_problem(PROB)    /\ (FDOM s = FDOM PROB.I) 
	  /\ (set as SUBSET PROB.A) /\ (FINITE vs) 
	  /\ child_parent_rel(PROB, vs))
	  ==>
	  (?as'. (exec_plan(s, as') = exec_plan(s, as))
	  /\ (LENGTH( FILTER (\a. varset_action(a, vs)) as')) <= (2**CARD(vs)) /\ set as' SUBSET PROB.A)``,
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
      THEN Cases_on `LENGTH (FILTER (λa. varset_action (a,vs)) ( (rem_condless_act (s,[],p)))) > 2 ** CARD (vs)`
      THENL
      [
	Cases_on `LENGTH (FILTER (λa. varset_action (a,vs)) ( (rem_effectless_act (rem_condless_act (s,[],p))))) > 2 ** CARD (vs)`
	THENL
	[
		
	      `(∃as1 as2 as3. (as1++as2++as3 = as_proj_child((rem_effectless_act (rem_condless_act (s,[],p))),vs)) ∧ (exec_plan(DRESTRICT s vs,as1 ++ as2) = exec_plan (DRESTRICT s vs,as1)) ∧ as2 ≠ [])` by 
		   (`LENGTH (as_proj_child((rem_effectless_act (rem_condless_act (s,[],p))), vs) ) > 2 ** CARD(vs)` by FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_3, graph_plan_lemma_16_6]
		   THEN `plan(PROB with <|G := exec_plan (s,rem_effectless_act (rem_condless_act (s,[],p))); I := s|>, rem_effectless_act (rem_condless_act (s,[],p)))` by SRW_TAC[][graph_plan_lemma_6, graph_plan_lemma_16, graph_plan_lemma_7]
		   THEN `LENGTH (as_proj((rem_effectless_act (rem_condless_act (s,[],p))),vs)) > 2 ** CARD(vs)` by METIS_TAC[child_parent_lemma_1, graph_plan_lemma_7, graph_plan_lemma_16]
		   THEN `sat_precond_as(s , (rem_effectless_act (rem_condless_act (s,[],p))))` by METIS_TAC[graph_plan_lemma_7, graph_plan_lemma_16]
		   THEN `sat_precond_as(((PROB with <|G := exec_plan (s,(rem_effectless_act (rem_condless_act (s,[],p)))); I := s|>).I) , (rem_effectless_act (rem_condless_act (s,[],p))))` by SRW_TAC[][]
		   THEN `as_proj_child((rem_effectless_act (rem_condless_act (s,[],p))),vs)
		   		=as_proj((rem_effectless_act (rem_condless_act (s,[],p))),vs)` by METIS_TAC[GSYM child_parent_lemma_1, graph_plan_lemma_7, graph_plan_lemma_16]
		   THEN `(∃as1 as2 as3. (as1++as2++as3 = as_proj((rem_effectless_act (rem_condless_act (s,[],p))),vs)) ∧ (exec_plan((prob_proj((PROB with <|G := exec_plan (s,rem_effectless_act (rem_condless_act (s,[],p))); I := s|>), vs)).I,as1 ++ as2) = exec_plan ((prob_proj((PROB with <|G := exec_plan (s,rem_effectless_act (rem_condless_act (s,[],p))); I := s|>), vs)).I,as1)) ∧ as2 ≠ [])` by METIS_TAC[graph_plan_lemma_2, prob_proj_def]
		   THEN FULL_SIMP_TAC(srw_ss())[prob_proj_def]
		   THEN METIS_TAC[])
                THEN FULL_SIMP_TAC(srw_ss())[exec_plan_Append]
	      	THEN `?p_1 p_2 p_3. ((p_1 ++ p_2 ++ p_3 = (rem_effectless_act (rem_condless_act (s,[],p)))) /\ (as2 = as_proj(p_2, vs)) /\ (as1 = as_proj(p_1, vs)))` by METIS_TAC[graph_plan_lemma_8, child_parent_lemma_1, graph_plan_lemma_7, graph_plan_lemma_16]
		   THEN `DRESTRICT (exec_plan (exec_plan (s,as1),as2)) vs = DRESTRICT (exec_plan(s,as1)) vs` by SRW_TAC[][graph_plan_lemma_9] 
		   THEN `sat_precond_as(s, p_1)` by METIS_TAC[graph_plan_lemma_17, graph_plan_lemma_16, graph_plan_lemma_7] 
		THEN `DRESTRICT (exec_plan (s,as1)) vs = DRESTRICT (exec_plan (s,p_1)) vs` by SRW_TAC[][graph_plan_lemma_11]
		THEN `sat_precond_as(exec_plan(s, p_1), p_2)` by METIS_TAC[graph_plan_lemma_17, graph_plan_lemma_16, graph_plan_lemma_7] 
		THEN `DRESTRICT (exec_plan (exec_plan (s,p_1),as2)) vs = DRESTRICT (exec_plan (exec_plan (s,p_1),p_2)) vs` by SRW_TAC[][graph_plan_lemma_11]
		THEN `set (p_1) SUBSET PROB.A` by (SRW_TAC[][] THEN FULL_SIMP_TAC(srw_ss())[] THEN METIS_TAC[LIST_TO_SET_APPEND, APPEND_ASSOC, UNION_SUBSET, graph_plan_lemma_7, graph_plan_lemma_16])
		THEN `set (p_2) SUBSET PROB.A` by (SRW_TAC[][] THEN FULL_SIMP_TAC(srw_ss())[] THEN METIS_TAC[LIST_TO_SET_APPEND, APPEND_ASSOC, UNION_SUBSET, graph_plan_lemma_7, graph_plan_lemma_16])
	      	THEN `set (p_3) SUBSET PROB.A` by (SRW_TAC[][] THEN FULL_SIMP_TAC(srw_ss())[] THEN METIS_TAC[LIST_TO_SET_APPEND, APPEND_ASSOC, UNION_SUBSET, graph_plan_lemma_7, graph_plan_lemma_16])
		THEN `(DRESTRICT (exec_plan (exec_plan (s,p_1),p_2)) vs = DRESTRICT (exec_plan (exec_plan (s,p_1), as_proj_parent(p_2, vs))) vs)
	      	   /\ LENGTH ( FILTER (λa. varset_action (a,vs)) (as_proj_parent(p_2, vs))) < LENGTH (FILTER (λa. varset_action (a,vs)) p_2)` by
   		   	(`(∃a. MEM a p_2 ∧ ( varset_action (a,vs)) )` by 
     			       (`(∃a. MEM a (as_proj_child(p_2, vs)) ∧ ( varset_action (a,vs) /\ FDOM (SND a) ≠ ∅) )` by
     	       	      	       	     (`as2 = as_proj_child (p_2,vs)` by METIS_TAC[GSYM child_parent_lemma_1 ]
				     THEN `FILTER (λa. varset_action (a,vs) ∧ FDOM (SND a) ≠ ∅) (MAP (λa. (DRESTRICT (FST a) vs,SND a)) p_2) <> []` by METIS_TAC[GSYM as_proj_child_def]
     				     THEN ` ?a. MEM a (MAP (λa. (DRESTRICT (FST a) vs,SND a)) p_2) /\ varset_action (a,vs) /\  FDOM (SND a) ≠ ∅` by FULL_SIMP_TAC(srw_ss())[FILTER_NEQ_NIL]
				     THEN Q.EXISTS_TAC `a`
				     THEN REWRITE_TAC[as_proj_child_def]
				     THEN SRW_TAC[][MEM_FILTER])
				     THEN FULL_SIMP_TAC(srw_ss())[as_proj_child_def]				     
				     THEN METIS_TAC[Q.SPEC`a`( Q.ISPEC `(\a. varset_action(a,vs))` ( Q.ISPEC `(λa. (DRESTRICT (FST a) vs,SND a))` ( Q.SPEC `p_2` graph_plan_lemma_14))), graph_plan_lemma_14_1, graph_plan_lemma_14_2, MEM_FILTER])
			THEN `DRESTRICT (exec_plan (exec_plan (s,p_1),p_2)) vs = DRESTRICT (exec_plan (s,p_1)) vs` by METIS_TAC[graph_plan_lemma_11, graph_plan_lemma_9] 
			THEN METIS_TAC[child_parent_lemma_2_1_1_1])
	        THEN `set (( p_1 ++ (as_proj_parent(p_2, vs)) ++ p_3)) SUBSET PROB.A` by SRW_TAC[][graph_plan_lemma_6_2, as_proj_parent_def]
		THEN `LENGTH (FILTER (λa. varset_action (a,vs)) ( p_1 ++ (as_proj_parent(p_2, vs)) ++ p_3)) < LENGTH (FILTER (λa. varset_action (a,vs)) (p_1 ++ p_2 ++ p_3))` by METIS_TAC[graph_plan_lemma_15]

		THEN `(DRESTRICT (exec_plan (exec_plan (s,p_1),p_2)) (FDOM s DIFF vs) = DRESTRICT (exec_plan (exec_plan (s,p_1), as_proj_parent(p_2, vs))) (FDOM s DIFF vs))` by
		     (`(∀a. MEM a p_2 ∧ (λa. varset_action (a,vs) \/ (FDOM (SND a) = EMPTY)) a ⇒  DISJOINT (FDOM (SND a)) (FDOM s DIFF vs))` by 
		     	   (SRW_TAC[][]
			   THEN `a IN PROB.A` by METIS_TAC[graph_plan_lemma_19]
		     	   THEN METIS_TAC[child_parent_lemma_xxx, DISJOINT_EMPTY])
	             THEN `sat_precond_as (exec_plan (s,p_1),as_proj_parent(p_2, vs))` by METIS_TAC[child_parent_lemma_2_1_1_2]
		     THEN ASSUME_TAC(Q.ISPEC`(\a. varset_action(a,vs) \/ ((FDOM (SND a)) = EMPTY))` (Q.SPEC `(FDOM PROB.I) DIFF vs` ( Q.SPEC `p_2` (Q.SPEC `exec_plan (s,p_1)` ( Q.SPEC `exec_plan (s,p_1)` graph_plan_lemma_4)))))
		     THEN REWRITE_TAC[as_proj_parent_def]
		     THEN SRW_TAC[][]
		     THEN METIS_TAC[Q.ISPEC`(\a. varset_action(a,vs) \/ ((FDOM (SND a)) = EMPTY))` (Q.SPEC `(FDOM PROB.I) DIFF vs` ( Q.SPEC `p_2` (Q.SPEC `exec_plan (s,p_1)` ( Q.SPEC `exec_plan (s,p_1)` graph_plan_lemma_4)))), as_proj_parent_def])		
		THEN `exec_plan (exec_plan (s,p_1), p_2) = exec_plan (exec_plan (s,p_1), as_proj_parent(p_2, vs))` by
		     (`set ((as_proj_parent(p_2, vs))) SUBSET PROB.A` by SRW_TAC[][graph_plan_lemma_6_2, as_proj_parent_def]
		     THEN METIS_TAC[graph_plan_lemma_5, graph_plan_lemma_6_1, as_proj_parent_def])
		THEN `exec_plan (s,rem_effectless_act (rem_condless_act (s,[],p))) = exec_plan (s,p_1 ++ as_proj_parent(p_2, vs) ++ p_3)` by  
	      	     (`exec_plan (s,p_1++ p_2++p_3) = exec_plan (s,p_1 ++ as_proj_parent(p_2, vs) ++ p_3)` by FULL_SIMP_TAC(srw_ss())[exec_plan_Append]
		     THEN SRW_TAC[][] THEN METIS_TAC[])
		THEN `exec_plan (s,p_1 ++ as_proj_parent(p_2, vs) ++ p_3) = exec_plan(s, p)` by
		     METIS_TAC[graph_plan_lemma_7, graph_plan_lemma_16]
     		THEN `LENGTH (FILTER (λa. varset_action (a,vs)) (p_1 ++ p_2 ++ p_3)) <= LENGTH (FILTER (λa. varset_action (a,vs)) (p))` by 
		     (SRW_TAC[][]
		     THEN ASSUME_TAC(Q.SPEC `s` (Q.SPEC `PROB`(Q.SPEC`p`  graph_plan_lemma_7))) THEN ASSUME_TAC(Q.ISPEC`(rem_condless_act (s,[],p))` (Q.SPEC `PROB.A`(Q.SPEC`s` graph_plan_lemma_16))) 
		     THEN `LENGTH (FILTER (λa. varset_action (a,vs)) (rem_condless_act (s,[],p))) ≤ LENGTH (FILTER (λa. varset_action (a,vs)) p)` by SRW_TAC[][]
		     THEN `LENGTH (FILTER (λa. varset_action (a,vs)) (rem_effectless_act(rem_condless_act (s,[],p)))) ≤ LENGTH (FILTER (λa. varset_action (a,vs)) (rem_condless_act (s,[],p)))` by SRW_TAC[][] 
		     THEN SRW_TAC[][]
		     THEN DECIDE_TAC)
		THEN `LENGTH (FILTER (λa. varset_action (a,vs)) (p_1 ++ as_proj_parent(p_2, vs) ++ p_3))
	      	    < LENGTH (FILTER (λa. varset_action (a,vs)) (p))` by DECIDE_TAC		    		    
	      	THEN METIS_TAC[]
		,
		FULL_SIMP_TAC(srw_ss())[NOT_LESS, GREATER_DEF]
		THEN ASSUME_TAC(Q.SPEC `s` (Q.SPEC `PROB.A`(Q.SPEC`p`  graph_plan_lemma_7))) 
		THEN ASSUME_TAC(Q.ISPEC`(rem_condless_act (s,[],p))` (Q.SPEC `PROB.A`(Q.SPEC`s` graph_plan_lemma_16)))
		THEN `exec_plan(s, p) = exec_plan(s, rem_condless_act(s,[],p))` by SRW_TAC[][]  
		THEN `(exec_plan (s,rem_condless_act (s,[],p)) = exec_plan (s,rem_effectless_act (rem_condless_act (s,[],p))))` by SRW_TAC[][]
		THEN `LENGTH (FILTER (λa. varset_action (a,vs)) (rem_effectless_act (rem_condless_act (s,[],p)))) < LENGTH (FILTER (λa. varset_action (a,vs)) p)`
		     by DECIDE_TAC
		THEN Q.EXISTS_TAC `(rem_effectless_act (rem_condless_act (s,[],p)))`
		THEN SRW_TAC[][]
		THEN METIS_TAC[]
	]
	,
	FULL_SIMP_TAC(srw_ss())[NOT_LESS, GREATER_DEF]
	THEN ASSUME_TAC(Q.SPEC `s` (Q.SPEC `PROB.A`(Q.SPEC`p`  graph_plan_lemma_7))) 
	THEN `exec_plan(s, p) = exec_plan(s, rem_condless_act(s,[],p))` by SRW_TAC[][]  
	THEN `LENGTH (FILTER (λa. varset_action (a,vs)) ((rem_condless_act (s,[],p)))) < LENGTH (FILTER (λa. varset_action (a,vs)) p)`
	     by DECIDE_TAC
	THEN METIS_TAC[]
      ])
THEN ASSUME_TAC(Q.SPEC  `2 ** CARD vs` (Q.ISPEC `(λas''. LENGTH (FILTER (λa. varset_action (a,vs)) as''))` ( Q.ISPEC `(λas''. (exec_plan (s,as'') = exec_plan (s,as)) ∧ set as'' ⊆ PROB.A)` general_theorem)))
THEN METIS_TAC[]);


val child_parent_lemma_2_1_2_1 = store_thm("child_parent_lemma_2_1_2_1",
``!PROB vs as. (child_parent_rel(PROB, vs) /\ set as SUBSET PROB.A /\ planning_problem(PROB)) ==>
	(as_proj_parent (as,vs) = FILTER (λa. varset_action (a, FDOM(PROB.I) DIFF vs) ∧ FDOM (SND a) ≠ ∅) as)``,
Induct_on `as`
THEN SRW_TAC[][as_proj_parent_def]
THEN SRW_TAC[][GSYM as_proj_parent_def]
THEN FULL_SIMP_TAC(srw_ss())[GSYM as_proj_parent_def, child_parent_lemma_1_1_2]
THEN METIS_TAC[child_parent_lemma_1_1_2]);


val child_parent_lemma_2_1_2_2_2 = store_thm("child_parent_lemma_2_1_2_2_2",
``!P l. (FILTER (\x. P x) l = []) ⇔ EVERY (λx. ¬P x) l``,
Induct_on `l`
THEN SRW_TAC[][]
);

val child_parent_lemma_2_1_2_2 = store_thm("child_parent_lemma_2_1_2_2",
``!PROB vs as s. (child_parent_rel(PROB, vs) /\ set as SUBSET PROB.A /\ planning_problem(PROB)
	       /\ EVERY (\a. varset_action(a, FDOM(PROB.I) DIFF vs)) as) ==>
	( DRESTRICT s vs = DRESTRICT (exec_plan(s, as)) vs)``,
SRW_TAC[][]
THEN `(∀a. MEM a as  ⇒ DISJOINT (FDOM (SND a)) vs)` by 
      (SRW_TAC[][]
      THEN FULL_SIMP_TAC(srw_ss())[EVERY_MEM]
      THEN METIS_TAC[child_parent_lemma_xxxx, graph_plan_lemma_19])
THEN `EVERY (\a. DISJOINT (FDOM (SND a)) vs) as` by FULL_SIMP_TAC(srw_ss())[EVERY_MEM ]
THEN `EVERY (\a. DISJOINT (FDOM (SND a)) vs) (rem_condless_act(s, [], as))` by FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_7_7]
THEN FULL_SIMP_TAC(srw_ss())[EVERY_MEM]
THEN SRW_TAC[][]
THEN `(exec_plan(s, as) = exec_plan(s, rem_condless_act(s, [], as))) /\ sat_precond_as(s, rem_condless_act(s, [], as))` by SRW_TAC[][Once graph_plan_lemma_7_1, graph_plan_lemma_7_2]
THEN MP_TAC (Q.ISPEC `(\a. varset_action(a, FDOM PROB.I DIFF vs))` (Q.SPEC `vs` (Q.ISPEC `rem_condless_act(s, [], as)` ( Q.SPEC `s` (Q.SPEC `s` graph_plan_lemma_4)))))
THEN SRW_TAC[][]
THEN `EVERY (\a. varset_action (a,FDOM PROB.I DIFF vs)) (rem_condless_act (s,[],as))` by FULL_SIMP_TAC(srw_ss())[EVERY_MEM, graph_plan_lemma_7_7] 
THEN `FILTER (λa. ¬varset_action (a,FDOM PROB.I DIFF vs)) (rem_condless_act (s,[],as)) = []` by SRW_TAC[][child_parent_lemma_2_1_2_2_2]
THEN `sat_precond_as (s, FILTER (λa. ¬varset_action (a,FDOM PROB.I DIFF vs)) (rem_condless_act (s,[],as)))` by SRW_TAC[][sat_precond_as_def]
THEN FULL_SIMP_TAC(srw_ss())[exec_plan_def, EVERY_MEM]);


val child_parent_lemma_2_1_2_3 = store_thm("child_parent_lemma_2_1_2_3",
``!P1 P2 a. (\a. P1 a) a /\ (\a. P2 a) a
      	 <=> (\a. P1 a /\ P2 a) a``,
SRW_TAC[][]
);

val child_parent_lemma_2_1_2_4 = store_thm("child_parent_lemma_2_1_2_4",
``! PROB as vs . (planning_problem PROB ∧ set as SUBSET PROB.A 
     ∧ child_parent_rel(PROB, vs))
     ==>
     (FILTER (λa. varset_action (a,FDOM PROB.I DIFF vs) /\ FDOM (SND a) ≠ ∅ ) as  = 
     	     FILTER (λa. ¬varset_action (a,vs) ∧ FDOM (SND a) ≠ ∅) as)``,
Induct_on `as`
THEN1 SRW_TAC[][]
THEN REPEAT GEN_TAC
THEN STRIP_TAC 
THEN SRW_TAC[][]
THEN FULL_SIMP_TAC(srw_ss())[]
THEN METIS_TAC[child_parent_lemma_1_1_2]);



val child_parent_lemma_2_1_2 = store_thm("child_parent_lemma_2_1_2",
``!PROB vs as s.
	  (planning_problem(PROB) /\ (FDOM s = FDOM PROB.I) 
	  /\ (set as SUBSET PROB.A) /\ (FINITE vs) 
	  /\ child_parent_rel(PROB, vs) /\ EVERY  (\a. varset_action(a, FDOM(PROB.I) DIFF vs)) as )
	  ==>
	  (?as'. (exec_plan(s, as') = exec_plan(s, as))
	  /\ (LENGTH as') <= (2**CARD(FDOM(PROB.I) DIFF vs))
	  /\ EVERY  (\a. varset_action(a, FDOM(PROB.I) DIFF vs)) as'
	  /\ set as' SUBSET PROB.A)``,
SRW_TAC[][]
THEN `(∀p.
      (λas''. (exec_plan (s,as'') = exec_plan (s,as)) ∧ set as'' ⊆ PROB.A /\ EVERY (\a. varset_action(a, FDOM(PROB.I) DIFF vs)) as'')  p ∧
      (λas''. LENGTH (as'')) p > 2 ** CARD (FDOM(PROB.I) DIFF vs) (* /\
      EVERY (\a. varset_action(a, FDOM(PROB.I) DIFF vs)) p *)
       ⇒
      ∃p'.
        (λas''.
           (exec_plan (s,as'') = exec_plan (s,as)) ∧ set as'' ⊆ PROB.A /\ EVERY (\a. varset_action(a, FDOM(PROB.I) DIFF vs)) as'') p' ∧	   
	    (* EVERY (\a. varset_action(a, FDOM(PROB.I) DIFF vs)) p' /\  *)
        (λas''. LENGTH as'') p' < (λas''. LENGTH as'') p)` by
      (SRW_TAC[][]
      THEN Cases_on `LENGTH ( (rem_condless_act (s,[],p))) > 2 ** CARD (FDOM(PROB.I) DIFF vs)`
      THEN FULL_SIMP_TAC(srw_ss())[NOT_LESS, GREATER_DEF, GSYM CARD_DIFF]
      THEN `2 ** (CARD ((FDOM PROB.I) DIFF vs)) < LENGTH p` by FULL_SIMP_TAC(srw_ss())[Once (GSYM CARD_DIFF)]
      THEN ASSUME_TAC(Q.SPEC `s` (Q.SPEC `PROB.A`(Q.SPEC`p`  graph_plan_lemma_7))) 
      THEN `exec_plan(s, p) = exec_plan(s, rem_condless_act(s,[],p))` by SRW_TAC[][]  
      THENL
      [
        `EVERY (λa. varset_action (a,FDOM PROB.I DIFF vs)) (rem_effectless_act (rem_condless_act (s,[],p)))` by SRW_TAC[][graph_plan_lemma_7_7, graph_plan_lemma_16_8]
	THEN Cases_on `LENGTH(rem_effectless_act (rem_condless_act (s,[],p))) > 2 ** CARD (FDOM(PROB.I) DIFF vs)`
	THENL
	[
	      `(∃as1 as2 as3. (as1++as2++as3 = as_proj_parent((rem_effectless_act (rem_condless_act (s,[],p))), vs)) ∧ (exec_plan(DRESTRICT s (FDOM(PROB.I) DIFF vs),as1 ++ as2) = exec_plan (DRESTRICT s (FDOM(PROB.I) DIFF vs),as1)) ∧ as2 ≠ [])` by 
		   (`plan(PROB with <|G := exec_plan (s,rem_effectless_act (rem_condless_act (s,[],p))); I := s|>, rem_effectless_act (rem_condless_act (s,[],p)))` by SRW_TAC[][graph_plan_lemma_6, graph_plan_lemma_16, graph_plan_lemma_7]
		   THEN `LENGTH (as_proj_parent((rem_effectless_act (rem_condless_act (s,[],p))), vs) ) > 2 ** CARD(FDOM(PROB.I) DIFF vs)` by
		   		(`EVERY (λa. ¬varset_action (a,vs) ∧ FDOM (SND a) ≠ ∅) (rem_effectless_act (rem_condless_act (s,[],p))) ` by
				       (`EVERY (\a. varset_action(a, FDOM(PROB.I) DIFF vs)) (rem_condless_act (s,[],p))` by SRW_TAC[][graph_plan_lemma_7_7]
				       THEN `EVERY (\a. varset_action(a, FDOM(PROB.I) DIFF vs) /\ FDOM (SND a) ≠ ∅ ) (rem_effectless_act(rem_condless_act (s,[],p)))` by METIS_TAC[GSYM graph_plan_lemma_16_7, graph_plan_lemma_16_8, graph_plan_lemma_21, graph_plan_lemma_16_6]
				       THEN FULL_SIMP_TAC(srw_ss())[GSYM FILTER_EQ_ID]
				       THEN `as_proj_parent(rem_effectless_act (rem_condless_act (s,[],p)), vs) = rem_effectless_act (rem_condless_act (s,[],p))` by METIS_TAC[ (Q.ISPEC `rem_effectless_act (rem_condless_act (s,[],p))` ( Q.SPEC `vs` (Q.SPEC`PROB` (GSYM child_parent_lemma_2_1_2_1)))), graph_plan_lemma_7, graph_plan_lemma_16]
				       THEN FULL_SIMP_TAC(srw_ss())[as_proj_parent_def])
				THEN FULL_SIMP_TAC(srw_ss())[ GSYM FILTER_EQ_ID] 
       				THEN FULL_SIMP_TAC(srw_ss())[as_proj_parent_def]
				THEN METIS_TAC[GSYM CARD_DIFF, FDOM_FINITE])
		   THEN `sat_precond_as(s , (rem_effectless_act (rem_condless_act (s,[],p))))` by METIS_TAC[graph_plan_lemma_7, graph_plan_lemma_16]
   		   THEN `as_proj_parent((rem_effectless_act (rem_condless_act (s,[],p))),vs)
		   		=as_proj((rem_effectless_act (rem_condless_act (s,[],p))),FDOM(PROB.I) DIFF vs)` by METIS_TAC[GSYM child_parent_lemma_1, graph_plan_lemma_7, graph_plan_lemma_16] 
		   THEN `LENGTH (as_proj (rem_effectless_act (rem_condless_act (s,[],p)), FDOM(PROB.I) DIFF vs)) > 2 ** CARD (FDOM PROB.I DIFF vs)` by METIS_TAC[]
		   THEN `FINITE (FDOM(PROB.I) DIFF vs)`  by SRW_TAC[][]
		   THEN MP_TAC (Q.ISPEC `(rem_effectless_act (rem_condless_act (s,[],p)))` (Q.ISPEC `((FDOM PROB.I) DIFF vs)` (Q.SPEC `PROB with <|G := exec_plan (s,rem_effectless_act (rem_condless_act (s,[],p))); I := s|>` graph_plan_lemma_2)))
		   THEN SRW_TAC[][]
		   THEN FULL_SIMP_TAC(srw_ss())[prob_proj_def]
		   THEN SRW_TAC[][]
		   THEN Q.EXISTS_TAC `as1`
		   THEN Q.EXISTS_TAC `as2`
		   THEN Q.EXISTS_TAC `as3`
		   THEN SRW_TAC[][])
                THEN FULL_SIMP_TAC(srw_ss())[exec_plan_Append]
	      	THEN `?p_1 p_2 p_3. ((p_1 ++ p_2 ++ p_3 = (rem_effectless_act (rem_condless_act (s,[],p)))) /\ (as2 = as_proj(p_2, FDOM(PROB.I) DIFF vs)) /\ (as1 = as_proj(p_1, FDOM(PROB.I) DIFF vs)))` by METIS_TAC[graph_plan_lemma_8, child_parent_lemma_1, graph_plan_lemma_7, graph_plan_lemma_16]
		THEN `DRESTRICT (exec_plan (exec_plan (s,as1),as2)) (FDOM(PROB.I) DIFF vs) = DRESTRICT (exec_plan(s,as1)) (FDOM(PROB.I) DIFF vs)` by SRW_TAC[][graph_plan_lemma_9] 
		THEN `sat_precond_as(s, p_1)` by METIS_TAC[graph_plan_lemma_17, graph_plan_lemma_16, graph_plan_lemma_7] 
		THEN `DRESTRICT (exec_plan (s,as1)) (FDOM(PROB.I) DIFF vs) = DRESTRICT (exec_plan (s,p_1)) (FDOM(PROB.I) DIFF vs)` by SRW_TAC[][graph_plan_lemma_11]
		THEN `sat_precond_as(exec_plan(s, p_1), p_2)` by METIS_TAC[graph_plan_lemma_17, graph_plan_lemma_16, graph_plan_lemma_7] 
		THEN  `DRESTRICT (exec_plan (exec_plan (s,p_1),as2)) (FDOM(PROB.I) DIFF vs) = DRESTRICT (exec_plan (exec_plan (s,p_1),p_2)) (FDOM(PROB.I) DIFF vs)` by SRW_TAC[][graph_plan_lemma_11]
		THEN `set (p_1) SUBSET PROB.A` by (SRW_TAC[][] THEN FULL_SIMP_TAC(srw_ss())[] THEN METIS_TAC[LIST_TO_SET_APPEND, APPEND_ASSOC, UNION_SUBSET, graph_plan_lemma_7, graph_plan_lemma_16])
		THEN `set (p_2) SUBSET PROB.A` by (SRW_TAC[][] THEN FULL_SIMP_TAC(srw_ss())[] THEN METIS_TAC[LIST_TO_SET_APPEND, APPEND_ASSOC, UNION_SUBSET, graph_plan_lemma_7, graph_plan_lemma_16])
	      	THEN `set (p_3) SUBSET PROB.A` by (SRW_TAC[][] THEN FULL_SIMP_TAC(srw_ss())[] THEN METIS_TAC[LIST_TO_SET_APPEND, APPEND_ASSOC, UNION_SUBSET, graph_plan_lemma_7, graph_plan_lemma_16])
		THEN `EVERY (λa. varset_action (a,FDOM PROB.I DIFF vs)) (p_2 ++ p_3)` by METIS_TAC[(EVERY_APPEND),  APPEND_ASSOC]
	     	THEN `EVERY (λa. varset_action (a,FDOM PROB.I DIFF vs)) (p_2)` by FULL_SIMP_TAC(srw_ss())[( EVERY_APPEND)]	
		THEN `EVERY (λa. varset_action (a,FDOM PROB.I DIFF vs)) (p_1)` by METIS_TAC[(EVERY_APPEND),  APPEND_ASSOC]
		THEN `(DRESTRICT (exec_plan (exec_plan (s,p_1),p_2)) (FDOM(PROB.I) DIFF vs) = DRESTRICT (exec_plan (s,p_1)) (FDOM(PROB.I) DIFF vs))
	      	   /\ LENGTH ( []) < LENGTH (p_2)` by 
   		   	(`(as2 = as_proj_parent(p_2, vs)) /\ (as1 = as_proj_parent(p_1, vs))` by SRW_TAC[][child_parent_lemma_1_2, as_proj_parent_def]
			THEN `EVERY (λa. FDOM (SND a) ≠ ∅) (rem_effectless_act (rem_condless_act (s,[],p)))` by METIS_TAC[graph_plan_lemma_16_7, graph_plan_lemma_16_6]
			THEN `as2 = p_2` by
			     (`EVERY (λa. FDOM (SND a) ≠ ∅) (p_2 ++ p_3)` by METIS_TAC[(EVERY_APPEND),  APPEND_ASSOC]
			     THEN `EVERY (λa. FDOM (SND a) ≠ ∅) (p_2)` by FULL_SIMP_TAC(srw_ss())[( EVERY_APPEND)]
			     THEN `EVERY (λa. varset_action (a,FDOM PROB.I DIFF vs) /\ FDOM (SND a) ≠ ∅ ) (p_2)` by METIS_TAC[EVERY_CONJ]
     			     THEN `as2 = FILTER (λa. varset_action (a,FDOM PROB.I DIFF vs) /\ FDOM (SND a) ≠ ∅) p_2` by METIS_TAC[GSYM child_parent_lemma_2_1_2_4, as_proj_parent_def]
			     THEN METIS_TAC[EVERY_MEM, FILTER_EQ_ID])
			THEN `as1 = p_1` by
			     (`EVERY (λa. FDOM (SND a) ≠ ∅) (p_1 )` by METIS_TAC[(EVERY_APPEND),  APPEND_ASSOC]
			     THEN `EVERY (λa. varset_action (a,FDOM PROB.I DIFF vs) /\ FDOM (SND a) ≠ ∅ ) (p_1)` by METIS_TAC[EVERY_CONJ]
     			     THEN `as1 = FILTER (λa. varset_action (a,FDOM PROB.I DIFF vs) /\ FDOM (SND a) ≠ ∅) p_1` by METIS_TAC[GSYM child_parent_lemma_2_1_2_4, as_proj_parent_def]
			     THEN METIS_TAC[EVERY_MEM, FILTER_EQ_ID])
			THEN SRW_TAC[][LENGTH_NOT_NULL, NULL_EQ])
	        THEN `set (( p_1  ++ p_3)) SUBSET PROB.A` by SRW_TAC[][graph_plan_lemma_6_2, as_proj_parent_def]
		THEN `LENGTH (( p_1 ++ p_3)) < LENGTH ((p_1 ++ p_2 ++ p_3))` by FULL_SIMP_TAC(srw_ss())[] 
		THEN `(DRESTRICT (exec_plan (exec_plan (s,p_1),p_2)) (vs) = DRESTRICT (exec_plan (s,p_1)) vs)` by METIS_TAC[child_parent_lemma_2_1_2_2]
		THEN `exec_plan (exec_plan (s,p_1), p_2) = (exec_plan (s,p_1))` by METIS_TAC[graph_plan_lemma_5, graph_plan_lemma_6_1, as_proj_parent_def]
		THEN `exec_plan (s,rem_effectless_act (rem_condless_act (s,[],p))) = exec_plan (s,p_1 ++ p_3)` by  
	      	     (`exec_plan (s,p_1++ p_2++p_3) = exec_plan (s,p_1 ++ p_3)` by FULL_SIMP_TAC(srw_ss())[exec_plan_Append]
		     THEN SRW_TAC[][] THEN METIS_TAC[])
		THEN `exec_plan (s,p_1 ++ p_3) = exec_plan(s, p)` by METIS_TAC[graph_plan_lemma_7, graph_plan_lemma_16]
     		THEN `LENGTH ((p_1 ++ p_2 ++ p_3)) <= LENGTH (p)` by
		     (ASSUME_TAC(Q.SPEC `s` (Q.SPEC `PROB`(Q.SPEC`p`  graph_plan_lemma_7))) THEN ASSUME_TAC(Q.ISPEC`(rem_condless_act (s,[],p))` (Q.SPEC `PROB.A`(Q.SPEC`s` graph_plan_lemma_16))) 
		     THEN `LENGTH ((rem_condless_act (s,[],p))) ≤ LENGTH (p)` by SRW_TAC[][]
		     THEN `LENGTH ((rem_effectless_act(rem_condless_act (s,[],p)))) ≤ LENGTH (rem_condless_act (s,[],p))` by SRW_TAC[][] 
		     THEN `LENGTH (rem_effectless_act (rem_condless_act (s,[],p))) ≤ LENGTH (p)` by DECIDE_TAC
		     THEN METIS_TAC[])
		THEN `LENGTH (p_1 ++ p_3) < LENGTH (p)` by DECIDE_TAC
		THEN `EVERY (λa. varset_action (a,FDOM PROB.I DIFF vs)) (p_3)` by METIS_TAC[(EVERY_APPEND),  APPEND_ASSOC] 
		THEN METIS_TAC[EVERY_APPEND]
		,
		ASSUME_TAC(Q.ISPEC`(rem_condless_act (s,[],p))` (Q.SPEC `PROB.A`(Q.SPEC`s` graph_plan_lemma_16)))
		THEN `LENGTH (rem_effectless_act (rem_condless_act (s,[],p))) < LENGTH  (p)` by DECIDE_TAC
		THEN `(exec_plan (s,rem_condless_act (s,[],p)) = exec_plan (s,rem_effectless_act (rem_condless_act (s,[],p))))` by SRW_TAC[][]
		THEN Q.EXISTS_TAC `(rem_effectless_act (rem_condless_act (s,[],p)))`
		THEN METIS_TAC[]
	]
	,
	`EVERY (λa. varset_action (a,FDOM PROB.I DIFF vs)) (rem_condless_act (s,[],p))` by SRW_TAC[][graph_plan_lemma_7_7, graph_plan_lemma_16_8]
	THEN `LENGTH(rem_condless_act (s,[],p)) < LENGTH  (p)` by DECIDE_TAC
	THEN Q.EXISTS_TAC `(rem_condless_act (s,[],p))`
	THEN METIS_TAC[]
      ])
THEN ASSUME_TAC(Q.SPEC  `2 ** CARD ((FDOM PROB.I) DIFF vs)` 
     			(Q.SPEC `(λas''. LENGTH (as''))` 
				(Q.ISPEC `(λas''. (exec_plan (s,as'') = exec_plan (s,as)) ∧ set as'' ⊆ PROB.A /\ EVERY (λa. varset_action (a,FDOM PROB.I DIFF vs)) as'')`
					  general_theorem)))
THEN METIS_TAC[FDOM_FINITE, CARD_DIFF]);


(* 
val child_parent_lemma_2_1_3 = store_thm("child_parent_lemma_2_1_3",
``!l P1 P2 P3 k1 k2. ((! x. MEM x l ==> (P1 x /\ ~P2 x) \/ (~P1 x /\ P2 x)) /\ LENGTH (FILTER P1 l) < k1
     /\ (!l'.  (?pfx sfx. pfx ++ l' ++ sfx = l) /\ (! x. MEM x l' ==> (P2 x)) ==> LENGTH l' < k2 ))
     ==>
     LENGTH(l) < k1 * k2``
); *)


val list_frag_def = Define `list_frag(l, frag) <=> ?pfx sfx. pfx ++ frag ++ sfx = l` ;


val list_frag_rec_def = 
Define `(list_frag_rec(h::l, h'::l', h_orig :: l_original) =
         if(h = h') then
	      list_frag_rec(l, l', h_orig :: l_original)
	 else if (h = h_orig) then 
	      	 list_frag_rec(l, l_original, h_orig :: l_original)
	      else 
	      	 list_frag_rec(l, h_orig :: l_original, h_orig :: l_original)) /\

	(list_frag_rec(l, [], l') = T) /\
	(list_frag_rec([], h::l, l') = F) /\
	(list_frag_rec(l, l', []) = T)` ;

fun cheat g = ACCEPT_TAC (mk_thm g) g

val child_parent_lemma_2_1_4_1_1_1_1 = store_thm("child_parent_lemma_2_1_4_1_1_1_1",
``!l la x lb P. list_frag(la ++ [x] ++ lb, l) /\ (~ MEM x l) 
       ==>
       	  list_frag(la, l) \/ list_frag(lb, l)``,
SRW_TAC[][list_frag_def]
THEN SRW_TAC[][GSYM EXISTS_OR_THM]
THEN ASSUME_TAC(Q.SPEC `l` (Q.SPEC `x` MEM_SPLIT))
THEN FULL_SIMP_TAC(srw_ss())[]
THEN ASSUME_TAC( Q.SPEC `(l++sfx)` (GEN_ALL APPEND_EQ_APPEND_MID))
THEN FULL_SIMP_TAC(srw_ss())[]
THEN ASSUME_TAC( Q.SPEC `l` (Q.SPEC `sfx`(GEN_ALL APPEND_EQ_APPEND_MID)))
THEN FULL_SIMP_TAC(srw_ss())[]
THEN METIS_TAC[]);





val child_parent_lemma_2_1_4_1_1_1 = store_thm("child_parent_lemma_2_1_4_1_1_1",
``!l la x lb P. list_frag(la ++ [x] ++ lb, l) /\ (~ P x) /\ EVERY P l
       ==>
       	  list_frag(la, l) \/ list_frag(lb, l)``,
SRW_TAC[][]
THEN Q_TAC SUFF_TAC `!l la x lb P. list_frag(la ++ [x] ++ lb, l) /\ (~ MEM x l) 
       ==>
       	  list_frag(la, l) \/ list_frag(lb, l)`
THENL
[
	SRW_TAC[][]
	THEN FULL_SIMP_TAC(srw_ss())[EVERY_MEM]
	THEN `~MEM x l` by METIS_TAC[]
	THEN METIS_TAC[]
	,
	METIS_TAC[child_parent_lemma_2_1_4_1_1_1_1]
]);




val child_parent_lemma_2_1_4_1_1_2 = store_thm("child_parent_lemma_2_1_4_1_1_2",
``!l' l. list_frag(l, l') ==> LENGTH (l') <= LENGTH (l)``,
SRW_TAC[][list_frag_def]
THEN SRW_TAC[][]
THEN DECIDE_TAC); 


val child_parent_lemma_2_1_4_1_1 = store_thm("child_parent_lemma_2_1_4_1_1",
``!Ch k1  Par f s l PProbs PProbl. PProbs(s) /\  PProbl(l)
      	      	       /\ (!l s. PProbs(s) /\  PProbl(l) /\ EVERY Par l ==> ?l'. (f(s, l') = f(s, l)) 
      	      	       	     	       /\ (LENGTH l' <= k1) /\ (EVERY Par l') /\ PProbl(l'))
		       /\ (!a l. PProbl (l) /\ MEM a l ==> (Ch a <=> ~Par a))
		       /\ (!s l1 l2. (f(f(s, l1), l2) = f(s, l1 ++ l2)))
		       /\ (!l1 l2. PProbl(l1 ++ l2) <=> (PProbl(l1) /\ PProbl(l2)))
		       /\ (!s l. PProbs(s) /\ PProbl(l) ==> PProbs(f(s, l)))
		       ==>
			      ?l'. (f(s, l') = f(s, l)) /\ (LENGTH (FILTER Ch l') = LENGTH (FILTER Ch l)) 
			           /\ (!l''. list_frag (l', l'') /\ EVERY Par l''
				      ==>
					 LENGTH l'' <= k1) /\ PProbl(l')``,
STRIP_TAC
THEN Induct_on`FILTER Ch l`
THEN SRW_TAC[][]
THENL
[
	FULL_SIMP_TAC(srw_ss())[FILTER_EQ_NIL, list_frag_def]
	THEN FULL_SIMP_TAC(srw_ss())[EVERY_MEM]
	THEN `∀x. MEM x l ⇒ Par x` by METIS_TAC[] 
	THEN FULL_SIMP_TAC(srw_ss()) [GSYM EVERY_MEM]
	THEN FIRST_X_ASSUM (Q.SPECL_THEN [`l`, `s`] MP_TAC)
	THEN SRW_TAC[][]
	THEN Q.EXISTS_TAC `l''` 
	THEN SRW_TAC[][]
	THENL
	[
		FULL_SIMP_TAC(srw_ss())[EVERY_MEM]
		THEN `∀e. MEM e l'' ⇒ ~Ch e` by METIS_TAC[]
     		THEN  FULL_SIMP_TAC(srw_ss())[GSYM EVERY_MEM]
     		THEN FULL_SIMP_TAC(srw_ss()) [(GSYM FILTER_EQ_NIL)]
		,
		FULL_SIMP_TAC(srw_ss())[LENGTH_APPEND]
		THEN DECIDE_TAC
	]
	,
	FULL_SIMP_TAC(srw_ss())[FILTER_EQ_CONS]
	THEN FIRST_ASSUM (Q.SPECL_THEN  [`Ch`, `l2`] MP_TAC)
	THEN SRW_TAC[][]
	THEN FIRST_ASSUM (Q.SPECL_THEN  [`k1`, `Par`, `f`, `f(s, l1++[h])`] MP_TAC)
	THEN SRW_TAC[][]
	THEN `∃l'.
		(f (f (s,l1 ++ [h]),l') = f (f (s,l1 ++ [h]),l2)) ∧
        	(LENGTH (FILTER Ch l') = LENGTH (FILTER Ch l2)) ∧ PProbl(l') /\
        	∀l''.
			list_frag(l', l'') ∧ EVERY Par l'' ⇒
          		LENGTH l'' ≤ k1` by (`PProbs (f (s,l1 ++ [h])) /\ PProbl(l2)` by FULL_SIMP_TAC(srw_ss())[Once (GSYM APPEND_ASSOC)]
				    THEN FIRST_X_ASSUM  (Q.SPECL_THEN [`PProbs`, `PProbl`] MP_TAC) 
				    THEN SRW_TAC[SatisfySimps.SATISFY_ss][]
				    THEN Q.EXISTS_TAC `l'` 
				    THEN SRW_TAC[SatisfySimps.SATISFY_ss][])
				    (* THEN FULL_SIMP_TAC(srw_ss())[]METIS_TAC[]
				     THEN FIRST_ASSUM MATCH_MP_TAC
				    THEN METIS_TAC[] *)
	THEN REWRITE_TAC[GSYM APPEND_ASSOC]
	THEN REWRITE_TAC[FILTER_APPEND]
	THEN SRW_TAC[][]
	THEN `?l. (f(s, l) = f(s, l1)) /\ LENGTH(l) <= k1 /\ EVERY Par l /\ PProbl(l)` by 
	     (FULL_SIMP_TAC(srw_ss())[]
	     THEN `EVERY Par l1` by (FULL_SIMP_TAC(srw_ss())[FILTER_EQ_NIL] THEN FULL_SIMP_TAC(srw_ss())[EVERY_MEM] 
	     THEN `∀x. MEM x l1 ⇒ Par x` by METIS_TAC[]) 
	     THEN FIRST_ASSUM (Q.SPECL_THEN [`l1`, `s`]  MP_TAC)  
	     THEN STRIP_TAC
	     THEN FIRST_ASSUM MATCH_MP_TAC
	     THEN SRW_TAC[][])
	THEN Q.EXISTS_TAC `l ++ [h] ++ l'`
	THEN SRW_TAC[][]
	THENL
	[
		Q.PAT_ASSUM `∀s l1 l2. f (f (s,l1),l2) = f (s,l1 ++ l2)` (MP_TAC o GSYM) THEN STRIP_TAC
		THEN REWRITE_TAC[GSYM APPEND_ASSOC]
		THEN ASM_SIMP_TAC(bool_ss)[] 
		THEN FULL_SIMP_TAC(srw_ss())[]
		,
		FULL_SIMP_TAC(srw_ss())[EVERY_MEM]
		THEN `∀e. MEM e l ⇒ ~ Ch e` by METIS_TAC[]
		THEN FULL_SIMP_TAC(srw_ss())[GSYM EVERY_MEM]
		THEN FULL_SIMP_TAC(srw_ss())[GSYM FILTER_EQ_NIL]
		THEN REWRITE_TAC[FILTER_APPEND]
		THEN REWRITE_TAC[LENGTH_APPEND]
		THEN SRW_TAC[][]
		,	
		Q.PAT_ASSUM `∀a l. PProbl l ∧ MEM a l ⇒ (Ch a ⇔ ¬Par a)` (MP_TAC o Q.SPEC `[h]` o Q.SPEC `h`)
		THEN SRW_TAC[][] 
		THEN MP_TAC((Q.SPEC `Par`
		     (Q.SPEC `l'` 
		     	     ( Q.SPEC `h` 
			       ( Q.SPEC `l` (Q.SPEC `l''`child_parent_lemma_2_1_4_1_1_1))))))
		THEN FULL_SIMP_TAC(srw_ss())[]
		THEN SRW_TAC[][]		
		THENL
		[
			MP_TAC (Q.SPEC`l` (Q.SPEC `l''`  child_parent_lemma_2_1_4_1_1_2))
			THEN SRW_TAC[][]
			THEN DECIDE_TAC 				
			,
			SRW_TAC[][]
		]
		,
		FULL_SIMP_TAC(bool_ss)[]		
	]
]);  

val child_parent_lemma_2_1_4_1 = store_thm("child_parent_lemma_2_1_4_1",
``!k1 k2 s Par Ch  f l PProbs PProbl. PProbs(s) /\ PProbl(l) /\
      	      	       (!l: 'a list s: 'b. PProbs(s) /\ PProbl(l) /\ EVERY Par l ==> ?l'. (f(s, l') = f(s, l)) 
      	      	       	     	       /\ (LENGTH l' <= k1) /\ (EVERY Par l') /\ PProbl(l'))
		       /\ (!l s. PProbs(s) /\ PProbl(l) ==>( ?l'. (f(s, l') = f(s, l)) 
		       	      	 /\ LENGTH (FILTER Ch l') <= k2 /\ PProbl (l')))
		       /\ (∀(a :α) l:'a list. PProbl (l) /\ MEM a l 
		       	       ⇒ ((Ch :α -> bool) a ⇔ ¬(Par :α -> bool) a))
		       /\ (!s l1 l2. (f(f(s, l1), l2) = f(s, l1 ++ l2)))
		       /\ (!l1 l2. PProbl(l1 ++ l2) <=> (PProbl(l1) /\ PProbl(l2)))
		       /\ (!s l. PProbs(s) /\ PProbl(l) ==> PProbs(f(s, l)))
		       ==>
			      ?l'. (f(s, l') = f(s, l)) /\ (LENGTH (FILTER Ch l') <= k2) 
			           /\ (!l''. list_frag (l', l'') /\ EVERY Par l''
				      ==>
					 LENGTH l'' <= k1) /\ PProbl(l')``,
SRW_TAC[][]
THEN Q.PAT_ASSUM `∀l s. PProbs s ∧ PProbl l ==> (∃l'. (f (s,l') = f (s,l)) ∧ LENGTH (FILTER Ch l') ≤ k2 /\ PProbl(l'))`
	    	(MP_TAC o Q.SPEC `s` o Q.SPEC `l`)
THEN SRW_TAC[][]
THEN MP_TAC
(Q.SPEC `PProbl`
   (Q.SPEC `PProbs`
      (Q.SPEC `l'` 
         (Q.SPEC `s` 
            (Q.SPEC `f` 
	        (Q.SPEC `Par` (Q.SPEC `k1` (Q.SPEC `Ch` child_parent_lemma_2_1_4_1_1))))))))
THEN SRW_TAC[][]

THEN `∃l''.
        (f (s,l'') = f (s,l)) ∧
        (LENGTH (FILTER Ch l'') = LENGTH (FILTER Ch l')) ∧
        (∀l'''. list_frag (l'',l''') ∧ EVERY Par l''' ⇒ LENGTH l''' ≤ k1)
	/\ PProbl(l'')` by METIS_TAC[]
THEN Q.EXISTS_TAC `l''`
THEN SRW_TAC[][]);



val child_parent_lemma_2_1_3 = store_thm("child_parent_lemma_2_1_3",
``!as PROB vs s. (planning_problem PROB ∧ (FDOM s = FDOM PROB.I) ∧ PROB.A SUBSET (\a. FDOM (SND a) <> EMPTY)  /\ set as ⊆ PROB.A ∧
     FINITE vs ∧ child_parent_rel (PROB,vs)) ==>
	?as'. (exec_plan (s,as') = exec_plan (s,as)) /\ 
	      (LENGTH (FILTER (λa. varset_action (a,vs)) as') ≤ 2 ** CARD vs) /\
	      (!as''.  (list_frag(as', as'') 
		/\ (!a''. MEM a'' as'' ==> (varset_action(a'', (FDOM PROB.I DIFF vs))))
		    ==> (LENGTH as'' <= 2 ** CARD (FDOM PROB.I DIFF vs)))) /\ set as' ⊆ PROB.A``,
REPEAT STRIP_TAC
THEN MP_TAC(Q.SPEC `as`( Q.ISPEC `PROB.A` graph_plan_lemma_16_4))
THEN STRIP_TAC
THEN ASSUME_TAC(Q.SPEC `as`( Q.SPEC `s` graph_plan_lemma_16_1))
THEN MP_TAC (Q.GEN `a` (Q.SPEC ` vs` (Q.SPEC `a`  (Q.SPEC `PROB`(child_parent_lemma_1_1_2)))))
THEN FULL_SIMP_TAC(bool_ss)[]
THEN STRIP_TAC
THEN `!a l. set l SUBSET PROB.A /\ MEM a l ==> (varset_action (a,vs) ⇔ ¬varset_action (a,FDOM PROB.I DIFF vs))` by 
     (Cases_on `l` THEN SRW_TAC[][no_effectless_act_def] THEN FULL_SIMP_TAC(srw_ss())[SUBSET_DEF, SPECIFICATION])
THEN MP_TAC (REWRITE_RULE [GSYM AND_IMP_INTRO] (Q.GEN `l` (Q.GEN `s` (Q.SPEC `s` (Q.SPEC `l ` (Q.SPEC `vs` (Q.SPEC `PROB` child_parent_lemma_2_1_1)))))))
THEN FULL_SIMP_TAC(bool_ss)[]
THEN STRIP_TAC
THEN MP_TAC ((Q.GEN `l` (Q.GEN `s` (Q.SPEC `s` ( Q.SPEC `l` ( Q.SPEC `vs` (Q.SPEC `PROB` child_parent_lemma_2_1_2)))))))
THEN FULL_SIMP_TAC(bool_ss)[]
THEN STRIP_TAC
THEN MP_TAC (GSYM exec_plan_Append)
THEN STRIP_TAC
THEN MP_TAC (graph_plan_lemma_6_1 
             |> Q.SPEC `as`
	     |> Q.SPEC `s`
	     |> Q.SPEC `PROB`
	     |> Q.GEN `s`
	     |> Q.GEN `as`)
THEN FULL_SIMP_TAC(bool_ss)[]
THEN STRIP_TAC 
THEN MP_TAC (child_parent_lemma_2_1_4_1
	     |> INST_TYPE [alpha |->  ``:'a state # 'a state``]
	     |> INST_TYPE [beta |-> ``:'a state``]
	     |> Q.SPEC `2 ** CARD (FDOM (PROB) .I DIFF (vs:α -> bool))`
	     |> Q.SPEC `2 ** CARD (vs:α -> bool)`
      	     |> Q.SPEC `s`
             |> Q.ISPEC `(\a. varset_action(a, FDOM((PROB).I) DIFF (vs:α -> bool)))` 
             |> Q.SPEC `(\a. varset_action(a, (vs:α -> bool)))` 
             |> Q.SPEC `(\x. exec_plan x )` 
             |> Q.SPEC `rem_effectless_act(as)` 
             |> Q.SPEC `(\s. FDOM(s) = FDOM((PROB).I))` 
             |> Q.SPEC `(\as. set as SUBSET (PROB).A )`)
THEN FULL_SIMP_TAC(bool_ss)[]
THEN STRIP_TAC
THEN FULL_SIMP_TAC(bool_ss)[EVERY_MEM]
THEN FIRST_ASSUM MATCH_MP_TAC
THEN SRW_TAC[SatisfySimps.SATISFY_ss][]);


val child_parent_lemma_2_1 = store_thm("child_parent_lemma_2_1",
``!PROB as vs. plan(PROB, as) /\ PROB.A ⊆ (λa. FDOM (SND a) ≠ ∅) /\ child_parent_rel(PROB, vs) /\ FINITE vs
	==> ?as'. plan(PROB, as') /\ LENGTH(as') < ((2 ** CARD vs + 1) * (2 ** CARD (FDOM(PROB.I) DIFF  vs) + 1))``,
REWRITE_TAC[plan_def]
THEN REPEAT STRIP_TAC
THEN MP_TAC (child_parent_lemma_2_1_3
			|> Q.SPEC `as`
			|> Q.SPEC `PROB`
			|> Q.SPEC `vs`
			|> Q.SPEC `PROB.I`)
THEN FULL_SIMP_TAC(bool_ss)[]
THEN STRIP_TAC
THEN Q.EXISTS_TAC `as'`

THEN FULL_SIMP_TAC(bool_ss)[]
MATCH_MP_TAC REWRITE_RULE[GSYM list_frag_def, GSYM EVERY_MEM] twosorted_list_length
child_parent_lemma_2_1_3


twosorted_list_length
val _ = export_theory();




