(*
val graph_plan_lemma___1_1 = store_thm("graph_plan_lemma___1_1",
``!PROB a vs s. (dep_var_set(PROB, (FDOM PROB.I) DIFF vs, vs  )  /\ ~dep_var_set(PROB, vs, (FDOM PROB.I) DIFF vs)  /\  ¬varset_action ((DRESTRICT (FST a) vs,SND a),vs) /\ a IN PROB.A /\ vs SUBSET FDOM(PROB.I) /\ (FDOM s = FDOM PROB.I) /\ planning_problem(PROB))
==> (DRESTRICT (state_succ s (DRESTRICT (FST a) vs,SND a)) vs = DRESTRICT s vs)``,
SRW_TAC[][varset_action_def, dep_var_set_def, dep_def, SUBSET_DEF, planning_problem_def]
THEN `!x. DRESTRICT (state_succ s (DRESTRICT (FST a) vs,SND a)) vs ' x = DRESTRICT s vs ' x` by (SRW_TAC[][state_succ_def]
     THEN REWRITE_TAC[DRESTRICT_DEF]
     THEN FULL_SIMP_TAC(srw_ss())[SUBSET_DEF,FUNION_DEF,UNION_DEF, EXTENSION, DRESTRICT_DEF, DISJOINT_DEF, INTER_DEF]
     THEN SRW_TAC[][]
     THEN METIS_TAC[SPECIFICATION])

THEN `FDOM(DRESTRICT (state_succ s (DRESTRICT (FST a) vs,SND a)) vs) = FDOM(DRESTRICT s vs)` by 
     (`FDOM (SND (DRESTRICT (FST a) vs,SND a)) SUBSET FDOM s` by SRW_TAC[][]
     THEN METIS_TAC[FDOM_state_succ, SUBSET_DEF, FDOM_DRESTRICT])
THEN METIS_TAC[fmap_EQ_THM]
);







val graph_plan_lemma___1 = store_thm("graph_plan_lemma___1",
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
		THEN METIS_TAC[graph_plan_lemma_9_1_4]
		,
		`(state_succ (DRESTRICT s vs) (DRESTRICT (FST h) vs,SND h)) = (DRESTRICT (state_succ s (DRESTRICT (FST h) vs,SND h)) vs)` by 
		     (FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_1_3, graph_plan_lemma_1_4, planning_problem_def, varset_action_def]
		     THEN `FST (DRESTRICT (FST h) vs,SND h) SUBMAP s` by METIS_TAC[graph_plan_lemma_12_4, graph_plan_lemma_1_4]
		     THEN `varset_action((DRESTRICT (FST h) vs,SND h), vs)` by SRW_TAC[][varset_action_def]
		     THEN `FDOM( SND (DRESTRICT (FST h) vs,SND h)) SUBSET FDOM s` by SRW_TAC[][]
		     THEN `(\a. (DRESTRICT (FST a) vs,SND a)) (DRESTRICT (FST h) vs,SND h) = (DRESTRICT (FST h) vs,SND h) ` by SRW_TAC[][] 
		     THEN METIS_TAC[graph_plan_lemma_9_1_6])
       		THEN `FDOM (state_succ s (DRESTRICT (FST h) vs,SND h)) = FDOM PROB.I` by (SRW_TAC[][FDOM_state_succ, planning_problem_def]
     	  	     THEN `FDOM (SND(DRESTRICT (FST h) vs,SND h)) SUBSET FDOM PROB.I` by FULL_SIMP_TAC(srw_ss())[planning_problem_def]  
	  	     THEN METIS_TAC[FDOM_state_succ])
       		THEN `(∀as'. (as' ≠ [] ∧ as' ≼ (FILTER (λa. varset_action (a,vs))(MAP (λa. (DRESTRICT (FST a) vs,SND a)) as))) ⇒ (FST (LAST as') ⊑ LAST (state_list ((state_succ s (DRESTRICT (FST h) vs,SND h)),as'))))` by METIS_TAC[graph_plan_lemma_1_1_1]		     
		THEN METIS_TAC[]	  
	]
	,
	METIS_TAC[FDOM_state_succ, planning_problem_def]
]);



val graph_plan_lemma___2 = store_thm("graph_plan_lemma___2",
``! vs as. FILTER (λa. varset_action (a,vs))(MAP (λa. (DRESTRICT (FST a) vs,SND a)) as) =  FILTER (λa. varset_action (a,vs))(MAP (λa. (DRESTRICT (FST a) vs,SND a)) (FILTER (λa. varset_action (a,vs))(MAP (λa. (DRESTRICT (FST a) vs,SND a)) as)))``,
Induct_on`as`
THEN SRW_TAC[][]
);

val graph_plan_lemma__ = store_thm("graph_plan_lemma__",
``∀PROB s as vs.
     (planning_problem PROB ∧ set as ⊆ PROB.A ∧ (FDOM s = FDOM PROB.I) /\
     vs ⊆ FDOM PROB.I ∧ dep_var_set (PROB,FDOM PROB.I DIFF vs,vs) ∧
     ¬dep_var_set (PROB,vs,FDOM PROB.I DIFF vs)
        /\ (∀as'. (as' ≠ [] ∧ as' ≼ (FILTER (λa. varset_action (a,vs)) (MAP (λa. (DRESTRICT (FST a) vs,SND a)) as))) ⇒ (FST (LAST as') ⊑ LAST (state_list (s,as'))))) ⇒ 
        (DRESTRICT (exec_plan( s, (FILTER (λa. varset_action (a,vs))(MAP (λa. (DRESTRICT (FST a) vs,SND a)) as)))) vs = exec_plan(DRESTRICT s vs, (FILTER (λa. varset_action (a,vs))(MAP (λa. (DRESTRICT (FST a) vs,SND a)) as))))``,
SRW_TAC[][]
THEN METIS_TAC[graph_plan_lemma___1, graph_plan_lemma_9_2])


 
val graph_plan_lemma_1_1_1 = store_thm("graph_plan_lemma_1_1_1",
``∀ s h as a' as'. (as <> []) /\ sat_precond_as(s,h::as)   ==> sat_precond_as(state_succ s h,as)``,
SRW_TAC[][sat_precond_as_def]
THEN `h::as' ≼ h::as` by METIS_TAC[isPREFIX_THM]
THEN `FST (LAST (h::as')) ⊑ LAST (state_list (s,h::as'))` by SRW_TAC[][]
THEN `FST (LAST (h::as')) = FST (LAST (as'))` by( Cases_on`as'` 
     THEN SRW_TAC[][isPREFIX_THM])
THEN `(state_list (s,h::as')) = s::(state_list (state_succ s h,as'))` by SRW_TAC[][state_list_def]
THEN `LAST (state_list (s,h::as')) = LAST (s::state_list (state_succ s h,as'))` by METIS_TAC[]
THEN `LAST (s::state_list (state_succ s h,as')) = LAST (state_list (state_succ s h,as'))` by (Cases_on`as'` 
      THEN SRW_TAC[][isPREFIX_THM, state_list_def])
THEN METIS_TAC[]
);




val graph_plan_lemma_2_3_2_8_1 = store_thm("graph_plan_lemma_2_3_2_8_1",
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
     THEN METIS_TAC[SPECIFICATION])
THEN METIS_TAC[fmap_EQ_THM]
);

val graph_plan_lemma_1_3_2 = store_thm("graph_plan_lemma_1_3_2",
``!fm1 fm2 vs.  (fm2 SUBMAP fm1) 
       ==> ((DRESTRICT fm2 vs) SUBMAP (DRESTRICT fm1 vs) )``,
SRW_TAC[][SUBSET_DEF, SUBMAP_DEF]
THEN FULL_SIMP_TAC(srw_ss())[SUBSET_DEF, SUBMAP_DEF, FDOM_DRESTRICT, DRESTRICT_DEF]
);


val graph_plan_lemma_1_3 = store_thm ("graph_plan_lemma_1_3",
``!s a vs. ( (FST a) SUBMAP s /\ vs SUBSET FDOM s /\ (FDOM (SND a) SUBSET FDOM s) /\ varset_action(a,vs)) ==> 
     (state_succ (DRESTRICT s vs) (DRESTRICT (FST a) vs,SND a) =
     		   DRESTRICT (state_succ s a) vs)``,
  SRW_TAC[][state_succ_def]
  THEN METIS_TAC[graph_plan_lemma_2_3_2_8_1, graph_plan_lemma_1_3_2]
);


val graph_plan_lemma_1_5 = store_thm("graph_plan_lemma_1_5",
``!PROB a vs s. (dep_var_set(PROB, (FDOM PROB.I) DIFF vs, vs  )  /\ ~dep_var_set(PROB, vs, (FDOM PROB.I) DIFF vs)  /\  ¬varset_action (a,vs) /\ a IN PROB.A /\ vs SUBSET FDOM(PROB.I) /\ (FDOM s = FDOM PROB.I) /\ planning_problem(PROB))
==> (DRESTRICT (state_succ s a) vs = DRESTRICT s vs)``,
SRW_TAC[][varset_action_def, dep_var_set_def, dep_def, SUBSET_DEF, planning_problem_def]

THEN `FDOM(DRESTRICT (state_succ s a) vs) = FDOM(DRESTRICT s vs)` by METIS_TAC[FDOM_state_succ, SUBSET_DEF, FDOM_DRESTRICT]
THEN `!x. DRESTRICT (state_succ s a) vs ' x = DRESTRICT s vs ' x` by (SRW_TAC[][state_succ_def]
     THEN REWRITE_TAC[DRESTRICT_DEF]
     THEN FULL_SIMP_TAC(srw_ss())[SUBSET_DEF,FUNION_DEF,UNION_DEF, EXTENSION, DRESTRICT_DEF, DISJOINT_DEF, INTER_DEF]
     THEN SRW_TAC[][]
     THEN METIS_TAC[SPECIFICATION])
THEN METIS_TAC[fmap_EQ_THM]
);




val graph_plan_lemma_2_3_2_1 = store_thm("graph_plan_lemma_2_3_2_1",
`` !PROB vs a.  vs ⊆ FDOM PROB.I ∧ varset_action ((DRESTRICT (FST a) vs,SND a),vs) ∧
  (a IN PROB.A) ⇒ ((DRESTRICT (FST a) vs,SND a) IN ( (prob_proj(PROB, vs)) .A))``,
SRW_TAC[][prob_proj_def,state_succ_def, varset_action_def, planning_problem_def, SUBSET_DEF,DRESTRICT_DEF,EXTENSION]
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



val graph_plan_lemma_2_3_2_2 = store_thm("graph_plan_lemma_2_3_2_2",
``!PROB as. plan(PROB, as) ==> (FDOM PROB.I = FDOM PROB.G)``,
Induct_on`as`
THEN1 SRW_TAC[][plan_def, exec_plan_def]
THEN SRW_TAC[][]
THEN `plan (PROB with I:=state_succ PROB.I h ,as)` by METIS_TAC[lemma_1_1]
THEN `FDOM (PROB with I := state_succ PROB.I h).I = FDOM (PROB with I := state_succ PROB.I h).G`  by METIS_TAC[]
THEN `FDOM (PROB with I := state_succ PROB.I h).G = FDOM(PROB.G)` by SRW_TAC[][state_succ_def]
THEN METIS_TAC[FDOM_state_succ, plan_def, planning_problem_def, exec_plan_def]
);


val graph_plan_lemma_2_3_2_8 = store_thm("graph_plan_lemma_2_3_2_8",
``! as PROB vs a. FST a ⊑ PROB.I /\ varset_action(a, vs) /\ vs SUBSET FDOM(PROB.I)
==>( exec_plan ((prob_proj (PROB,vs)).I,(DRESTRICT (FST a) vs,SND a)::as) =   exec_plan((prob_proj (PROB with I := state_succ PROB.I a,vs)).I,as))``,
Induct_on`as`
THEN SRW_TAC[][exec_plan_def, state_succ_def, prob_proj_def] 
THEN METIS_TAC[graph_plan_lemma_2_3_2_8_1,graph_plan_lemma_1_1_1] 
);


val graph_plan_lemma_2_3_2 = store_thm("graph_plan_lemma_2_3_2",
``!PROB as a vs. ((FST a) SUBMAP PROB.I) /\ planning_problem(PROB) /\ (vs SUBSET FDOM(PROB.I)) /\ (a IN PROB.A) /\ varset_action (a,vs) /\ plan(prob_proj(PROB with I:= state_succ PROB.I a, vs), as)
==> plan(prob_proj (PROB,vs),(DRESTRICT (FST a) vs,(SND a))::as)``,
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
			THEN METIS_TAC[graph_plan_lemma_2_3_2_3]
			,
			METIS_TAC[graph_plan_lemma_2_3_2_6]			
		]
		,
		FULL_SIMP_TAC(srw_ss())[exec_plan_def,state_succ_def]
		THEN SRW_TAC[][]
		THENL
		[
			FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_2_3_2_8_1, prob_proj_def]
			THEN METIS_TAC[graph_plan_lemma_2_3_2_8_1]
			,
			FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_2_3_2_8_1, prob_proj_def, planning_problem_def]
			THEN METIS_TAC[graph_plan_lemma_1_1_1]
		]
		,
		FULL_SIMP_TAC(srw_ss())[prob_proj_def, varset_action_def]
		THEN METIS_TAC[graph_plan_lemma_2_3_2_7]
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
			THEN METIS_TAC[graph_plan_lemma_2_3_2_3]
			,
			METIS_TAC[graph_plan_lemma_2_3_2_6]			
		]
		,
		METIS_TAC[graph_plan_lemma_2_3_2_8, graph_plan_lemma_2_3_2_9]
		,
		FULL_SIMP_TAC(srw_ss())[prob_proj_def, varset_action_def]
		THEN METIS_TAC[graph_plan_lemma_2_3_2_7]
		,
		FULL_SIMP_TAC(srw_ss())[prob_proj_def, varset_action_def]
		THEN METIS_TAC[graph_plan_lemma_2_3_2_7]
		,
		FULL_SIMP_TAC(srw_ss())[prob_proj_def, varset_action_def]
	]	
]);




val graph_plan_lemma_2_3_3 = store_thm("graph_plan_lemma_2_3_3",
``!PROB vs1 vs2 a. (a IN PROB.A) /\ (vs1 SUBSET FDOM(PROB.I)) /\ (vs2 SUBSET FDOM(PROB.I)) ==>  (dep_var_set(PROB with I:= state_succ PROB.I a,vs1,vs2) <=> dep_var_set(PROB, vs1, vs2))``,
SRW_TAC[][dep_var_set_def, dep_def]
);






val graph_plan_lemma_2_3_6 = store_thm("graph_plan_lemma_2_3_6",
``! x y vs.  varset_action((x ,DRESTRICT y vs),vs)``,
SRW_TAC[][varset_action_def, FDOM_DRESTRICT]
);




val graph_plan_lemma_9_1_2 = store_thm("graph_plan_lemma_9_1_2",
``!x s vs. (x ⊑ s) ==> ((DRESTRICT x vs) SUBMAP s)``,
SRW_TAC[][DRESTRICT_DEF, SUBMAP_DEF]
THEN `FDOM (DRESTRICT s vs) = FDOM  (DRESTRICT s' vs)` by FULL_SIMP_TAC(srw_ss())[]
);


val graph_plan_lemma_9_1_3 = store_thm("graph_plan_lemma_9_1_3",
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



val graph_plan_lemma_9_1_1 = store_thm("graph_plan_lemma_9_1_1",
``∀s s' a vs.
     (FST a ⊑ s /\ varset_action (a,vs) /\ (DRESTRICT s vs = DRESTRICT s' vs) )⇒
     (DRESTRICT (state_succ s' (DRESTRICT (FST a) vs,SND a)) vs =
      DRESTRICT (state_succ s a) vs)``,
  SRW_TAC[][state_succ_def]
  THEN `FDOM (DRESTRICT s vs) = FDOM  (DRESTRICT s' vs)` by FULL_SIMP_TAC(srw_ss())[]
  THEN `FDOM (DRESTRICT (SND a ⊌ s') vs) = FDOM (DRESTRICT (SND a ⊌ s) vs)` by (FULL_SIMP_TAC(srw_ss())[FDOM_DRESTRICT, DRESTRICT_DEF, UNION_DEF, INTER_DEF, EXTENSION, varset_action_def, SUBSET_DEF]
       THEN  METIS_TAC[])
  THEN `!x. (DRESTRICT s vs) ' x =  (DRESTRICT s' vs) ' x` by FULL_SIMP_TAC(srw_ss())[]
  THEN `!x. (DRESTRICT (SND a ⊌ s') vs) ' x = (DRESTRICT (SND a ⊌ s) vs) ' x` by (FULL_SIMP_TAC(srw_ss())[FDOM_DRESTRICT, DRESTRICT_DEF, UNION_DEF, INTER_DEF, EXTENSION, varset_action_def, SUBSET_DEF, FUNION_DEF]
       THEN METIS_TAC[])
  THEN1 METIS_TAC[fmap_EQ_THM]
  THEN  METIS_TAC[graph_plan_lemma_9_1_3]);





val graph_plan_lemma_9_1_4 = store_thm("graph_plan_lemma_9_1_4",
``∀vs h.
    (varset_action(h, vs)) ⇒
     (DRESTRICT (state_succ (DRESTRICT s vs) h) vs =
     		state_succ (DRESTRICT s vs) h)``,
SRW_TAC[][state_succ_def]
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


val graph_plan_lemma_2_3_2_8_1 = store_thm("graph_plan_lemma_2_3_2_8_1",
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



val graph_plan_lemma_9_1_6 = store_thm ("graph_plan_lemma_9_1_6",
``!s a vs. ( vs SUBSET FDOM s /\ (FDOM (SND a) SUBSET FDOM s) /\ varset_action(a,vs)) ==> 
     (state_succ (DRESTRICT s vs) (DRESTRICT (FST a) vs,SND a) =
     		   DRESTRICT (state_succ s (DRESTRICT (FST a) vs,SND a)) vs)``,
  SRW_TAC[][state_succ_def]
  THEN METIS_TAC[graph_plan_lemma_2_3_2_8_1, graph_plan_lemma_1_1_1, graph_plan_lemma_9_1_2, graph_plan_lemma_9_1_6_1]
);


val graph_plan_lemma_9_1_7 = store_thm ("graph_plan_lemma_9_1_7",
``!s a vs. ( (FST a) SUBMAP s ) ==> 
     (state_succ (s ) (DRESTRICT (FST a) vs,SND a) =
     		   (state_succ s (a)) )``,
  SRW_TAC[][state_succ_def]
  THEN METIS_TAC[graph_plan_lemma_2_3_2_8_1, graph_plan_lemma_1_1_1, graph_plan_lemma_9_1_2]
);






val child_parent_lemma_2_1_1_2_1_2 = store_thm("child_parent_lemma_2_1_1_2_1_2",
``!(x :α state # α state) (vs) (s) (s'). (DRESTRICT s vs = DRESTRICT s' vs)
     	      /\ ((FDOM (FST x)) SUBSET vs)
	      ==> (((FST x) SUBMAP s) = ((FST x) SUBMAP s'))``,
SRW_TAC[][SUBMAP_DEF, SUBSET_DEF]
THEN EQ_TAC
THEN SRW_TAC[][]
THEN `FDOM(DRESTRICT s vs) = FDOM(DRESTRICT s' vs)` by FULL_SIMP_TAC(srw_ss())[fmap_EQ_THM]
THEN FULL_SIMP_TAC(srw_ss())[FDOM_DRESTRICT, INTER_DEF, EXTENSION]
THEN FULL_SIMP_TAC(srw_ss())[fmap_EXT, DRESTRICT_DEF, FDOM_DRESTRICT, INTER_DEF] 
THEN METIS_TAC[]);


val child_parent_lemma_2_1_1_2_1_1 = store_thm("child_parent_lemma_2_1_1_2_1_1",
``∀s s' a vs.
     ((FST a ⊑ s = FST a ⊑ s' ) /\ varset_action (a,vs) /\ (DRESTRICT s vs = DRESTRICT s' vs) )⇒
     (DRESTRICT (state_succ s' a) vs =
      DRESTRICT (state_succ s a) vs)``,
  SRW_TAC[][state_succ_def]
  THEN `FDOM (DRESTRICT s vs) = FDOM  (DRESTRICT s' vs)` by FULL_SIMP_TAC(srw_ss())[]
  THEN `FDOM (DRESTRICT (SND a ⊌ s') vs) = FDOM (DRESTRICT (SND a ⊌ s) vs)` by (FULL_SIMP_TAC(srw_ss())[FDOM_DRESTRICT, DRESTRICT_DEF, UNION_DEF, INTER_DEF, EXTENSION, varset_action_def, SUBSET_DEF]
       THEN  METIS_TAC[])
  THEN `!x. (DRESTRICT s vs) ' x =  (DRESTRICT s' vs) ' x` by FULL_SIMP_TAC(srw_ss())[]
  THEN `!x. (DRESTRICT (SND a ⊌ s') vs) ' x = (DRESTRICT (SND a ⊌ s) vs) ' x` by (FULL_SIMP_TAC(srw_ss())[FDOM_DRESTRICT, DRESTRICT_DEF, UNION_DEF, INTER_DEF, EXTENSION, varset_action_def, SUBSET_DEF, FUNION_DEF]
       THEN METIS_TAC[])
  THEN1 METIS_TAC[fmap_EQ_THM]);




val child_parent_lemma_2_1_1_2_1 = store_thm("child_parent_lemma_2_1_1_2_1",
``!as vs s s'. ((!a. MEM a as ==> ((FDOM (FST a)) SUBSET (vs)) /\ varset_action(a,vs)) /\ 
	      (DRESTRICT s vs = DRESTRICT s' vs) )
	    ==>
	    (sat_precond_as (s',as) = sat_precond_as (s ,as))``,
Induct_on `as`
THEN SRW_TAC[][sat_precond_as_def]
THEN `FDOM (FST h) ⊆ vs` by FULL_SIMP_TAC(srw_ss())[]
THEN `varset_action(h, vs)` by FULL_SIMP_TAC(srw_ss())[]
THEN EQ_TAC
THEN SRW_TAC[][]
THEN METIS_TAC[child_parent_lemma_2_1_1_2_1_1, child_parent_lemma_2_1_1_2_1_2]);



val child_parent_lemma_2_1_1_2_2_1 = store_thm("child_parent_lemma_2_1_1_2_2_1",
``! PROB vs a. child_parent_rel (PROB,vs) ∧ a IN PROB.A /\ varset_action(a, FDOM(PROB.I) DIFF vs)
    	       ==> ((FDOM (FST(a)) SUBSET ((FDOM(PROB.I)) DIFF vs)) <=> (FDOM (FST(a)) SUBSET FDOM(PROB.I)))``,
SRW_TAC[][planning_problem_def, child_parent_rel_def, dep_var_set_def, dep_def, SUBSET_DEF, varset_action_def, DISJOINT_DEF, INTER_DEF, EXTENSION]
FULL_SIMP_TAC(srw_ss())[child_parent_rel_def, dep_var_set_def, dep_def]
THEN EQ_TAC
THEN SRW_TAC[][]
THEN Q_TAC SUFF_TAC `!PROB vs1 vs2. ~dep_var_set(PROB, vs1, vs2) ==> 
     	   	    	       ~(?a v1 v2. (a IN PROB.A) /\ ( )`)
THEN METIS_TAC[]
);

val child_parent_lemma_2_1_1_2_2 = store_thm("child_parent_lemma_2_1_1_2_2",
``!PROB as vs. (child_parent_rel (PROB,vs) /\ set as ⊆ PROB.A /\ no_effectless_act(as))
	    ==>
	    (!a. MEM a (FILTER (λa. ¬varset_action (a,vs)) as) ==> ((FDOM (FST a)) SUBSET (FDOM(PROB.I) DIFF vs)) 
	    	 /\ varset_action(a,(FDOM(PROB.I) DIFF vs)))``,
Induct_on `as`
THEN SRW_TAC[][]   no_effectless_act_def]    sat_precond_as_def]
THEN 


THEN `FDOM (FST h) ⊆ vs` by FULL_SIMP_TAC(srw_ss())[]
THEN `varset_action(h, vs)` by FULL_SIMP_TAC(srw_ss())[]
THEN EQ_TAC
THEN SRW_TAC[][]
THEN METIS_TAC[child_parent_lemma_2_1_1_2_1_1, child_parent_lemma_2_1_1_2_1_2]);





val child_parent_lemma_2_1_1_1_2 = store_thm("child_parent_lemma_2_1_1_1_2",
``!P l. (?x. MEM x l /\ P x) 
==> LENGTH(FILTER (\x. ~ (P x)) l) < LENGTH(l)``,
Induct_on`l`
THEN SRW_TAC[][]
THEN ASSUME_TAC (Q.SPEC `l` (Q.SPEC `(λx. ¬P x)` rich_listTheory.LENGTH_FILTER_LEQ))
THEN METIS_TAC[LESS_EQ_IMP_LESS_SUC]);

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
THEN `LENGTH (FILTER (λa. ~P a) (FILTER (λa. P a) l)) < SUC (LENGTH (FILTER (λa. P a) l))` by
     (`LENGTH (FILTER (λa. ¬P a) (FILTER (λa. P a) l)) <= LENGTH (FILTER (λa. P a) l)` by METIS_TAC[rich_listTheory.LENGTH_FILTER_LEQ]
      THEN `!x y. x <= y ==> x < SUC y` by DECIDE_TAC 
      THEN METIS_TAC[])
THEN `!x y. x< y ==> x <  SUC y` by DECIDE_TAC
THEN METIS_TAC[FILTER_COMM]);



val child_parent_lemma_2_1_1_1_1_1_3 = store_thm("child_parent_lemma_2_1_1_1_1_1_3",
``!PROB a vs as. ((as <> []) /\  planning_problem(PROB) /\ (vs SUBSET FDOM(PROB.I)) /\ (a IN PROB.A) /\ (MEM a (FILTER (\a. ~varset_action (a,vs)) as)))
    ==> ~(DISJOINT (FDOM (SND a)) (FDOM(PROB.I) DIFF vs))``,
Induct_on`as`
THEN FULL_SIMP_TAC(srw_ss())[DISJOINT_DEF, INTER_DEF, varset_action_def, EXTENSION,FILTER, planning_problem_def, MEM, SUBSET_DEF]
THEN SRW_TAC[][]
THEN1 METIS_TAC[]
THEN Cases_on`as = []`
THEN SRW_TAC[][]
THEN FULL_SIMP_TAC(srw_ss())[MEM]
THEN METIS_TAC[planning_problem_def]);

val child_parent_lemma_2_1_1_1_1_1 = store_thm("child_parent_lemma_2_1_1_1_1_1",
``!PROB s vs a. (planning_problem(PROB) /\ (FDOM s = FDOM PROB.I) /\ (vs SUBSET FDOM PROB.I) /\ child_parent_rel(PROB, vs) /\  ¬varset_action (a,vs) /\ (a IN PROB.A))
==> (DRESTRICT (state_succ s a) vs = (DRESTRICT s vs))``,
METIS_TAC[child_parent_lemma_1_1_4, graph_plan_lemma_1_2, child_parent_lemma_1_1_5]
);


val child_parent_lemma_2_1_1_1_1_2 = store_thm("child_parent_lemma_2_1_1_1_1_2",
``! PROB x y as vs. (planning_problem(PROB) /\ (set as SUBSET PROB.A)  /\ (FDOM x =  FDOM (PROB.I)) /\ (FDOM y = FDOM (PROB.I)) /\ (vs SUBSET FDOM(PROB.I)) /\ child_parent_rel(PROB, vs) /\ (DRESTRICT (x) vs = DRESTRICT y vs)) ==>
(DRESTRICT (exec_plan (x,FILTER (λa. ¬varset_action (a,vs)) as)) vs = DRESTRICT (exec_plan (y ,FILTER (λa. ¬varset_action (a,vs)) as)) vs) ``,
Induct_on`as`
THEN  SRW_TAC [] [exec_plan_def]
THEN `FDOM (state_succ x h) = FDOM (PROB.I)` by METIS_TAC[planning_problem_def, FDOM_state_succ]
THEN `FDOM (state_succ y h) = FDOM (PROB.I)` by METIS_TAC[planning_problem_def, FDOM_state_succ]
THEN METIS_TAC[child_parent_lemma_2_1_1_1_1_1]
);


val child_parent_lemma_2_1_1_1_1_3 = store_thm("child_parent_lemma_2_1_1_1_1_3",
``! PROB s as vs. (planning_problem(PROB) /\ (set as SUBSET PROB.A)  /\ (FDOM s =  FDOM (PROB.I)) /\ (vs SUBSET FDOM(PROB.I)) /\ child_parent_rel(PROB, vs)) 
	==>
	((DRESTRICT s vs) = (DRESTRICT (exec_plan (s,FILTER (λa. ¬varset_action (a,vs)) as)) vs))``,
Induct_on`as`
THEN  SRW_TAC [] [exec_plan_def]
THEN METIS_TAC[child_parent_lemma_1_1_5, graph_plan_lemma_1_2, child_parent_lemma_1_1_4, child_parent_lemma_2_1_1_1_1_2, planning_problem_def, FDOM_state_succ] 
);


val child_parent_lemma_2_1_1_1_1 = store_thm("child_parent_lemma_2_1_1_1_1",
``!PROB s as vs. (planning_problem(PROB) /\ (FDOM s = FDOM PROB.I) /\ (set as SUBSET PROB.A) /\ (vs SUBSET FDOM PROB.I) /\ child_parent_rel(PROB, vs)
	    /\ ((DRESTRICT s vs) = (DRESTRICT (exec_plan(s,as)) vs))) 
     	    ==>
            ((DRESTRICT (exec_plan(s,as)) vs) = (DRESTRICT (exec_plan (s,FILTER (\a. ~varset_action (a,vs)) as)) vs))``,
METIS_TAC[child_parent_lemma_2_1_1_1_1_3]);












*)
open HolKernel Parse boolLib bossLib;

val _ = new_theory "GraphPlanTheorem";
open HolKernel Parse boolLib bossLib;
open finite_mapTheory
open arithmeticTheory
open pred_setTheory
open FM_planTheory
open rich_listTheory
open listTheory;							 


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
``!PROB vs. (vs SUBSET FDOM(PROB.I) )
==>
(CARD( FDOM((prob_proj(PROB, vs)).I)) = CARD(vs))``,

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
  /\ sat_precond_as(PROB.I, as)
 /\ vs SUBSET FDOM(PROB.I))
==> plan(prob_proj(PROB,vs), as_proj(as, vs))``,
Induct_on`as`
THEN1 SRW_TAC[][graph_plan_lemma_2_3_1, as_proj_def] 
THEN SRW_TAC[][]
THEN `plan (PROB with I:=state_succ PROB.I h,as)` by METIS_TAC[lemma_1_1]
THEN `h IN PROB.A` by FULL_SIMP_TAC(srw_ss())[plan_def]
THEN `(FDOM PROB.I DIFF vs) SUBSET FDOM(PROB.I)` by SRW_TAC[][]
THEN `vs SUBSET FDOM((PROB with I:= state_succ PROB.I h).I)` by FULL_SIMP_TAC(srw_ss())[FDOM_state_succ, plan_def, planning_problem_def]
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
	  /\ (vs SUBSET FDOM PROB.I)
	  /\ LENGTH(as_proj(as, vs)) > (2**(CARD(vs)))  
	  /\ sat_precond_as(PROB.I, as))
	  ==>
	  (∃as1 as2 as3. (as1 ++ as2 ++ as3 = as_proj(as, vs)) ∧
       	  ((exec_plan((prob_proj(PROB, vs)).I,as1 ++ as2) = exec_plan ((prob_proj(PROB, vs)).I,as1)) ∧ (as2 ≠ [])))``,
SRW_TAC[][]
THEN `CARD (FDOM (prob_proj(PROB, vs)).I) = CARD(vs)` by METIS_TAC[graph_plan_lemma_2_1]
THEN `plan(prob_proj (PROB,vs), as_proj(as, vs))` by FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_2_3]
THEN `planning_problem(prob_proj(PROB,vs))` by METIS_TAC[graph_plan_lemma_2_2, plan_def] 
THEN `LENGTH (as_proj(as, vs)) > 2 ** CARD (FDOM (prob_proj (PROB,vs)).I) ` by SRW_TAC[][]
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
``! as s PROB. ((set as) SUBSET (PROB.A) /\ planning_problem(PROB) /\ (FDOM s = FDOM PROB.I)) ==> (FDOM(exec_plan(s, as)) = FDOM PROB.I)``,
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


val child_parent_lemma_1_1_1 = store_thm("child_parent_lemma_1_1_1",
``! a vs. varset_action (a,vs) ==>  (DRESTRICT (SND a) vs = SND a )``,
SRW_TAC[][varset_action_def]
THEN SRW_TAC[][graph_plan_lemma_2_3_8_5]);

val child_parent_lemma_1_1_2 = store_thm("child_parent_lemma_1_2_1",
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
	  (planning_problem(PROB)   /\ (FDOM s = FDOM PROB.I) 
	  /\ (set as SUBSET PROB.A) /\ (vs SUBSET FDOM PROB.I) 
	  /\ child_parent_rel(PROB, vs))
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
      THEN Cases_on `LENGTH (FILTER (λa. varset_action (a,vs)) ( (rem_condless_act (s,[],p)))) > 2 ** CARD (vs)`
      THENL
      [
	Cases_on `LENGTH (FILTER (λa. varset_action (a,vs)) ( (rem_effectless_act (rem_condless_act (s,[],p))))) > 2 ** CARD (vs)`
	THENL
	[
		
	      `(∃as1 as2 as3. (as1++as2++as3 = as_proj_child((rem_effectless_act (rem_condless_act (s,[],p))),vs)) ∧ (exec_plan(DRESTRICT s vs,as1 ++ as2) = exec_plan (DRESTRICT s vs,as1)) ∧ as2 ≠ [])` by
		   (`LENGTH (as_proj_child((rem_effectless_act (rem_condless_act (s,[],p))), vs) ) > 2 ** CARD(vs)` by FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_3, graph_plan_lemma_16_6]
		   THEN `plan(PROB with <|G := exec_plan (s,rem_effectless_act (rem_condless_act (s,[],p))); I := s|>, rem_effectless_act (rem_condless_act (s,[],p)))` by SRW_TAC[][graph_plan_lemma_6, graph_plan_lemma_16, graph_plan_lemma_7]
	      	   THEN `vs SUBSET FDOM ((PROB with <|G := exec_plan (s,(rem_effectless_act (rem_condless_act (s,[],p)))); I := s|>).I)` by SRW_TAC[][]		   
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

(*
val child_parent_lemma_2_1_2 = store_thm("child_parent_lemma_2_1_2",
``!PROB vs as s.
	  (planning_problem(PROB)   /\ (FDOM s = FDOM PROB.I) 	   
	  /\ (set as SUBSET PROB.A) /\ (vs SUBSET FDOM PROB.I) 
	  /\ child_parent_rel(PROB, vs))
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
      THEN Cases_on `LENGTH (FILTER (λa. varset_action (a,vs)) ( (rem_condless_act (s,[],p)))) > 2 ** CARD (vs)`
      THENL
      [
	Cases_on `LENGTH (FILTER (λa. varset_action (a,vs)) ( (rem_effectless_act (rem_condless_act (s,[],p))))) > 2 ** CARD (vs)`
	THENL
	[
		
	      `(∃as1 as2 as3. (as1++as2++as3 = as_proj_child((rem_effectless_act (rem_condless_act (s,[],p))),vs)) ∧ (exec_plan(DRESTRICT s vs,as1 ++ as2) = exec_plan (DRESTRICT s vs,as1)) ∧ as2 ≠ [])` by
		   (`LENGTH (as_proj_child((rem_effectless_act (rem_condless_act (s,[],p))), vs) ) > 2 ** CARD(vs)` by FULL_SIMP_TAC(srw_ss())[graph_plan_lemma_3, graph_plan_lemma_16_6]
		   THEN `plan(PROB with <|G := exec_plan (s,rem_effectless_act (rem_condless_act (s,[],p))); I := s|>, rem_effectless_act (rem_condless_act (s,[],p)))` by SRW_TAC[][graph_plan_lemma_6, graph_plan_lemma_16, graph_plan_lemma_7]
	      	   THEN `vs SUBSET FDOM ((PROB with <|G := exec_plan (s,(rem_effectless_act (rem_condless_act (s,[],p)))); I := s|>).I)` by SRW_TAC[][]		   
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



val child_parent_lemma_2_1_3 = store_thm("child_parent_lemma_2_1_3",
``!l P1 P2 P3 k1 k2. ((! x. MEM x l ==> (P1 x /\ ~P2 x) \/ (~P1 x /\ P2 x)) /\ LENGTH (FILTER P1 l) < k1
     /\ (!l'.  (?pfx sfx. pfx ++ l' ++ sfx = l) /\ (! x. MEM x l' ==> (P2 x)) ==> LENGTH l' < k2 ))
     ==>
     LENGTH(l) < k1 ** k2``

);

*)
val _ = export_theory();




