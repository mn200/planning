open HolKernel Parse boolLib QLib tautLib mesonLib metisLib
     simpLib boolSimps BasicProvers;
open finite_mapTheory
open arithmeticTheory
open pred_setTheory
open rich_listTheory
open listTheory;							 
open utilsTheory;
open FM_planTheory 
open sublistTheory;
open GraphPlanTheoremTheory;
open relationTheory;
open SCCTheory;
val _ = new_theory "SCCGraphPlanTheorem";


val dep_tc_def = Define `dep_tc (PROB)   =  TC (\v1' v2'. dep(PROB, v1', v2'))`;

val ancestors_def = Define
 `ancestors(PROB: 'a problem, vs: ('a -> bool)) = 
    {v: 'a | (?v': 'a. v' IN vs /\ ((dep_tc(PROB)) v v') ) /\ (!v': 'a. v' IN vs ==> ~((dep_tc(PROB)) v' v))}`;

val scc_vs_def = Define 
`scc_vs(PROB, vs) 
    = SCC (\v1' v2'. dep(PROB, v1', v2')) vs`;
 

val scc_set_def = Define
`scc_set PROB S = !vs. vs IN S ==> scc_vs(PROB, vs)`;


val sum_scc_parents_def 
  = Define` sum_scc_parents(PROB, S) 
     = SIGMA (\vs. problem_plan_bound((prob_proj(PROB, vs UNION (ancestors(PROB, vs)))))) S + 1`;

val childless_vs_def = Define`
      childless_vs(PROB, vs) = !vs'. (* DISJOINT vs vs' ==> *) ~(dep_var_set(PROB, vs, vs'))`


val childless_svs_def = Define`
      childless_svs(PROB, S) = !vs. vs IN S ==> (childless_vs(PROB, vs))`;

val problem_scc_set_def = Define`
      problem_scc_set(PROB) = {vs | (scc_vs(PROB, vs)) }`;


val childless_problem_scc_set_def = Define`
      childless_problem_scc_set(PROB) = {vs | (scc_vs(PROB, vs)) /\ (childless_vs(PROB, vs))}`;



val single_child_parents_def = Define
`single_child_parents(PROB, vs) 
           = {vs' | vs' SUBSET (ancestors(PROB, vs)) 
                       /\ childless_vs(prob_proj(PROB, (FDOM PROB.I) DIFF vs), vs') 
                            /\scc_vs(PROB, vs')}`;


(*
val single_child_ancestors_def_1 = store_thm("single_child_ancestors_def_1",
``WF (\x y. CARD (FDOM (FST(x)).I ) < CARD(FDOM ((FST(y)).I)))``,
cheat(*SRW_TAC[][WF_DEF]
THEN Q.EXISTS_TAC `(prob_proj((FST w), EMPTY) , SND w)`
SRW_TAC[][]
THEN SRW_TAC[][prob_proj_def]
THENL
[
   METIS_TAC[]
   ,
   FULL_SIMP_TAC(srw_ss())[FDOM_DRESTRICT]
]*));

val single_child_ancestors_def_2_1 = store_thm("single_child_ancestors_def_2_1",
``!s t.FINITE s /\ FINITE t /\ s SUBSET t ==> (t INTER (t DIFF s) = t DIFF s)``, 
SRW_TAC[][SUBSET_DEF, INTER_DEF, DIFF_DEF, EXTENSION]
THEN METIS_TAC[]
)


val single_child_ancestors_def_2 = store_thm("single_child_ancestors_def_2",
``!PROB vs vs'. vs SUBSET FDOM(PROB.I) /\ ~(vs = EMPTY) 
                ==> CARD(FDOM((prob_proj(PROB, (FDOM(PROB.I)) DIFF vs)).I)) < CARD(FDOM(PROB.I))``,
SRW_TAC[][prob_proj_def, FDOM_DRESTRICT]
THEN `FINITE (FDOM(PROB.I))` by SRW_TAC[][]
THEN `FINITE vs` by METIS_TAC[SUBSET_FINITE]
THEN MP_TAC(single_child_ancestors_def_2_1 |> Q.SPECL[`vs`,`(FDOM PROB.I)`])
THEN SRW_TAC[][]
THEN MP_TAC(REWRITE_RULE [Once INTER_COMM] (bound_child_parent_lemma_1_1_1_3_1_3 |> Q.SPECL[`vs`, `FDOM PROB.I`]))
THEN SRW_TAC[][]
THEN `~(CARD vs = 0)` by METIS_TAC[(GSYM CARD_EQ_0 |> Q.SPEC `vs`)] 
THEN1 DECIDE_TAC
THEN MP_TAC(CARD_SUBSET |>  Q.SPEC `FDOM PROB.I`)
THEN SRW_TAC[][]  
THEN Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `vs`)
THEN SRW_TAC[][]
THEN DECIDE_TAC
);


val single_child_ancestors_def = tDefine "single_child_ancestors"
   `single_child_ancestors(PROB, vs) = 
          if(vs SUBSET FDOM(PROB.I) /\ ~(vs = EMPTY)) then
             single_child_parents(PROB, vs) 
              UNION BIGUNION (IMAGE 
                   (\vs'. single_child_ancestors((prob_proj(PROB, (FDOM PROB.I) DIFF vs)), vs')) 
                                  (single_child_parents(PROB, vs)))
          else {}`
(WF_REL_TAC `measure (CARD o FDOM o (\PROB. PROB.I) o FST)`
THEN METIS_TAC[single_child_ancestors_def_2]);
*)

(*
(* remove the ~(vs = vs') condition becase it is a contradiction
because of SCCTheory SCC_loop_contradict*)
val single_child_ancestors_def = Define`single_child_ancestors PROB vs
= {vs' | ~(vs' = vs) /\ scc_vs (PROB, vs') /\ (\vs vs'. dep_var_set(PROB, vs, vs'))^+ vs' vs 
         /\  (!vs''. (\vs vs'. dep_var_set(PROB, vs, vs'))^+ vs' vs'' 
                     /\ childless_vs(PROB, vs'') /\ scc_vs(PROB, vs'')
                     ==>  (vs'' = vs))}`;
*)

(* remove the ~(vs = vs') condition becase it is a contradiction
because of SCCTheory SCC_loop_contradict*)
val single_child_ancestors_def = Define`single_child_ancestors PROB vs
= {vs' | ~(vs' = vs) /\ scc_vs (PROB, vs') /\ (\vs vs'. dep_var_set(PROB, vs, vs'))^+ vs' vs 
         /\  (!vs''. (\vs vs'. dep_var_set(PROB, vs, vs'))^+ vs' vs'' 
                     /\ childless_vs(PROB, vs'')
                     ==>  (vs'' SUBSET vs))}`;

val member_leaves_def = Define
     `member_leaves(PROB, S) 
           =  (\vs. (scc_vs(PROB, vs) /\ childless_vs(PROB, vs))) INTER S`;

val problem_wo_vs_ancestors_def = Define
  `problem_wo_vs_ancestors(PROB, vs) = 
              prob_proj(PROB, FDOM PROB.I DIFF (vs ∪ BIGUNION (single_child_ancestors PROB vs)))`;



val scc_main_lemma_x = store_thm("scc_main_lemma_x",
``!s t x. x IN s /\ ~(x IN t) ==> ~(s = t)``,
METIS_TAC[])
 
val scc_main_lemma_xx = store_thm("scc_main_lemma_xx",
``!PROB vs vs'. scc_vs(PROB, vs) /\ scc_vs(PROB, vs') /\ ~(vs = vs') ==> DISJOINT vs vs'``,
METIS_TAC[scc_disjoint_lemma, scc_vs_def])


val scc_lemma_1_1 = store_thm("scc_lemma_1_1",
``!PROB S. FINITE(S) ==> FINITE((member_leaves(PROB, S)))``,
SRW_TAC[][member_leaves_def]
THEN METIS_TAC[FINITE_INTER]);

val scc_lemma_1_2 = store_thm("scc_lemma_1_2",
``!PROB vs S. vs IN member_leaves(PROB, S) ==> scc_vs(PROB, vs)``,
SRW_TAC[][member_leaves_def]);

val scc_lemma_1_3 = store_thm("scc_lemma_1_3",
``!PROB vs S. vs IN member_leaves(PROB, S) ==> vs IN S``,
SRW_TAC[][member_leaves_def]);



val scc_lemma_1_5 = store_thm("scc_lemma_1_5",
``!PROB vs S. vs IN member_leaves(PROB, S) ==> childless_vs(PROB, vs)``,
SRW_TAC[][member_leaves_def]);


val scc_lemma_1_4_1_1_1 = store_thm("scc_lemma_1_4_1_1_1",
``!PROB vs vs'. scc_vs(PROB, vs') /\ childless_vs(PROB, vs') 
                ==> DISJOINT  vs' (BIGUNION (single_child_ancestors PROB vs))``,
SRW_TAC[][childless_vs_def, single_child_ancestors_def]
THEN MP_TAC(TC_CASES1 |> Q.ISPEC `(λvs vs'. dep_var_set (PROB,vs,vs'))` |> Q.SPECL[`s'`, `vs`])
THEN SRW_TAC[][]
THENL
[
   Cases_on `s' = vs'`
   THEN METIS_TAC[scc_disjoint_lemma, scc_vs_def]
   ,
   Cases_on `s' = vs'`
   THEN METIS_TAC[scc_disjoint_lemma, scc_vs_def]
])

val scc_lemma_1_4_1_1_2_1_1_1_1 = store_thm("scc_lemma_1_4_1_1_2_1_1_1_1",
``!fdom vs v f. ~(v IN vs) /\ FDOM f SUBSET fdom /\ v IN FDOM f
                ==> v IN FDOM(DRESTRICT f (fdom DIFF vs))``,
SRW_TAC[][dep_def, prob_proj_def, DIFF_DEF, INTER_DEF, EXTENSION, GSPEC_ETA, DISJOINT_DEF, SUBSET_DEF, FDOM_DRESTRICT])

val scc_lemma_1_4_1_1_2_1_1_1 = store_thm("scc_lemma_1_4_1_1_2_1_1_1",
``!PROB vs v a. ~(v IN vs) /\ a IN PROB.A /\ planning_problem(PROB)
                ==> ((v IN FDOM(FST a) ==> v IN FDOM(FST (action_proj(a, FDOM PROB.I DIFF vs))))
                    /\ (v IN FDOM(SND a) ==> v IN FDOM(SND (action_proj(a, FDOM PROB.I DIFF vs)))))``,
SRW_TAC[][planning_problem_def, action_proj_def]
THEN METIS_TAC[scc_lemma_1_4_1_1_2_1_1_1_1])


val scc_lemma_1_4_1_1_2_1_1 = store_thm("scc_lemma_1_4_1_1_2_1_1",
``!PROB  vs vs' v v'. planning_problem(PROB) /\ v IN vs' /\ v' IN vs'  /\ DISJOINT vs vs'
              ==> (dep(PROB, v, v') ==> dep(prob_proj(PROB, FDOM PROB.I DIFF vs), v, v'))``,
SRW_TAC[][dep_def, prob_proj_def, DIFF_DEF, INTER_DEF, EXTENSION, GSPEC_ETA, DISJOINT_DEF]
THEN Q.EXISTS_TAC `action_proj(a, FDOM PROB.I DIFF vs)` 
THEN SRW_TAC[][]
THENL
[
   Q.EXISTS_TAC `a` 
   THEN SRW_TAC[][action_proj_def, DIFF_DEF, EXTENSION, GSPEC_ETA]
   ,
   METIS_TAC[scc_lemma_1_4_1_1_2_1_1_1]
   ,
   Q.EXISTS_TAC `a` 
   THEN SRW_TAC[][action_proj_def, DIFF_DEF, EXTENSION, GSPEC_ETA]
   ,
   METIS_TAC[scc_lemma_1_4_1_1_2_1_1_1]
])

val scc_lemma_1_4_1_1_2_1_2 = store_thm("scc_lemma_1_4_1_1_2_1_2",
``!PROB vs v v'. v IN vs /\ v' IN vs  /\ scc_vs(PROB, vs)
              ==> ((\v v'. dep(PROB, v, v') /\ v IN vs /\ v' IN vs)^+ v v')``,
SRW_TAC[][scc_vs_def]
THEN METIS_TAC[(scc_tc_inclusion |> Q.ISPEC `(λv1' v2'. dep (PROB,v1',v2'))`)])

val scc_lemma_1_4_1_1_2_1_4 = store_thm("scc_lemma_1_4_1_1_2_1_4",
``!PROB  vs v v'. (dep(prob_proj(PROB, FDOM PROB.I DIFF vs), v, v') ==> dep(PROB, v, v'))``,
SRW_TAC[][dep_def, prob_proj_def]
THEN Q.EXISTS_TAC `a'`
THEN SRW_TAC[][]
THEN FULL_SIMP_TAC(bool_ss)[pairTheory.FST, pairTheory.SND, FDOM_DRESTRICT]
THEN METIS_TAC[INTER_SUBSET, SUBSET_DEF]
)


val scc_lemma_1_4_1_1_2_1 = store_thm("scc_lemma_1_4_1_1_2_1",
``!PROB vs vs'. planning_problem(PROB) /\ scc_vs(PROB, vs') /\ DISJOINT vs vs'
                ==> scc_vs (prob_proj (PROB,FDOM PROB.I DIFF vs),vs')``,
SRW_TAC[][scc_vs_def, SCC_def]
THENL
[
   MP_TAC(scc_lemma_1_4_1_1_2_1_1 |> Q.SPECL[`PROB`, `vs`, `vs'`])
   THEN SRW_TAC[][]
   THEN MP_TAC(REWRITE_RULE[scc_vs_def, SCC_def] scc_lemma_1_4_1_1_2_1_2 |> Q.SPECL[`PROB`, `vs'`])
   THEN SRW_TAC[][]
   THEN MP_TAC(scc_lemma_1_4_1_1_2_1_3 |> Q.SPECL[`(\v v'. dep(PROB, v, v'))`, 
                                           `(\v v'. dep(prob_proj(PROB, FDOM PROB.I DIFF vs), v, v'))`,
                                           `(\v. v IN vs')`])
   THEN SRW_TAC[][]
   ,
   MP_TAC(scc_lemma_1_4_1_1_2_1_1 |> Q.SPECL[`PROB`, `vs`, `vs'`])
   THEN SRW_TAC[][]
   THEN MP_TAC(REWRITE_RULE[scc_vs_def, SCC_def] scc_lemma_1_4_1_1_2_1_2 |> Q.SPECL[`PROB`, `vs'`])
   THEN SRW_TAC[][]
   THEN MP_TAC(scc_lemma_1_4_1_1_2_1_3 |> Q.SPECL[`(\v v'. dep(PROB, v, v'))`, 
                                           `(\v v'. dep(prob_proj(PROB, FDOM PROB.I DIFF vs), v, v'))`,
                                           `(\v. v IN vs')`])
   THEN SRW_TAC[][]
   ,
   Q.PAT_ASSUM `!x y. P x y ==> Q x y \/ N x y` (MP_TAC o Q.SPECL[`v`, `v'`])
   THEN SRW_TAC[][]
   THENL
   [
     `¬(λv1' v2'. dep (prob_proj (PROB,FDOM PROB.I DIFF vs),v1',v2'))⁺ v v'`
        by(REWRITE_TAC[TC_DEF]
        THEN SRW_TAC[][]
        THEN Q.PAT_ASSUM `¬(λv1' v2'. dep (PROB,v1',v2'))⁺ v v'` (MP_TAC o REWRITE_RULE[TC_DEF])
        THEN SRW_TAC[][]
        THEN Q.EXISTS_TAC `P`
        THEN METIS_TAC[scc_lemma_1_4_1_1_2_1_4])
     THEN SRW_TAC[][]
     ,
     `¬(λv1' v2'. dep (prob_proj (PROB,FDOM PROB.I DIFF vs),v1',v2'))⁺ v' v`
        by(REWRITE_TAC[TC_DEF]
        THEN SRW_TAC[][]
        THEN Q.PAT_ASSUM `¬(λv1' v2'. dep (PROB,v1',v2'))⁺ v v'` (MP_TAC o REWRITE_RULE[TC_DEF])
        THEN SRW_TAC[][]
        THEN Q.EXISTS_TAC `P`
        THEN METIS_TAC[scc_lemma_1_4_1_1_2_1_4])
     THEN SRW_TAC[][]
   ]
])

val scc_lemma_1_4_1_1_2_2_1_1_1 = store_thm("scc_lemma_1_4_1_1_2_2_1_1_1",
``!a vs. (FDOM(FST (action_proj(a, vs))) SUBSET FDOM (FST a))
         /\ (FDOM(SND (action_proj(a, vs))) SUBSET FDOM (SND a))``,
SRW_TAC[][action_proj_def, SUBSET_DEF, FDOM_DRESTRICT])

val scc_lemma_1_4_1_1_2_2_1_1 = store_thm("scc_lemma_1_4_1_1_2_2_1_1",
``!a v vs. (~(v IN FDOM(FST a)) ==> ~(v IN FDOM(FST (action_proj(a, vs)))))
           /\ (~(v IN FDOM(SND a)) ==> ~(v IN FDOM(SND (action_proj(a, vs)))))``,
SRW_TAC[][]
THEN MP_TAC(REWRITE_RULE[SUBSET_DEF] scc_lemma_1_4_1_1_2_2_1_1_1)
THEN SRW_TAC[][]
THEN METIS_TAC[])

val scc_lemma_1_4_1_1_2_2_1 = store_thm("scc_lemma_1_4_1_1_2_2_1",
``!PROB vs vs' vs''. ~dep_var_set(PROB, vs, vs') 
                     ==> ~dep_var_set(prob_proj(PROB, vs''), vs, vs')``,
SRW_TAC[][dep_var_set_def, prob_proj_def, dep_def]
THEN SRW_TAC[][GSYM action_proj_def]
THEN FIRST_X_ASSUM (MP_TAC o Q.SPECL [`v1`, `v2`])
THEN SRW_TAC[][]
THEN1 METIS_TAC[]
THEN1 METIS_TAC[]
THEN1 METIS_TAC[]
THEN SPOSE_NOT_THEN STRIP_ASSUME_TAC
THEN LAST_X_ASSUM (MP_TAC o Q.SPEC `a'`)
THEN REPEAT STRIP_TAC
THEN FULL_SIMP_TAC(srw_ss())[]
THEN METIS_TAC[scc_lemma_1_4_1_1_2_2_1_1])


val scc_lemma_1_4_1_1_2_2 = store_thm("scc_lemma_1_4_1_1_2_2",
``!PROB vs vs'. childless_vs(PROB, vs') (* /\ DISJOINT vs vs' *)
                ==> childless_vs (prob_proj (PROB,FDOM PROB.I DIFF vs),vs')``,
METIS_TAC[childless_vs_def, scc_lemma_1_4_1_1_2_2_1])

val scc_lemma_1_4_1_1_2 = store_thm("scc_lemma_1_4_1_1_2",
``!PROB vs vs' S. planning_problem(PROB) /\ DISJOINT vs vs' /\ vs' IN member_leaves(PROB, S)
                  ==> vs' IN (member_leaves(prob_proj(PROB, (FDOM PROB.I) DIFF vs), S))``,
SRW_TAC[][member_leaves_def]
THEN METIS_TAC[scc_lemma_1_4_1_1_2_1, scc_lemma_1_4_1_1_2_2])

val scc_lemma_1_4_1_1 = store_thm("scc_lemma_1_4_1_1",
``!PROB vs vs' S. planning_problem(PROB) /\ scc_vs (PROB, vs) /\ ~(vs = vs') /\ vs' IN member_leaves(PROB, S)
                  ==> vs' IN (member_leaves(problem_wo_vs_ancestors(PROB, vs), S))``,
SRW_TAC[][]
THEN MP_TAC(scc_lemma_1_5 |> Q.SPECL [`PROB`, `vs'`, `S'`])
THEN SRW_TAC[][]
THEN MP_TAC(scc_lemma_1_4_1_1_1 |> Q.SPECL[`PROB`, `vs`, `vs'`])
THEN `scc_vs (PROB,vs')` by FULL_SIMP_TAC(srw_ss())[member_leaves_def]
THEN ASM_SIMP_TAC(bool_ss)[]
THEN STRIP_TAC
THEN `DISJOINT vs vs'` by METIS_TAC[scc_main_lemma_xx, scc_lemma_1_2]
THEN REWRITE_TAC[problem_wo_vs_ancestors_def]
THEN METIS_TAC[scc_lemma_1_4_1_1_2,  GSYM DISJOINT_UNION, DISJOINT_SYM])

val scc_lemma_1_4_1 = store_thm("scc_lemma_1_4_1",
``!PROB S vs. planning_problem(PROB) /\ scc_vs(PROB, vs) ==> (member_leaves(PROB, S) DELETE vs) 
SUBSET (member_leaves(problem_wo_vs_ancestors(PROB, vs), S))``,
SRW_TAC[][scc_lemma_1_4_1_1, Once (GSYM IN_DELETE), SUBSET_DEF]
);



(* 
val scc_lemma_1_4_2_1_1_1_4 = store_thm("scc_lemma_1_4_2_1_1_1_4",
``!PROB v v'. ~(v' IN FDOM PROB.I) ==> ~dep(PROB, v, v')``,
cheat)

val scc_lemma_1_4_2_1_1_1_5 = store_thm("scc_lemma_1_4_2_1_1_1_5",
``!s t. DISJOINT s (t DIFF s)``,
SRW_TAC[][]
THEN cheat)

val scc_lemma_1_4_2_1_1_1_6 = store_thm("scc_lemma_1_4_2_1_1_1_6",
``!PROB vs v v'. (v IN vs) /\ ~(v' IN vs) /\ (λv1' v2'. dep (PROB,v1',v2'))⁺ v v'
            ==> ?v'' v'''. v'' IN vs /\ ~(v''' IN vs) /\ dep(PROB, v'', v''')``,
cheat)
*)

val scc_lemma_1_4_2_1_1_1_1_1 = store_thm("scc_lemma_1_4_2_1_1_1_1_1",                
``!PROB v v'. planning_problem(PROB) /\ dep(PROB, v, v')
              ==> v IN FDOM PROB.I /\ v' IN FDOM PROB.I``,
SRW_TAC[][dep_def, planning_problem_def, SUBSET_DEF]
THEN METIS_TAC[])

val scc_lemma_1_4_2_1_1_1_1 = store_thm("scc_lemma_1_4_2_1_1_1_1",                
``!PROB vs. planning_problem(PROB) /\ scc_vs(PROB, vs) ==> vs SUBSET FDOM PROB.I``,
SRW_TAC[][scc_vs_def, SCC_def, SUBSET_DEF]
THEN `(λv1' v2'. dep (PROB,v1',v2'))⁺ x x` by METIS_TAC[]
THEN MP_TAC(TC_CASES1 |> Q.SPECL[`(λv1' v2'. dep (PROB,v1',v2'))`, `x`, `x`])
THEN METIS_TAC[scc_lemma_1_4_2_1_1_1_1_1]
)

val scc_lemma_1_4_2_1_1_1_2_1 = store_thm("scc_lemma_1_4_2_1_1_1_2_1",                
``!s t u. s SUBSET t /\ s SUBSET (t DIFF u)
          ==> DISJOINT s u``,
SRW_TAC[][SUBSET_DEF, DISJOINT_DEF, INTER_DEF, EXTENSION]
THEN METIS_TAC[])

val scc_lemma_1_4_2_1_1_1_2 = store_thm("scc_lemma_1_4_2_1_1_1_2",                
``!PROB vs vs'. vs SUBSET FDOM (prob_proj(PROB, FDOM PROB.I DIFF vs')).I
                ==> DISJOINT vs vs'``,
SRW_TAC[][prob_proj_def, FDOM_DRESTRICT]
THEN METIS_TAC[scc_lemma_1_4_2_1_1_1_2_1])




val scc_lemma_1_4_2_1_1_1_3_1 = store_thm("scc_lemma_1_4_2_1_1_1_3_1",
``!PROB vs v v'. (~(v IN vs) /\ ~(v' IN vs)) /\
                     dep (PROB,v,v') ==>  dep (prob_proj (PROB,FDOM PROB.I DIFF vs),v,v')``,
cheat
(*
SRW_TAC[][dep_def, prob_proj_def]
THEN FIRST_X_ASSUM (MP_TAC o Q.SPEC `a`)
THEN SRW_TAC[][]
THEN 
*))



val scc_lemma_1_4_2_1_1_1_3_3 = store_thm("scc_lemma_1_4_2_1_1_1_3_3",
``!PROB. planning_problem(PROB) ==> reflexive (\v v'. dep (PROB,v,v'))``,
cheat
(*SRW_TAC[][dep_def, reflexive_def, planning_problem_def]
*))




val scc_lemma_1_4_2_1_1_1_3 = store_thm("scc_lemma_1_4_2_1_1_1_3",
``!PROB vs v v'. ~(λv1' v2'. dep(prob_proj (PROB,FDOM PROB.I DIFF vs),v1',v2'))⁺ v v' 
                 ==> ((¬(λv1' v2'. dep (PROB,v1',v2'))⁺ v v') 
                      \/ (?v''. v'' IN vs /\ (λv1' v2'. dep (PROB,v1',v2'))⁺ v v'' 
                                /\ (λv1' v2'. dep (PROB,v1',v2'))⁺ v'' v'))``,
SRW_TAC[][]
THEN MP_TAC(REWRITE_RULE[Once (GSYM AND_IMP_INTRO)] scc_lemma_1_4_2_1_1_1_3_1 |> Q.SPECL [`PROB`, `vs`])
THEN SRW_TAC[][]
THEN MP_TAC(REWRITE_RULE[Once (GSYM AND_IMP_INTRO)] scc_lemma_1_4_2_1_1_1_3_3 |> Q.SPECL [`PROB`])
THEN SRW_TAC[][]
THEN MP_TAC(scc_lemma_1_4_2_1_1_1_3_2 |> Q.SPECL[`(\v v'. dep (prob_proj (PROB,FDOM PROB.I DIFF vs),v,v'))`,
                                          `(\v v'. dep (PROB,v,v'))`,
                                          `(\v. ~(v IN vs))`,
                                          `v`, `v'`])
THEN SRW_TAC[][])


val scc_lemma_1_4_2_1_1_1 = store_thm("scc_lemma_1_4_2_1_1_1",
``!PROB S vs. planning_problem(PROB) 
               /\ ~(S = {}) /\ scc_set PROB S
               /\ scc_vs(prob_proj (PROB,FDOM PROB.I DIFF BIGUNION S), vs)
               ==> scc_vs(PROB, vs)``,
SRW_TAC[][]
THEN `DISJOINT vs (BIGUNION S')` 
   by METIS_TAC[scc_lemma_1_4_2_1_1_1_1, scc_lemma_1_4_2_1_1_1_2, graph_plan_lemma_2_2]
THEN FULL_SIMP_TAC(srw_ss())[scc_vs_def, SCC_def]
THEN SRW_TAC[][]
THENL
[
   MP_TAC(scc_lemma_1_4_1_1_2_1_4 |> Q.SPECL[`PROB`, `BIGUNION S'`])
   THEN SRW_TAC[][]
   THEN MP_TAC(((Q.GEN `R` o Q.GEN `Q` o Q.GEN `x` o Q.GEN `y`) TC_MONOTONE)
             |> Q.ISPECL [`(\v v'. dep (prob_proj (PROB,FDOM PROB.I DIFF (BIGUNION S')),v,v'))`,
                          `(\v v'. dep (PROB,v,v'))`])
   THEN SRW_TAC[][]  
   ,
   MP_TAC(scc_lemma_1_4_1_1_2_1_4 |> Q.SPECL[`PROB`, `BIGUNION S'`])
   THEN SRW_TAC[][]
   THEN MP_TAC(((Q.GEN `R` o Q.GEN `Q` o Q.GEN `x` o Q.GEN `y`) TC_MONOTONE)
             |> Q.ISPECL [`(\v v'. dep (prob_proj (PROB,FDOM PROB.I DIFF (BIGUNION S')),v,v'))`,
                          `(\v v'. dep (PROB,v,v'))`])
   THEN SRW_TAC[][]  
   ,   
   Q.PAT_ASSUM `!x y. P x y ==> Q x y \/ N x y` (MP_TAC o Q.SPECL[`v`, `v'`])
   THEN SRW_TAC[][]
   THENL
   [
      Cases_on `v' IN BIGUNION S'`
      THENL
      [
         `!s. s IN S' ==> ~(v IN s)`
            by (FULL_SIMP_TAC(bool_ss)[DISJOINT_DEF, INTER_DEF, EXTENSION, GSPEC_ETA, EMPTY_DEF, IN_DEF]
               THEN METIS_TAC[])
         THEN FULL_SIMP_TAC(bool_ss)[IN_BIGUNION]
         THEN `scc_vs(PROB, s)` by FULL_SIMP_TAC(srw_ss())[scc_set_def]
         THEN FULL_SIMP_TAC(srw_ss())[scc_vs_def, SCC_def]
         THEN METIS_TAC[]
         ,
         Cases_on `(λv1' v2'.
          dep (prob_proj (PROB,FDOM PROB.I DIFF BIGUNION S'),v1',v2'))⁺
         v' v`
         THENL
         [
            `(λv1' v2'. dep (PROB,v1',v2'))⁺ v' v` by METIS_TAC[scc_lemma_1_4_1_1_2_1_4, 
                                                                (((Q.GEN `R` o Q.GEN `Q` o Q.GEN `x` o Q.GEN `y`) TC_MONOTONE)
                                                                       |> Q.ISPECL [`(\v v'. dep (prob_proj (PROB,FDOM PROB.I DIFF (BIGUNION S')),v,v'))`,
                                                                                    `(\v v'. dep (PROB,v,v'))`])]
            THEN SRW_TAC[][]
            THEN FULL_SIMP_TAC(srw_ss())[childless_vs_def, dep_var_set_def]
            THEN MP_TAC(scc_lemma_1_4_2_1_1_1_3 |> Q.SPECL[`PROB`,`BIGUNION S'`, `v`, `v'`])  
            THEN SRW_TAC[][]
            THEN `(λv1' v2'. dep (PROB,v1',v2'))⁺ v'' v` by METIS_TAC[TC_RULES |> Q.SPEC `(λv1' v2'. dep (PROB,v1',v2'))`]
            THEN `!s. s IN S' ==> ~(v' IN s)`
                  by (FULL_SIMP_TAC(bool_ss)[DISJOINT_DEF, INTER_DEF, EXTENSION, GSPEC_ETA, EMPTY_DEF, IN_DEF]
                     THEN METIS_TAC[])
            THEN FULL_SIMP_TAC(bool_ss)[IN_BIGUNION]
            THEN `scc_vs(PROB, s)` by FULL_SIMP_TAC(srw_ss())[scc_set_def]
            THEN FULL_SIMP_TAC(srw_ss())[scc_vs_def, SCC_def]
            THEN METIS_TAC[]
            ,            
            MP_TAC(scc_lemma_1_4_2_1_1_1_3 |> Q.SPECL[`PROB`,`BIGUNION S'`, `v`, `v'`])  
            THEN SRW_TAC[][]
            THEN1 METIS_TAC[]
            THEN MP_TAC(scc_lemma_1_4_2_1_1_1_3 |> Q.SPECL[`PROB`,`BIGUNION S'`, `v'`, `v`])  
            THEN SRW_TAC[][]
            THEN1 METIS_TAC[]
            THEN `(λv1' v2'. dep (PROB,v1',v2'))⁺ v' v''` by METIS_TAC[TC_RULES |> Q.SPEC `(λv1' v2'. dep (PROB,v1',v2'))`]
            THEN `(λv1' v2'. dep (PROB,v1',v2'))⁺ v'' v'` by METIS_TAC[TC_RULES |> Q.SPEC `(λv1' v2'. dep (PROB,v1',v2'))`]            
            THEN `!s. s IN S' ==> ~(v' IN s)`
                  by (FULL_SIMP_TAC(srw_ss())[DISJOINT_DEF, INTER_DEF, EXTENSION, GSPEC_ETA, EMPTY_DEF, IN_DEF]
                     THEN METIS_TAC[])
            THEN FULL_SIMP_TAC(bool_ss)[IN_BIGUNION]
            THEN `scc_vs(PROB, s)` by FULL_SIMP_TAC(srw_ss())[scc_set_def]
            THEN FULL_SIMP_TAC(srw_ss())[scc_vs_def, SCC_def]
            THEN METIS_TAC[]
         ]
      ]
      ,
      Cases_on `v' IN BIGUNION S'`
      THENL
      [
         `!s. s IN S' ==> ~(v IN s)`
            by (FULL_SIMP_TAC(bool_ss)[DISJOINT_DEF, INTER_DEF, EXTENSION, GSPEC_ETA, EMPTY_DEF, IN_DEF]
               THEN METIS_TAC[])
         THEN FULL_SIMP_TAC(bool_ss)[IN_BIGUNION]
         THEN `scc_vs(PROB, s)` by FULL_SIMP_TAC(srw_ss())[scc_set_def]
         THEN FULL_SIMP_TAC(srw_ss())[scc_vs_def, SCC_def]
         THEN METIS_TAC[]
         ,
         Cases_on `(λv1' v2'.
          dep (prob_proj (PROB,FDOM PROB.I DIFF BIGUNION S'),v1',v2'))⁺
         v v'`
         THENL
         [
            `(λv1' v2'. dep (PROB,v1',v2'))⁺ v v'` by METIS_TAC[scc_lemma_1_4_1_1_2_1_4, 
                                                                (((Q.GEN `R` o Q.GEN `Q` o Q.GEN `x` o Q.GEN `y`) TC_MONOTONE)
                                                                       |> Q.ISPECL [`(\v v'. dep (prob_proj (PROB,FDOM PROB.I DIFF (BIGUNION S')),v,v'))`,
                                                                                    `(\v v'. dep (PROB,v,v'))`])]
            THEN SRW_TAC[][]
            THEN FULL_SIMP_TAC(srw_ss())[childless_vs_def, dep_var_set_def]
            THEN MP_TAC(scc_lemma_1_4_2_1_1_1_3 |> Q.SPECL[`PROB`,`BIGUNION S'`, `v'`, `v`])  
            THEN SRW_TAC[][]
            THEN `(λv1' v2'. dep (PROB,v1',v2'))⁺ v'' v'` by METIS_TAC[TC_RULES |> Q.SPEC `(λv1' v2'. dep (PROB,v1',v2'))`]
            THEN `!s. s IN S' ==> ~(v' IN s)`
                  by (FULL_SIMP_TAC(bool_ss)[DISJOINT_DEF, INTER_DEF, EXTENSION, GSPEC_ETA, EMPTY_DEF, IN_DEF]
                     THEN METIS_TAC[])
            THEN FULL_SIMP_TAC(bool_ss)[IN_BIGUNION]
            THEN `scc_vs(PROB, s)` by FULL_SIMP_TAC(srw_ss())[scc_set_def]
            THEN FULL_SIMP_TAC(srw_ss())[scc_vs_def, SCC_def]
            THEN METIS_TAC[]
            ,            
            MP_TAC(scc_lemma_1_4_2_1_1_1_3 |> Q.SPECL[`PROB`,`BIGUNION S'`, `v`, `v'`])  
            THEN SRW_TAC[][]
            THEN1 METIS_TAC[]
            THEN MP_TAC(scc_lemma_1_4_2_1_1_1_3 |> Q.SPECL[`PROB`,`BIGUNION S'`, `v'`, `v`])  
            THEN SRW_TAC[][]
            THEN1 METIS_TAC[]
            THEN `(λv1' v2'. dep (PROB,v1',v2'))⁺ v' v''` by METIS_TAC[TC_RULES |> Q.SPEC `(λv1' v2'. dep (PROB,v1',v2'))`]
            THEN `(λv1' v2'. dep (PROB,v1',v2'))⁺ v'' v'` by METIS_TAC[TC_RULES |> Q.SPEC `(λv1' v2'. dep (PROB,v1',v2'))`]            
            THEN `!s. s IN S' ==> ~(v' IN s)`
                  by (FULL_SIMP_TAC(srw_ss())[DISJOINT_DEF, INTER_DEF, EXTENSION, GSPEC_ETA, EMPTY_DEF, IN_DEF]
                     THEN METIS_TAC[])
            THEN FULL_SIMP_TAC(bool_ss)[IN_BIGUNION]
            THEN `scc_vs(PROB, s)` by FULL_SIMP_TAC(srw_ss())[scc_set_def]
            THEN FULL_SIMP_TAC(srw_ss())[scc_vs_def, SCC_def]
            THEN METIS_TAC[]
         ]
      ]
   ]      
])


val scc_lemma_1_4_2_1_1 = store_thm("scc_lemma_1_4_2_1_1",
``!PROB S. planning_problem(PROB) /\ scc_set PROB S
           ==> (problem_scc_set (prob_proj(PROB, FDOM PROB.I DIFF BIGUNION S))) SUBSET (problem_scc_set PROB) ``,
SRW_TAC[][problem_scc_set_def, SUBSET_DEF]
THEN METIS_TAC[scc_lemma_1_4_2_1_1_1])

                
val scc_lemma_1_4_2_1_2 = store_thm("scc_lemma_1_4_2_1_2",
``!PROB vs vs'. childless_vs(prob_proj(PROB, FDOM PROB.I DIFF vs), vs')
                ==> (childless_vs(PROB, vs') 
                     \/ (!vs''. (dep_var_set (PROB,vs',vs'')) 
                               ==> childless_vs (PROB,vs'') /\  vs'' SUBSET vs))``,
cheat)

val scc_lemma_1_4_2_1_3 = store_thm("scc_lemma_1_4_2_1_3",
``!PROB vs vs'. scc_vs(PROB, vs') /\ (?vs''. dep_var_set(PROB, vs', vs''))
                /\ (!vs'''. (dep_var_set (PROB,vs',vs''')) 
                               ==> vs''' SUBSET vs)
                ==> vs' IN single_child_ancestors PROB vs``,
cheat(*
SRW_TAC[][single_child_ancestors_def]
THENL
[
   FULL_SIMP_TAC(srw_ss())[dep_var_set_def]
   THEN FULL_SIMP_TAC(srw_ss())[SUBSET_DEF, DISJOINT_DEF, EXTENSION]
   THEN METIS_TAC[]
   ,
   
   ,
]*)
)


val scc_lemma_1_4_2_1 = store_thm("scc_lemma_1_4_2_1",
``!PROB S S'. (childless_vs(PROB, BIGUNION S') /\ scc_set PROB S')
                  ==> (member_leaves(prob_proj(PROB, (FDOM PROB.I) DIFF BIGUNION S'), S)) 
                         SUBSET (member_leaves(PROB, S)) 
                             UNION 
                                (single_child_ancestors PROB (BIGUNION S'))``,
SRW_TAC[][member_leaves_def, SUBSET_DEF, UNION_DEF, GSPEC_ETA]
THEN `scc_vs(PROB, x)` 
   by METIS_TAC[(SIMP_RULE(srw_ss())[] o REWRITE_RULE[SUBSET_DEF, problem_scc_set_def, GSPEC_ETA]) scc_lemma_1_4_2_1_1 ]
THEN SRW_TAC[][]
THEN MP_TAC(scc_lemma_1_4_2_1_2 |> Q.SPECL [`PROB`, `(BIGUNION S'')`, `x`])
THEN SRW_TAC[][]
THEN1 METIS_TAC[]
THEN METIS_TAC[scc_lemma_1_4_2_1_3])


val scc_lemma_1_4_2 = store_thm("scc_lemma_1_4_2",
``!PROB vs  S vs'. childless_vs(PROB, vs) /\ ~(vs' IN single_child_ancestors PROB vs) /\ ~(vs' IN member_leaves(PROB, S))
                       ==> ~(vs' IN (member_leaves(prob_proj(PROB, (FDOM PROB.I) DIFF vs), S)))``,
SRW_TAC[][]
THEN METIS_TAC[(SIMP_RULE(srw_ss())[] o REWRITE_RULE[SUBSET_DEF, UNION_DEF, GSPEC_ETA]) scc_lemma_1_4_2_1]);




(*
val scc_lemma_1_4_3_1 = store_thm("scc_lemma_1_4_3_1",
``!PROB vs vs' vs''. (\vs vs'. dep_var_set (PROB,vs,vs'))^+ vs (vs' ∪ vs'')
         ==> ((\vs vs'. dep_var_set (PROB,vs,vs'))^+ vs vs') 
             \/ ((\vs vs'. dep_var_set (PROB,vs,vs'))^+ vs vs'')``,
cheat);

val scc_lemma_1_4_3_2 = store_thm("scc_lemma_1_4_3_2",
``!PROB vs S. (\vs vs'. dep_var_set (PROB,vs,vs'))^+ vs (BIGUNION S)
         ==> ?vs'. vs' IN S /\ (\vs vs'. dep_var_set (PROB,vs,vs'))^+ vs vs'``,
cheat);

 val scc_lemma_1_4_3_6 = store_thm("scc_lemma_1_4_3_6",
``!PROB vs. single_child_ancestors PROB vs ≠ ∅ ==> (BIGUNION (single_child_ancestors PROB vs)) ≠ ∅``,
cheat)

val scc_lemma_1_4_3_2_1 = store_thm("scc_lemma_1_4_3_2_1",
``!PROB vs vs'. (λvs vs'. dep_var_set (PROB,vs,vs'))⁺ vs vs'
         ==> (DISJOINT vs vs' \/ ((vs = vs') /\ ~scc_vs(PROB, vs)))``,
cheat);


 val scc_lemma_1_4_3_3_1 = store_thm("scc_lemma_1_4_3_3_1",
``!PROB. (λvs vs'. dep_var_set (PROB,vs,vs')) 
     = (\vs vs'. lift (\v v'. dep(PROB,v, v')) vs vs' 
        /\ DISJOINT vs vs') ``,
cheat) 

*)





val scc_lemma_1_4_3_2 = store_thm("scc_lemma_1_4_3_2",
``!PROB vs vs'. scc_vs(PROB, vs) /\ vs' IN (single_child_ancestors PROB vs)
                ==> DISJOINT vs vs' /\ ~(vs' = {})``,
SRW_TAC[][single_child_ancestors_def]
THENL
[
   (* If there is time, use SCC_loop_contradict to prove it
    refer t pg 33 in the notebook
    Cases_on `(vs = vs')` *)
   SRW_TAC[SatisfySimps.SATISFY_ss][scc_main_lemma_xx]
   (* THEN FULL_SIMP_TAC(bool_ss)[] *)
   ,
   METIS_TAC[scc_vs_def, SCC_def]
]);


val scc_lemma_1_4_3_3_1 = store_thm("scc_lemma_1_4_3_3_1",
``!PROB vs vs' vs''. dep_var_set (PROB,vs,vs' UNION vs'')  
                     ==> dep_var_set (PROB,vs,vs') \/ dep_var_set (PROB,vs,vs'')``,
SRW_TAC[][dep_var_set_def]
THEN METIS_TAC[DISJOINT_SYM]
)

val scc_lemma_1_4_3_3_2 = store_thm("scc_lemma_1_4_3_3_2",
``!PROB vs S. dep_var_set (PROB,vs, BIGUNION S)  
                     ==> ?vs'. vs' IN S /\ dep_var_set (PROB, vs, vs')``,
SRW_TAC[][dep_var_set_def]
THEN METIS_TAC[DISJOINT_SYM])

val scc_lemma_1_4_3_3_3 = store_thm("scc_lemma_1_4_3_3_3",
``!PROB vs vs'. vs' IN single_child_ancestors PROB vs
                     ==> (\ vs vs'. dep_var_set (PROB, vs, vs'))^+ vs' vs``,
SRW_TAC[][single_child_ancestors_def])


val scc_lemma_1_4_3_3 = store_thm("scc_lemma_1_4_3_3",
``!PROB vs vs'. (\vs vs'. dep_var_set (PROB,vs,vs'))^+ vs (vs' ∪ BIGUNION (single_child_ancestors PROB vs'))
         ==> (\vs vs'. dep_var_set (PROB,vs,vs'))^+ vs vs'``,
SRW_TAC[][]
THEN MP_TAC(TC_CASES2 |> Q.ISPEC `(\vs vs'. dep_var_set (PROB,vs,vs'))`
          |> Q.SPECL[`vs`,
                     `(vs' ∪ BIGUNION (single_child_ancestors PROB vs'))`]) 
THEN SRW_TAC[][]
THENL
[
   MP_TAC(scc_lemma_1_4_3_3_1 |> Q.SPECL[`PROB`, `vs`, `vs'`,
                                           `BIGUNION (single_child_ancestors PROB vs')`] )
   THEN SRW_TAC[][]
   THENL
   [
      SRW_TAC[SatisfySimps.SATISFY_ss][TC_SUBSET]
      ,
      MP_TAC(scc_lemma_1_4_3_3_2 |> Q.SPECL[`PROB`, `vs`, `(single_child_ancestors PROB vs')`])
      THEN SRW_TAC[][]
      THEN METIS_TAC[ scc_lemma_1_4_3_3_3, TC_RULES|> Q.ISPEC `(λvs vs'. dep_var_set (PROB,vs,vs'))`,
                                    TC_SUBSET |> Q.ISPEC `(λvs vs'. dep_var_set (PROB,vs,vs'))`]
   ]
   ,
   MP_TAC(scc_lemma_1_4_3_3_1 |> Q.SPECL[`PROB`, `y`, `vs'`,
                                           `BIGUNION (single_child_ancestors PROB vs')`] )
   THEN SRW_TAC[][]
   THENL
   [
      METIS_TAC[TC_RULES|> Q.ISPEC `(λvs vs'. dep_var_set (PROB,vs,vs'))`,
                                    TC_SUBSET |> Q.ISPEC `(λvs vs'. dep_var_set (PROB,vs,vs'))`]
      ,
      MP_TAC(scc_lemma_1_4_3_3_2 |> Q.SPECL[`PROB`, `y`, `(single_child_ancestors PROB vs')`])
      THEN SRW_TAC[][]
      THEN METIS_TAC[ scc_lemma_1_4_3_3_3, TC_RULES|> Q.ISPEC `(λvs vs'. dep_var_set (PROB,vs,vs'))`,
                                    TC_SUBSET |> Q.ISPEC `(λvs vs'. dep_var_set (PROB,vs,vs'))`]
   ]
]);

val scc_lemma_1_4_3_4 = store_thm("scc_lemma_1_4_3_4",
``!s t u. s SUBSET t ==> (s UNION u )SUBSET (t UNION u)``,
SRW_TAC[][SUBSET_DEF, UNION_DEF])

val scc_lemma_1_4_3_5 = store_thm("scc_lemma_1_4_3_5",
``!s t. ~(s SUBSET t) /\ ~(t SUBSET s)
        ==> s PSUBSET (s UNION t)``,
SRW_TAC[][SUBSET_DEF, UNION_DEF, PSUBSET_DEF, EXTENSION]
THEN METIS_TAC[])

val scc_lemma_1_4_3_6 = store_thm("scc_lemma_1_4_3_6",
``!s t u. (s PSUBSET t) /\ (t SUBSET u)
        ==> s PSUBSET u``,
SRW_TAC[][SUBSET_DEF, UNION_DEF, PSUBSET_DEF, EXTENSION]
THEN METIS_TAC[])

val scc_lemma_1_4_3_7 = store_thm("scc_lemma_1_4_3_7",
``!s t. DISJOINT s t /\ ~(s = {})
        ==> t PSUBSET (s UNION t)``,
SRW_TAC[][SUBSET_DEF, UNION_DEF, PSUBSET_DEF, EXTENSION, DISJOINT_DEF]
THEN METIS_TAC[])

val scc_lemma_1_4_3 = store_thm("scc_lemma_1_4_3",
``!PROB vs. scc_vs(PROB, vs) /\ childless_vs(PROB, vs)
            ==> ((single_child_ancestors PROB (vs 
                           UNION BIGUNION 
                                 (single_child_ancestors PROB vs))) = {})``,
SRW_TAC[][]
THEN Cases_on `(single_child_ancestors PROB vs) = {}`
THEN1 SRW_TAC[][]
THEN1(REWRITE_TAC[Once single_child_ancestors_def]
THEN SPOSE_NOT_THEN STRIP_ASSUME_TAC
THEN FIRST_X_ASSUM  (MP_TAC o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY])
THEN REPEAT STRIP_TAC
THEN FULL_SIMP_TAC(srw_ss())[]
THEN `(vs = vs ∪ BIGUNION (single_child_ancestors PROB vs))` by METIS_TAC[scc_lemma_1_4_3_3]
THEN FULL_SIMP_TAC(srw_ss())[GSYM MEMBER_NOT_EMPTY]
THEN `DISJOINT x' vs /\ ~(x' = {})` by METIS_TAC[scc_lemma_1_4_3_2, DISJOINT_SYM]
THEN `x' SUBSET BIGUNION (single_child_ancestors PROB vs)` by METIS_TAC[SUBSET_BIGUNION_I]
THEN `vs PSUBSET x' UNION vs` by METIS_TAC[scc_lemma_1_4_3_7]
THEN `x' ∪ vs SUBSET (BIGUNION (single_child_ancestors PROB vs)) UNION vs` by METIS_TAC[scc_lemma_1_4_3_4]
THEN `vs PSUBSET vs UNION (BIGUNION (single_child_ancestors PROB vs))` by METIS_TAC[scc_lemma_1_4_3_6,  UNION_COMM]
THEN METIS_TAC[scc_lemma_1_4_3_4, PSUBSET_DEF]));


val scc_lemma_1_4_4 = store_thm("scc_lemma_1_4_4",
``!s t. (!x. ~(x IN s) ==> ~(x IN t)) ==> (t DIFF s = {})``,
SRW_TAC[][IN_DEF, DIFF_DEF, GSPEC_ETA, EXTENSION]
THEN METIS_TAC[]);


val scc_lemma_1_4_5 = store_thm("scc_lemma_1_4_5",
``!x s t. (x INSERT s = t) ==> x IN t``,
SRW_TAC[][INSERT_DEF, GSPEC_ETA]
THEN SRW_TAC[][]);


val scc_lemma_1_4 = store_thm("scc_lemma_1_4",
``!S. FINITE S ==> (!PROB vs S'. planning_problem(PROB) /\ scc_vs(PROB, vs) /\ ~(vs IN S') /\ (member_leaves(PROB, S) = vs INSERT S')
                 ==> (member_leaves(problem_wo_vs_ancestors(PROB, vs), S) = S'))``,
SRW_TAC[][]
THEN Q.PAT_ASSUM `member_leaves (PROB,S') = vs INSERT S''` (ASSUME_TAC o GSYM)
THEN FULL_SIMP_TAC(srw_ss())[DELETE_NON_ELEMENT]
THEN MP_TAC(scc_lemma_1_4_1 |> Q.SPECL [`PROB`, `S'`, `vs`])
THEN SRW_TAC[][DELETE_INSERT]
THEN FULL_SIMP_TAC(srw_ss())[problem_wo_vs_ancestors_def]
THEN MP_TAC(scc_lemma_1_4_2 |> Q.SPECL [`PROB`, `(vs ∪ BIGUNION (single_child_ancestors PROB vs))`, `vs`, `S'`])
THEN SRW_TAC[][]
THEN `!vs'. (vs' ∉ member_leaves (PROB,S') ∨ (vs' = vs)) <=> ~(vs' IN (member_leaves (PROB,S') DELETE vs))` by SRW_TAC[][]
THEN FULL_SIMP_TAC(bool_ss)[]
THEN `childless_vs(PROB, vs)` by (METIS_TAC[scc_lemma_1_4_5, scc_lemma_1_5])
THEN MP_TAC(scc_lemma_1_4_3 |> Q.SPECL[`PROB`, `vs`])
THEN SRW_TAC[][]
THEN `!vs'. ~(vs' IN (single_child_ancestors
        PROB (vs ∪ BIGUNION (single_child_ancestors PROB vs))))` by SRW_TAC[][]
THEN `∀vs'. vs' ∉ (member_leaves (PROB,S') DELETE vs) ⇒
        vs' ∉
        member_leaves
          (prob_proj
             (PROB,
              FDOM PROB.I DIFF
              (vs ∪ BIGUNION (single_child_ancestors PROB vs))),S')` by METIS_TAC[]
THEN MP_TAC (((scc_lemma_1_4_4 |> Q.ISPECL [`member_leaves(PROB,S') DELETE vs`,
                                 `member_leaves
                                  (prob_proj
                                     (PROB,
                                        FDOM PROB.I DIFF
                                          (vs ∪ BIGUNION (single_child_ancestors PROB vs))),S')`])))
THEN ASM_SIMP_TAC(bool_ss)[]
THEN STRIP_TAC
THEN MP_TAC (MATCH_MP (AND1_THM)
 (REWRITE_RULE[IMP_CONJ_THM]  (((Q.GEN `s`o Q.GEN `t` )UNION_DIFF) |> Q.ISPECL [`member_leaves (PROB,S') DELETE vs`, `member_leaves
             (prob_proj
                (PROB,
                 FDOM PROB.I DIFF
                 (vs ∪ BIGUNION (single_child_ancestors PROB vs))),S')`])))
THEN SRW_TAC[][]
THEN Q.PAT_ASSUM `vs INSERT S'' = member_leaves (PROB,S')` (ASSUME_TAC o GSYM)
THEN FULL_SIMP_TAC(bool_ss)[DELETE_INSERT]);

val scc_main_lemma_1_1_1_1_1_1 = store_thm("scc_main_lemma_1_1_1_1_1_1",
``!PROB v1 v2. planning_problem(PROB) /\ dep(PROB, v1, v2)
               ==> (v1 IN FDOM(PROB.I) /\ v2 IN FDOM(PROB.I))``,
SRW_TAC[][planning_problem_def, dep_def]
THEN METIS_TAC[SUBSET_DEF])

val scc_main_lemma_1_1_1_1_1 = store_thm("scc_main_lemma_1_1_1_1_1",
``!PROB v1 v2. planning_problem(PROB) /\ dep_tc PROB v1 v2
               ==> v1 IN FDOM (PROB.I)``,
SRW_TAC[][dep_tc_def]
THEN MP_TAC(TC_CASES1 |> Q.SPECL[`(λv1' v2'. dep (PROB,v1',v2'))`, `v1`, `v2`])
THEN SRW_TAC[][]
THEN METIS_TAC[scc_main_lemma_1_1_1_1_1_1])

val scc_main_lemma_1_1_1_1 = store_thm("scc_main_lemma_1_1_1_1",
``!PROB vs. planning_problem(PROB) /\ scc_vs(PROB, vs) ==> vs SUBSET FDOM(PROB.I)``,
SRW_TAC[][scc_vs_def, SCC_def]
THEN REWRITE_TAC[SUBSET_DEF]
THEN METIS_TAC[scc_main_lemma_1_1_1_1_1, dep_tc_def])


val scc_main_lemma_1_1_1_2 = store_thm("scc_main_lemma_1_1_1_2",
``!PROB vs vs'. ~(DISJOINT vs vs') /\ scc_vs(PROB, vs) /\ scc_vs(PROB, vs') ==> (vs = vs')``,
METIS_TAC[scc_disjoint_lemma, scc_vs_def])

val scc_main_lemma_1_1_1 = store_thm("scc_main_lemma_1_1_1",
``!PROB S vs. planning_problem(PROB) /\ FDOM(PROB.I) SUBSET BIGUNION S /\ scc_set(PROB, S) /\ scc_vs(PROB, vs)
              ==> vs IN S``,
SRW_TAC[][]
THEN `!v. v IN vs ==> ( vs IN S' (* /\ v IN vs' /\ scc_vs(PROB, vs') /\ (vs' = vs)*))` by 
     (`vs SUBSET BIGUNION S'` by METIS_TAC[scc_main_lemma_1_1_1_1, SUBSET_TRANS]
      THEN SRW_TAC[][]
      THEN `∃vs'. vs' ∈ S' ∧ v ∈ vs'` by METIS_TAC[IN_BIGUNION, SUBSET_DEF]
      THEN FULL_SIMP_TAC(bool_ss)[scc_set_def]
      THEN FIRST_X_ASSUM (MP_TAC o Q.SPEC `vs' : 'a -> bool`)
      THEN SRW_TAC[][DISJOINT_DEF]
      THEN MP_TAC(scc_main_lemma_1_1_1_1 |> Q.SPECL[`PROB`, `vs`])
      THEN SRW_TAC[][SUBSET_DEF]
      THEN FULL_SIMP_TAC(srw_ss())[INTER_DEF, SUBSET_DEF, GSPEC_ETA, GSYM MEMBER_NOT_EMPTY]
      THEN `scc_vs(PROB, vs')` by METIS_TAC[]
      THEN `~(DISJOINT vs vs')` by (SRW_TAC[][DISJOINT_DEF,INTER_DEF, GSPEC_ETA, GSYM MEMBER_NOT_EMPTY]
                                  THEN Q.EXISTS_TAC `v` THEN SRW_TAC[][])
      THEN METIS_TAC[scc_main_lemma_1_1_1_2])
THEN FULL_SIMP_TAC(srw_ss())[scc_vs_def, SCC_def |> Q.SPECL [`(λv1' v2'. dep (PROB,v1',v2'))`, `vs`]]
THEN METIS_TAC[MEMBER_NOT_EMPTY]);
 
val scc_main_lemma_1_1 = store_thm("scc_main_lemma_1_1",
``!PROB S. planning_problem(PROB) /\ FDOM PROB.I SUBSET BIGUNION S /\ scc_set(PROB, S)
           ==> (childless_problem_scc_set(PROB) = member_leaves(PROB, S))``,
SRW_TAC[][childless_problem_scc_set_def, member_leaves_def, EXTENSION]
THEN EQ_TAC
THEN SRW_TAC[][]
THEN METIS_TAC[scc_main_lemma_1_1_1])

val scc_main_lemma_1_2_1 = store_thm("scc_main_lemma_1_2_1",
``!PROB. planning_problem(PROB) ==> ((FDOM PROB.I = EMPTY) ==> (!vs. ~scc_vs(PROB, vs)))``,
SRW_TAC[][]
THEN SPOSE_NOT_THEN STRIP_ASSUME_TAC
THEN FULL_SIMP_TAC(bool_ss)[GSYM MEMBER_NOT_EMPTY, scc_vs_def, SCC_def]
THEN `(λv1' v2'. dep (PROB,v1',v2'))⁺ x x ∧
 (λv1' v2'. dep (PROB,v1',v2'))⁺ x x` by SRW_TAC[][]
THEN MP_TAC(scc_main_lemma_1_1_1_1_1 |> Q.SPECL [`PROB`, `x`, `x`])
THEN SRW_TAC[][dep_tc_def])


val scc_main_lemma_1_2_2_1 = store_thm("scc_main_lemma_1_2_2_1",
``!PROB. StrongOrder(REL_RESTRICT (\vs1 vs2. dep_var_set(PROB, vs2, vs1))^+ (problem_scc_set(PROB)))``,
cheat)

val scc_main_lemma_1_2_2_2 = store_thm("scc_main_lemma_1_2_2_2",
``!PROB. FINITE (problem_scc_set(PROB))``,
cheat)

val scc_main_lemma_1_2_2_3 = store_thm("scc_main_lemma_1_2_2_3",
``!PROB. ~(FDOM(PROB.I) = EMPTY) /\ planning_problem(PROB) ==> ?vs. scc_vs(PROB, vs)``,
cheat)

val scc_main_lemma_1_2_2_4 = store_thm("scc_main_lemma_1_2_2_4",
``!R s min. (!x. REL_RESTRICT (R^+) s x min ==> ~(x IN s))
            ==> !x'. x' IN s ==> ~(R x' min)``,
(* WF_TC_EQN *)
cheat)


val scc_main_lemma_1_2_2 = store_thm("scc_main_lemma_1_2_2",
``!PROB. planning_problem(PROB) /\ ~(FDOM(PROB.I) = EMPTY) ==> ?vs. scc_vs(PROB, vs) /\ childless_vs(PROB, vs)``,
(* SRW_TAC[][]
THEN MP_TAC(scc_main_lemma_1_2_2_1 |> Q.SPEC `PROB`)
THEN SRW_TAC[][]
THEN MP_TAC(scc_main_lemma_1_2_2_2 |> Q.SPEC `PROB`)
THEN SRW_TAC[][]
THEN MP_TAC(FINITE_StrongOrder_WF |> Q.ISPEC `(\vs1 vs2. dep_var_set(PROB, vs2, vs1))^+`|> Q.SPEC  `(problem_scc_set(PROB))`)
THEN SRW_TAC[][]
THEN MP_TAC(scc_main_lemma_1_2_2_3 |> Q.SPEC `PROB`)
THEN SRW_TAC[][]
THEN FULL_SIMP_TAC(srw_ss())[(WF_DEF |> Q.ISPEC `(REL_RESTRICT (\vs1 vs2. dep_var_set(PROB, vs2, vs1))^+ (problem_scc_set(PROB)))`)]
THEN `(∃w: ('a -> bool). {vs' | scc_vs (PROB,vs')} w)` by (Q.EXISTS_TAC `vs` THEN SRW_TAC[][GSPEC_ETA])
THEN Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `{vs' | scc_vs(PROB, vs')}`)
THEN SRW_TAC[][]
THEN `∃min.
        {vs' | scc_vs (PROB,vs')} min ∧
        ∀b.
          REL_RESTRICT (λvs1 vs2. dep_var_set (PROB,vs2,vs1))⁺
            (problem_scc_set PROB) b min ⇒
          ¬{vs' | scc_vs (PROB,vs')} b` by METIS_TAC[]
THEN FULL_SIMP_TAC(srw_ss()) [GSYM problem_scc_set_def]
THEN MP_TAC(scc_main_lemma_1_2_2_4 |> Q.ISPEC `(λvs1 vs2. dep_var_set (PROB,vs2,vs1))` |> Q.SPEC `problem_scc_set(PROB)`|> Q.SPEC  `min`)
THEN SRW_TAC[][IN_DEF] *)
cheat)


val scc_main_lemma_1_2 = store_thm("scc_main_lemma_1_2",
``!PROB. planning_problem(PROB) ==> ((FDOM PROB.I = EMPTY) = (childless_problem_scc_set(PROB) = EMPTY))``,
SRW_TAC[][]
THEN EQ_TAC
THENL
[
   SRW_TAC[][]
   THEN REWRITE_TAC[IN_DEF, EXTENSION,childless_problem_scc_set_def]
   THEN SRW_TAC[][GSPEC_ETA]
   THEN METIS_TAC[scc_main_lemma_1_2_1]
   ,
   FULL_SIMP_TAC(bool_ss)[childless_problem_scc_set_def, EXTENSION, GSPEC_ETA, EMPTY_DEF]
   THEN SRW_TAC[][]
   THEN SPOSE_NOT_THEN STRIP_ASSUME_TAC
   THEN METIS_TAC[scc_main_lemma_1_2_2, MEMBER_NOT_EMPTY]
])

val scc_main_lemma_1_3 = store_thm("scc_main_lemma_1_3",
``!PROB S S'. scc_set(PROB, S) /\ S' SUBSET S ==> scc_set(prob_proj(PROB, FDOM(PROB.I) DIFF BIGUNION S'), S)``,
cheat)

val scc_main_lemma_1_4 = store_thm("scc_main_lemma_1_4",
``!PROB vs S. scc_set(PROB, S) /\ scc_vs(PROB, vs) /\ FDOM(PROB.I) SUBSET BIGUNION S 
              ==> single_child_ancestors PROB vs SUBSET S``,
cheat)

val scc_main_lemma_1_5 = store_thm("scc_main_lemma_1_5",
``!PROB vs vs'. FDOM(PROB.I) SUBSET vs ==> FDOM((prob_proj(PROB, vs')).I) SUBSET vs``,
cheat)


val scc_main_lemma_1_6 = store_thm("scc_main_lemma_1_6",
``!PROB vs S S'. (member_leaves (PROB,S) = vs INSERT S') /\ ~(vs IN S')
              ==> (sum_scc_parents(problem_wo_vs_ancestors(PROB, vs)
                           , member_leaves(problem_wo_vs_ancestors(PROB, vs), S)) = sum_scc_parents(PROB, S'))``,
cheat)

val scc_main_lemma_1_7 = store_thm("scc_main_lemma_1_7",
``!PROB vs. childless_vs(PROB, vs) /\ scc_vs(PROB, vs)
            ==> problem_plan_bound(PROB)
                   <= problem_plan_bound(problem_wo_vs_ancestors(PROB, vs))
                           + problem_plan_bound(prob_proj(PROB, vs UNION (ancestors (PROB,vs))))``,
cheat)



val scc_main_lemma_1 = store_thm("scc_main_lemma_1",
``∀s. FINITE s ⇒  
      ∀S PROB.
       planning_problem PROB ∧ scc_set (PROB,S) ∧
       FDOM PROB.I ⊆ BIGUNION S ∧ (S ≠ ∅ ∧ S ≠ {∅}) ∧ FINITE S ∧
       (s = member_leaves (PROB,S)) ⇒
       problem_plan_bound PROB ≤
       sum_scc_parents (PROB,member_leaves (PROB,S))``,
MATCH_MP_TAC(simpLib.ASM_SIMP_RULE (srw_ss()) [AND_IMP_INTRO]  (FINITE_INDUCT 
   |> INST_TYPE [alpha |-> ``:'a -> bool``] 
   |> Q.SPEC `(\s. !S PROB. planning_problem PROB ∧ scc_set (PROB,S) 
                   ∧ FDOM PROB.I ⊆ BIGUNION S ∧ (BIGUNION S ≠ ∅ ) ∧ FINITE S 
                   /\ (s = member_leaves(PROB, S)) 
                   ==> problem_plan_bound PROB ≤ sum_scc_parents (PROB,s))`))
THEN SRW_TAC[][]
THENL
[
   Q.PAT_ASSUM `EMPTY = x` (ASSUME_TAC o GSYM)
   THEN SRW_TAC[][]
   THEN MP_TAC(scc_main_lemma_1_1 |> Q.SPECL [`PROB`,`S'`])
   THEN SRW_TAC[][]
   THEN MP_TAC(scc_main_lemma_1_2 |> Q.SPEC `PROB`)
   THEN SRW_TAC[][sum_scc_parents_def, SUM_IMAGE_THM]
   THEN MP_TAC(bound_main_lemma |> Q.SPEC `PROB`)
   THEN SRW_TAC[][]
   ,
   Q.PAT_ASSUM `a INSERT b= x` (ASSUME_TAC o GSYM)
   THEN SRW_TAC[][]
   THEN MP_TAC(scc_lemma_1_2 |> Q.SPECL [`PROB`, `e`, `S'`])
   THEN SRW_TAC[][]
   THEN MP_TAC(scc_main_lemma_1_4 |> Q.SPECL [`PROB`, `e`, `S'`])
   THEN SRW_TAC[][]
   THEN MP_TAC(scc_main_lemma_1_5 |> Q.SPEC `PROB` |> Q.SPEC `BIGUNION S'` |> Q.ISPEC `FDOM(PROB.I) DIFF (e UNION BIGUNION (single_child_ancestors PROB e))`)
   THEN SRW_TAC[][]
   THEN MP_TAC(scc_lemma_1_3 |> Q.SPECL[`PROB`, `e`, `S'`])
   THEN SRW_TAC[][]
   THEN MP_TAC(scc_main_lemma_1_3 |> INST_TYPE[alpha |-> ``:'a`` ] |> Q.SPECL [`PROB`, `S'`, `((e :α -> bool) INSERT (single_child_ancestors PROB e ))`])
   THEN SRW_TAC[][]
   THEN Q.PAT_ASSUM `!x y. p x y` (Q.SPECL_THEN [`S'`,`(problem_wo_vs_ancestors(PROB, e))`] MP_TAC)
   THEN SRW_TAC[][graph_plan_lemma_2_2, scc_lemma_1_4, problem_wo_vs_ancestors_def]
   THEN FULL_SIMP_TAC(srw_ss())[GSYM problem_wo_vs_ancestors_def]
   THEN MP_TAC(scc_main_lemma_1_6 |> Q.SPECL [`PROB`, `e`,`S'`,`s`])
   THEN SRW_TAC[][]
   THEN FULL_SIMP_TAC(bool_ss)[]
   THEN SRW_TAC[][sum_scc_parents_def, SUM_IMAGE_THM]
   THEN FULL_SIMP_TAC(bool_ss)[DELETE_NON_ELEMENT]
   THEN MP_TAC( scc_lemma_1_5 |> Q.SPECL [`PROB`,`e`,`S'`])
   THEN SRW_TAC[][]
   THEN MP_TAC(scc_main_lemma_1_7 |> Q.SPECL [`PROB`, `e`])
   THEN SRW_TAC[][]
   THEN FULL_SIMP_TAC(bool_ss)[((sum_scc_parents_def) |> Q.SPECL [`PROB`, `s`])]
   THEN DECIDE_TAC])

val scc_main_lemma = store_thm("scc_main_lemma",
``!S PROB. planning_problem(PROB) /\ scc_set(PROB, S) /\ FDOM PROB.I SUBSET BIGUNION S /\ ~(BIGUNION S = EMPTY)
           /\ FINITE(S)
           ==>  problem_plan_bound(PROB) <= sum_scc_parents(PROB, (member_leaves(PROB, S)))``,
NTAC 2 STRIP_TAC 
THEN MP_TAC(scc_lemma_1_1 |> Q.SPECL [`PROB`, `S'`])
THEN SRW_TAC[][]
THEN FULL_SIMP_TAC(srw_ss())[]
THEN METIS_TAC [scc_main_lemma_1]
(*
THEN   Q.UNDISCH_TAC `FINITE (member_leaves (PROB,S'))`
   THEN Q.UNDISCH_TAC `planning_problem PROB`
   THEN Q.UNDISCH_TAC `scc_set (PROB,S')`
   THEN Q.UNDISCH_TAC `FDOM PROB.I ⊆ BIGUNION S'`
   THEN Q.UNDISCH_TAC `S' ≠ ∅`
   THEN Q.UNDISCH_TAC `S' ≠ {∅}`
   THEN Q.UNDISCH_TAC `FINITE S'`
THEN REWRITE_TAC[AND_IMP_INTRO, GSYM CONJ_ASSOC]
THEN Q.SPEC_TAC(`S'`, `S'`)
THEN Q.SPEC_TAC(`PROB`, `PROB`)
THEN MATCH_MP_TAC(simpLib.ASM_SIMP_RULE (bool_ss) [AND_IMP_INTRO]((CONV_RULE RIGHT_IMP_FORALL_CONV) (simpLib.ASM_SIMP_RULE (srw_ss()) [AND_IMP_INTRO] (GSYM(FINITE_INDUCT 
   |> INST_TYPE [alpha |-> ``:'a -> bool``] 
   |> Q.SPEC `(\s. !S PROB. planning_problem PROB ∧ scc_set (PROB,S) 
                   ∧ FDOM PROB.I ⊆ BIGUNION S ∧ (BIGUNION S ≠ ∅ ) ∧ FINITE S 
                   /\ (s = member_leaves(PROB, S)) 
                   ==> problem_plan_bound PROB ≤ sum_scc_parents (PROB,s))`))))) *)
);


val _ = export_theory();