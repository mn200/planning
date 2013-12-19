
open HolKernel Parse boolLib bossLib;
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
val _ = new_theory "SCCGraphPlanTheorem";


val dep_tc_def = Define `dep_tc (PROB)   =  TC (\v1' v2'. dep(PROB, v1', v2'))`;

val ancestors_def = Define
 `ancestors(PROB: 'a problem, vs: ('a -> bool)) = 
    {v: 'a | (?v': 'a. v' IN vs /\ ((dep_tc(PROB)) v v') ) /\ (!v': 'a. v' IN vs ==> ~((dep_tc(PROB)) v' v))}`;

val dep_var_set_relaxed_def = Define
  `dep_var_set_relaxed (PROB, vs1, vs2)
          <=> ? v1 v2. (v1 IN vs1) /\ (v2 IN vs2) /\ dep(PROB, v1, v2)`;

val scc_def = Define 
`scc(PROB, vs) 
    = (!v1 v2. v1 IN vs /\ v2 IN vs ==> ((dep_tc(PROB)) v1 v2) /\ ((dep_tc(PROB)) v2 v1))
          /\ (!vs'. ~(vs'= vs) ==> ~(dep_var_set_relaxed(PROB, vs, vs')) \/ ~(dep_var_set_relaxed(PROB, vs', vs)))
          /\ ~(vs = EMPTY) /\ (!v. v IN vs ==> ?v'. v' IN vs /\ dep(PROB, v, v'))`;
 

val scc_set_def = Define
`scc_set(PROB, S) = !vs. vs IN S /\ ~(DISJOINT vs (FDOM(PROB.I))) ==> scc(PROB, vs)`;


val sum_scc_parents_def 
  = Define` sum_scc_parents(PROB, S) 
     = SIGMA (\vs. problem_plan_bound((prob_proj(PROB, vs UNION (ancestors(PROB, vs)))))) S + 1`;

val childless_vs_def = Define`
      childless_vs(PROB, vs) = !vs'. DISJOINT vs vs' ==> ~(dep_var_set(PROB, vs, vs'))`


val childless_svs_def = Define`
      childless_svs(PROB, S) = !vs. vs IN S ==> (childless_vs(PROB, vs))`;


val childless_problem_scc_set_def = Define`
      childless_problem_scc_set(PROB) = {vs | (scc(PROB, vs)) /\ (childless_vs(PROB, vs))}`;

val single_child_parents_def = Define
`single_child_parents(PROB, vs) 
           = {vs' | vs' SUBSET (ancestors(PROB, vs)) 
                       /\ childless_vs(prob_proj(PROB, (FDOM PROB.I) DIFF vs), vs') 
                            /\scc(PROB, vs')}`;

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


val member_leaves_def = Define
     `member_leaves(PROB, S) 
           =  (\vs. (scc(PROB, vs) /\ childless_vs(PROB, vs))) INTER S`;

val problem_wo_vs_ancestors_def = Define
  `problem_wo_vs_ancestors(PROB, vs) = 
              prob_proj(PROB, FDOM PROB.I DIFF (vs ∪ BIGUNION (single_child_ancestors (PROB,vs))))`;

val scc_lemma_1_1 = store_thm("scc_lemma_1_1",
``!PROB S. FINITE(S) ==> FINITE((member_leaves(PROB, S)))``,
SRW_TAC[][member_leaves_def]
THEN METIS_TAC[FINITE_INTER]);

val scc_lemma_1_2 = store_thm("scc_lemma_1_2",
``!PROB vs S. vs IN member_leaves(PROB, S) ==> scc(PROB, vs)``,
SRW_TAC[][member_leaves_def]);

val scc_lemma_1_3 = store_thm("scc_lemma_1_3",
``!PROB vs S. vs IN member_leaves(PROB, S) ==> vs IN S``,
SRW_TAC[][member_leaves_def]);



val scc_lemma_1_4 = store_thm("scc_lemma_1_4",
``!S. FINITE S ==> (!PROB vs S'. (member_leaves(PROB, S) = vs INSERT S')
                 ==> (member_leaves(problem_wo_vs_ancestors(PROB, vs), S) = S'))``,
cheat
 (*DB.fetch "-" "single_child_ancestors_ind"
 SRW_TAC[][problem_wo_vs_ancestors_def]
 HO_MATCH_MP_TAC FINITE_INDUCT
 THEN SRW_TAC[][]
 THENL
 [
    ,
    FULL_SIMP_TAC(srw_ss())[member_leaves_def, INTER_DEF]
 ]*));

val scc_lemma_1_5 = store_thm("scc_lemma_1_5",
``!PROB vs S. vs IN member_leaves(PROB, S) ==> childless_vs(PROB, vs)``,
SRW_TAC[][member_leaves_def]);

val scc_main_lemma_1_1_1_1_1_1 = store_thm("scc_main_lemma_1_1_1_1_1_1",
``!PROB v1 v2. planning_problem(PROB) /\ dep(PROB, v1, v2)
               ==> (v1 IN FDOM(PROB.I) /\ v1 IN FDOM(PROB.I))``,
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
``!PROB vs. planning_problem(PROB) /\ scc(PROB, vs) ==> vs SUBSET FDOM(PROB.I)``,
SRW_TAC[][scc_def]
THEN REWRITE_TAC[SUBSET_DEF]
THEN METIS_TAC[scc_main_lemma_1_1_1_1_1])



val scc_main_lemma_1_1_1_2_1 = store_thm("scc_main_lemma_1_1_1_2_1",
``!s t x. x IN s /\ ~(x IN t) ==> ~(s = t)``,
METIS_TAC[])
 
val scc_main_lemma_1_1_1_2_2 = store_thm("scc_main_lemma_1_1_1_2_2",
``!PROB vs vs'. scc(PROB, vs) /\ scc(PROB, vs') /\ ~(vs = vs') ==> DISJOINT vs vs'``,
SRW_TAC[][] 
THEN SPOSE_NOT_THEN STRIP_ASSUME_TAC
THEN FULL_SIMP_TAC(srw_ss()) [DISJOINT_DEF, INTER_DEF, GSPEC_ETA, GSYM MEMBER_NOT_EMPTY]
THEN FULL_SIMP_TAC(bool_ss)[scc_def]
THEN Q.PAT_ASSUM `∀vs''.
        vs'' ≠ vs' ⇒
        ¬dep_var_set_relaxed (PROB,vs',vs'') ∨ ¬dep_var_set_relaxed (PROB,vs'',vs')` (MP_TAC o Q.SPEC `vs`)
THEN SRW_TAC[][]
THEN SRW_TAC[][dep_var_set_relaxed_def]
THEN METIS_TAC[])


val scc_main_lemma_1_1_1_2 = store_thm("scc_main_lemma_1_1_1_2",
``!PROB vs vs'. ~(DISJOINT vs vs') /\ scc(PROB, vs) /\ scc(PROB, vs') ==> (vs = vs')``,
METIS_TAC[scc_main_lemma_1_1_1_2_2])

val scc_main_lemma_1_1_1 = store_thm("scc_main_lemma_1_1_1",
``!PROB S vs. planning_problem(PROB) /\ FDOM(PROB.I) SUBSET BIGUNION S /\ scc_set(PROB, S) /\ scc(PROB, vs)
              ==> vs IN S``,
SRW_TAC[][]
THEN `!v. v IN vs ==> ( vs IN S' (* /\ v IN vs' /\ scc(PROB, vs') /\ (vs' = vs)*))` by 
     (`vs SUBSET BIGUNION S'` by METIS_TAC[scc_main_lemma_1_1_1_1, SUBSET_TRANS]
      THEN SRW_TAC[][]
      THEN `∃vs'. vs' ∈ S' ∧ v ∈ vs'` by METIS_TAC[IN_BIGUNION, SUBSET_DEF]
      THEN FULL_SIMP_TAC(bool_ss)[scc_set_def]
      THEN FIRST_X_ASSUM (MP_TAC o Q.SPEC `vs' : 'a -> bool`)
      THEN SRW_TAC[][DISJOINT_DEF]
      THEN MP_TAC(scc_main_lemma_1_1_1_1 |> Q.SPECL[`PROB`, `vs`])
      THEN SRW_TAC[][SUBSET_DEF]
      THEN FULL_SIMP_TAC(srw_ss())[INTER_DEF, SUBSET_DEF, GSPEC_ETA, GSYM MEMBER_NOT_EMPTY]
      THEN `scc(PROB, vs')` by METIS_TAC[]
      THEN `~(DISJOINT vs vs')` by (SRW_TAC[][DISJOINT_DEF,INTER_DEF, GSPEC_ETA, GSYM MEMBER_NOT_EMPTY]
                                  THEN Q.EXISTS_TAC `v` THEN SRW_TAC[][])
      THEN METIS_TAC[scc_main_lemma_1_1_1_2])
THEN METIS_TAC[MEMBER_NOT_EMPTY, scc_def]);
 
val scc_main_lemma_1_1 = store_thm("scc_main_lemma_1_1",
``!PROB S. planning_problem(PROB) /\ FDOM PROB.I SUBSET BIGUNION S /\ scc_set(PROB, S)
           ==> (childless_problem_scc_set(PROB) = member_leaves(PROB, S))``,
SRW_TAC[][childless_problem_scc_set_def, member_leaves_def, EXTENSION]
THEN EQ_TAC
THEN SRW_TAC[][]
THEN METIS_TAC[scc_main_lemma_1_1_1])

val scc_main_lemma_1_2 = store_thm("scc_main_lemma_1_2",
``!PROB. ((FDOM PROB.I = EMPTY) = (childless_problem_scc_set(PROB) = EMPTY))``,
cheat)

val scc_main_lemma_1_3 = store_thm("scc_main_lemma_1_3",
``!PROB S S'. scc_set(PROB, S) /\ S' SUBSET S ==> scc_set(prob_proj(PROB, FDOM(PROB.I) DIFF BIGUNION S'), S)``,
cheat)

val scc_main_lemma_1_4 = store_thm("scc_main_lemma_1_4",
``!PROB vs S. scc_set(PROB, S) /\ scc(PROB, vs) /\ FDOM(PROB.I) SUBSET BIGUNION S ==> single_child_ancestors(PROB, vs) SUBSET S``,
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
``!PROB vs. childless_vs(PROB, vs) /\ scc(PROB, vs)
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
   THEN MP_TAC(scc_main_lemma_1_5 |> Q.SPEC `PROB` |> Q.SPEC `BIGUNION S'` |> Q.ISPEC `FDOM(PROB.I) DIFF (e UNION BIGUNION (single_child_ancestors (PROB,e)))`)
   THEN SRW_TAC[][]
   THEN MP_TAC(scc_lemma_1_3 |> Q.SPECL[`PROB`, `e`, `S'`])
   THEN SRW_TAC[][]
   THEN MP_TAC(scc_main_lemma_1_3 |> INST_TYPE[alpha |-> ``:'a`` ] |> Q.SPECL [`PROB`, `S'`, `((e :α -> bool) INSERT (single_child_ancestors (PROB,e)))`])
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