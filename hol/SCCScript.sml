open HolKernel Parse boolLib bossLib;
(*open HolKernel Parse boolLib QLib tautLib mesonLib metisLib
     simpLib boolSimps BasicProvers; *)
open pred_setTheory;
open relationTheory;
val _ = new_theory "SCC";


val SCC_def = Define`SCC R vs <=> (!v v'. v IN vs /\ v' IN vs ==> R^+ v v' /\ R^+ v' v)
                                  /\ (!v v'. v IN vs /\ ~(v' IN vs) ==> ~(R^+ v v') \/ ~(R^+ v' v))
                                  (*/\ ?v v'. ~(v = v') /\ v IN vs /\ v' IN vs*)
                                  /\ ~(vs = {})`

(* A function to lift a relation ('a -> 'a -> bool) to (('a -> bool) -> ('a -> bool) -> bool), i.e
yeilds a relation between sets of objects. *)
val lift_def = Define`lift R vs vs' <=> ?v v'. v IN vs /\ v' IN vs' ==> R v v'`


val scc_disjoint_lemma = store_thm("scc_disjoint_lemma",
``!R vs vs'. SCC R vs /\ SCC R vs' /\ ~(vs = vs') ==> DISJOINT vs vs'``,
SRW_TAC[][] 
THEN SPOSE_NOT_THEN STRIP_ASSUME_TAC
THEN FULL_SIMP_TAC(srw_ss()) [DISJOINT_DEF, INTER_DEF, GSPEC_ETA, GSYM MEMBER_NOT_EMPTY]
THEN FULL_SIMP_TAC(bool_ss)[SCC_def]
THEN `?v. v IN vs /\ ~(v IN vs')` by (FULL_SIMP_TAC(bool_ss)[EXTENSION, IN_DEF] THEN METIS_TAC[])
THEN METIS_TAC[])





val scc_lemma_x = store_thm("scc_lemma_x",
  ``!R x z. (R x z \/ ?y:'a. R x y /\ TC R y z) ==> TC R x z ``,
SRW_TAC[][]
THEN1 METIS_TAC[MATCH_MP AND1_THM (TC_RULES |> Q.SPEC `R`)]
THEN METIS_TAC[(REWRITE_RULE[transitive_def] TC_TRANSITIVE) |> Q.SPEC `R`, 
               MATCH_MP AND1_THM (TC_RULES |> Q.SPEC `R`)]);

val TC_CASES1_RW = store_thm("TC_CASES1_RW",
``!R x z. (R x z \/ ?y:'a. R x y /\ TC R y z) <=> TC R x z ``,
mesonLib.MESON_TAC[TC_CASES1, scc_lemma_x])





val scc_lemma_xx = store_thm("scc_lemma_xx",
``!R R' P P'. (!x y. P x /\ P' y ==> (R x y ==> R' x y) /\ ((\x y. R x y /\ P x /\ P' y)^+ x y)) 
              ==> (!x y. P x /\ P' y ==> (R'^+ x y))``,
REWRITE_TAC[TC_DEF]
THEN REPEAT STRIP_TAC
THEN LAST_ASSUM (MP_TAC o Q.SPECL[`x`, `y`])
THEN REPEAT STRIP_TAC
THEN `(R x y ⇒ R' x y) ∧
      ∀P''.
        (∀x y. (λx y. R x y ∧ P x ∧ P' y) x y ⇒ P'' x y) ∧
        (∀x y z. P'' x y ∧ P'' y z ⇒ P'' x z) ⇒
        P'' x y` by METIS_TAC[]
THEN FIRST_X_ASSUM (MP_TAC o Q.SPEC `P''`)
THEN REPEAT STRIP_TAC
THEN METIS_TAC[])


val scc_lemma_xxx = store_thm("scc_lemma_xxx",
  ``!R x z. (R x z \/ ?y:'a. R^+ x y /\ R y z) ==> TC R x z ``,
SRW_TAC[][]
THEN1 METIS_TAC[MATCH_MP AND1_THM (TC_RULES |> Q.SPEC `R`)]
THEN METIS_TAC[(REWRITE_RULE[transitive_def] TC_TRANSITIVE) |> Q.SPEC `R`, 
               MATCH_MP AND1_THM (TC_RULES |> Q.SPEC `R`)]);

val TC_CASES2_RW = store_thm("TC_CASES2_RW",
``!R x z. (R x z \/ ?y:'a. R^+ x y /\ R y z) <=> TC R x z ``,
mesonLib.MESON_TAC[TC_CASES2, scc_lemma_xxx])



val scc_lemma_1_4_2_1_1_1_3_2_1_1 = store_thm("scc_lemma_1_4_2_1_1_1_3_2_1_1",
``!R P x y. ~R^+ x y
            ==> ~(\x y. R x y /\ P x y) ^+ x y``,
REWRITE_TAC[TC_DEF]
THEN SRW_TAC[][]
THEN Q.EXISTS_TAC `P'`
THEN SRW_TAC[][]
THEN METIS_TAC[])


val scc_lemma_1_4_2_1_1_1_3_2_1 = store_thm("scc_lemma_1_4_2_1_1_1_3_2_1",
``!R R' P x y. ((!x y. P x  y ==> R' x y ==> R x y)                  
               /\ ~R^+ x y )
              ==>  ~((\x y. R' x y /\ P x y)^+ x y)``,
SRW_TAC[][]
THEN `¬(λx y. R x y /\ P x  y)⁺ x y` 
   by METIS_TAC[ scc_lemma_1_4_2_1_1_1_3_2_1_1 |> Q.SPECL [`R`, `(\x y. P x y)`, `x`, `y`]]
THEN FULL_SIMP_TAC(srw_ss())[TC_DEF]
THEN Q.EXISTS_TAC `P'`
THEN SRW_TAC[][]
THEN METIS_TAC[])


val scc_lemma_1_4_1_1_2_1_3 = store_thm("scc_lemma_1_4_1_1_2_1_3",
``!R R' P. (!x y. P x /\ P y ==> (R x y ==> R' x y) 
           /\ ((\x y. R x y /\ P x /\ P y)^+ x y)) 
              ==> (!x y. P x /\ P y ==> (R'^+ x y))``,
REWRITE_TAC[TC_DEF]
THEN REPEAT STRIP_TAC
THEN LAST_ASSUM (MP_TAC o Q.SPECL[`x`, `y`])
THEN REPEAT STRIP_TAC
THEN `(R x y ⇒ R' x y) ∧
        ∀P'.
          (∀x y. (λx y. R x y ∧ P x ∧ P y) x y ⇒ P' x y) ∧
          (∀x y z. P' x y ∧ P' y z ⇒ P' x z) ⇒
          P' x y` by METIS_TAC[]
THEN FIRST_X_ASSUM (MP_TAC o Q.SPEC `P'`)
THEN REPEAT STRIP_TAC
THEN METIS_TAC[])


val scc_lemma_1_4_2_1_1_1_3_2_2_1 = store_thm("scc_lemma_1_4_2_1_1_1_3_2_2_1",
``!R P x y. (\x y. R x y /\ P x y)^+ x y
            ==> R^+ x y``,
NTAC 2 STRIP_TAC
THEN HO_MATCH_MP_TAC TC_INDUCT
THEN SRW_TAC[][]
THEN1 SRW_TAC[][TC_RULES]
THEN PROVE_TAC[TC_RULES])


val cond_reflexive_def = Define `cond_reflexive P R = (!x. P x ==> R x x )`


val scc_lemma_1_4_2_1_1_1_3_2_2 = store_thm("scc_lemma_1_4_2_1_1_1_3_2_2",
``!R'. reflexive R' ==> (!P x y. (R'^+ x y) 
               ==> ( ((\x y. R' x y /\ P x /\ P y)^+ x y) \/ (?z. ~P z /\ R'^+ x z /\ R'^+ z y)))``,
NTAC 3 STRIP_TAC
THEN HO_MATCH_MP_TAC TC_INDUCT
THEN SRW_TAC[][]
THENL
[
   Cases_on `P y`
   THEN Cases_on `P x`
   THEN1 SRW_TAC[][TC_RULES]
   THEN1( `∃z. ¬P z ∧ R'⁺ x z ∧ R'⁺ z y` by
      (Q.EXISTS_TAC `x`
      THEN SRW_TAC[][]
      THEN1( FULL_SIMP_TAC(srw_ss())[reflexive_def]
      THEN SRW_TAC[][TC_RULES])
      THEN SRW_TAC[][TC_RULES])
      THEN METIS_TAC[])
   THEN(`∃z. ¬P z ∧ R'⁺ x z ∧ R'⁺ z y` by
      (Q.EXISTS_TAC `y`
      THEN SRW_TAC[][]
      THEN1 SRW_TAC[][TC_RULES]
      THEN FULL_SIMP_TAC(srw_ss())[reflexive_def]
      THEN SRW_TAC[][TC_RULES])
      THEN METIS_TAC[])
   ,
   PROVE_TAC[REWRITE_RULE[transitive_def] TC_TRANSITIVE]
   ,
   MP_TAC(scc_lemma_1_4_2_1_1_1_3_2_2_1 |> Q.SPECL[`R'`, `(\x y. P x /\ P y)`, `x`, `x'`])
   THEN SRW_TAC[][]
   THEN `R'⁺ x z` by METIS_TAC[(MATCH_MP AND2_THM (TC_RULES |> Q.SPEC `R'`) |> Q.SPECL [`x`, `y`, `z'`] )]
   THEN `∃z. ¬P z ∧ R'⁺ x z ∧ R'⁺ z z` by
      (Q.EXISTS_TAC `z`
      THEN SRW_TAC[][]
      THEN FULL_SIMP_TAC(srw_ss())[reflexive_def]
      THEN SRW_TAC[][TC_RULES])
   THEN METIS_TAC[]
   ,
   MP_TAC(scc_lemma_1_4_2_1_1_1_3_2_2_1 |> Q.SPECL[`R'`, `(\x y. P x /\ P y)`, `x'`, `y`])
   THEN SRW_TAC[][]
   THEN `R'⁺ z y` by METIS_TAC[(MATCH_MP AND2_THM (TC_RULES |> Q.SPEC `R'`) |> Q.SPECL [`z`, `x'`, `y`] )]
   THEN `∃z. ¬P z ∧ R'⁺ x z ∧ R'⁺ z z` by
      (Q.EXISTS_TAC `z`
      THEN SRW_TAC[][]
      THEN FULL_SIMP_TAC(srw_ss())[reflexive_def]
      THEN SRW_TAC[][TC_RULES])
   THEN METIS_TAC[]   
   ,
   `R'⁺ x z'` by METIS_TAC[(MATCH_MP AND2_THM (TC_RULES |> Q.SPEC `R'`))]
   THEN `∃z. ¬P z ∧ R'⁺ x z ∧ R'⁺ z z` by
      (Q.EXISTS_TAC `z'`
      THEN SRW_TAC[][]
      THEN FULL_SIMP_TAC(srw_ss())[reflexive_def]
      THEN SRW_TAC[][TC_RULES])
   THEN METIS_TAC[]         
])




val scc_lemma_1_4_2_1_1_1_3_2 = store_thm("scc_lemma_1_4_2_1_1_1_3_2",
``!R R' P x y. (reflexive R' 
               /\ (!x y. P x /\ P y ==> (R' x y ==> R x y))
               /\ (~R ^+ x y ))       
              ==> ( ~(R'^+ x y) \/ (?z. ~P z /\ R'^+ x z /\ R'^+ z y))``,
SRW_TAC[][]
THEN Cases_on `¬R'⁺ x y`
THEN1 METIS_TAC[]
THEN FULL_SIMP_TAC(srw_ss())[]
THEN MP_TAC(scc_lemma_1_4_2_1_1_1_3_2_1 |> Q.SPECL[`R`, `R'`, `(\x y. P x /\ P y)`,  `x` ,`y`] )
THEN SRW_TAC[][]
THEN MP_TAC(scc_lemma_1_4_2_1_1_1_3_2_2 |> Q.SPEC `R'`)
THEN SRW_TAC[][]
THEN FIRST_X_ASSUM  (MP_TAC o Q.SPECL[`P` , `x`, `y`])
THEN SRW_TAC[][])

val scc_tc_inclusion = store_thm("scc_tc_inclusion",
``!R vs v v'. v IN vs /\ v' IN vs/\ SCC R vs /\ reflexive R
              ==> (\v v'. R v v' /\ v IN vs /\ v' IN vs)^+ v v'``,
SRW_TAC[][SCC_def]
THEN LAST_X_ASSUM (MP_TAC o Q.SPECL[`v`, `v'`])
THEN SRW_TAC[][]
THEN MP_TAC(scc_lemma_1_4_2_1_1_1_3_2_2  |> Q.SPEC `R`)
THEN SRW_TAC[][]
THEN FIRST_X_ASSUM (MP_TAC o Q.SPECL[ `(\v. v IN vs)`, `v`, `v'`])
THEN SRW_TAC[][]
THEN METIS_TAC[REWRITE_RULE[transitive_def] (TC_TRANSITIVE |> Q.SPEC `R`)])




val TC_CASES1_NEQ =
store_thm
("TC_CASES1_NEQ",
  ``!R x z. TC R x z ==> R x z \/ ?y:'a. ~(x = y) /\ ~(y = z) /\ R x y /\ TC R y z``,
GEN_TAC
 THEN HO_MATCH_MP_TAC TC_INDUCT
 THEN mesonLib.MESON_TAC [REWRITE_RULE[transitive_def] TC_TRANSITIVE, TC_SUBSET]);

val TC_CASES2_NEQ =
store_thm
("TC_CASES2_NEQ",
  ``!R x z. TC R x z ==> R x z \/ ?y:'a. ~(x = y) /\ ~(y = z) /\ TC R x y /\ R y z``,
GEN_TAC
 THEN HO_MATCH_MP_TAC TC_INDUCT
 THEN METIS_TAC [(REWRITE_RULE[transitive_def] TC_TRANSITIVE) |> Q.SPEC `R`, TC_SUBSET |> Q.SPEC `R`]);


val SCC_loop_contradict = store_thm("SCC_loop_contradict",
``!R vs vs'. (lift R)^+ vs vs' /\ (lift R)^+ vs' vs
             ==> ~(SCC R vs) /\ ~(SCC R vs')``,
cheat)


val _ = export_theory();

