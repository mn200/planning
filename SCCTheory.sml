structure SCCTheory :> SCCTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading SCCTheory ... " else ()
  open Type Term Thm
  infixr -->

  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  (*  Parents *)
  local open listTheory
  in end;
  val _ = Theory.link_parents
          ("SCC",Arbnum.fromString "1389615417",Arbnum.fromString "175454")
          [("list",
           Arbnum.fromString "1380541561",
           Arbnum.fromString "111594")];
  val _ = Theory.incorporate_types "SCC" [];

  val idvector = 
    let fun ID(thy,oth) = {Thy = thy, Other = oth}
    in Vector.fromList
  [ID("min", "fun"), ID("min", "bool"), ID("bool", "!"), ID("bool", "/\\"),
   ID("min", "="), ID("min", "==>"), ID("bool", "?"),
   ID("pred_set", "DISJOINT"), ID("pred_set", "EMPTY"), ID("bool", "IN"),
   ID("SCC", "SCC"), ID("relation", "TC"), ID("bool", "\\/"),
   ID("SCC", "cond_reflexive"), ID("SCC", "lift"),
   ID("relation", "reflexive"), ID("bool", "~")]
  end;
  local open SharingTables
  in
  val tyvector = build_type_vector idvector
  [TYOP [1], TYV "'b", TYOP [0, 1, 0], TYOP [0, 2, 0], TYV "'a",
   TYOP [0, 4, 0], TYOP [0, 5, 3], TYOP [0, 4, 2], TYOP [0, 7, 6],
   TYOP [0, 4, 5], TYOP [0, 9, 0], TYOP [0, 5, 10], TYOP [0, 5, 0],
   TYOP [0, 9, 12], TYOP [0, 12, 0], TYOP [0, 10, 0], TYOP [0, 7, 0],
   TYOP [0, 16, 0], TYOP [0, 3, 0], TYOP [0, 0, 0], TYOP [0, 0, 19],
   TYOP [0, 5, 12], TYOP [0, 4, 12], TYOP [0, 1, 3], TYOP [0, 9, 9],
   TYOP [0, 21, 21], TYOP [0, 9, 21]]
  end
  val _ = Theory.incorporate_consts "SCC" tyvector
     [("lift", 8), ("cond_reflexive", 11), ("SCC", 13)];

  local open SharingTables
  in
  val tmvector = build_term_vector idvector tyvector
  [TMV("P", 5), TMV("P", 9), TMV("P'", 5), TMV("R", 9), TMV("R", 7),
   TMV("R'", 9), TMV("v", 4), TMV("v'", 4), TMV("v'", 1), TMV("vs", 5),
   TMV("vs'", 5), TMV("vs'", 2), TMV("x", 4), TMV("y", 4), TMV("z", 4),
   TMC(2, 12), TMC(2, 14), TMC(2, 15), TMC(2, 17), TMC(2, 18), TMC(3, 20),
   TMC(4, 9), TMC(4, 20), TMC(4, 21), TMC(5, 20), TMC(6, 12), TMC(6, 3),
   TMC(7, 21), TMC(8, 5), TMC(9, 22), TMC(9, 23), TMC(10, 13), TMC(11, 24),
   TMC(11, 25), TMC(12, 20), TMC(13, 11), TMC(14, 26), TMC(14, 8),
   TMC(15, 10), TMC(16, 19)]
  end
  local
  val DT = Thm.disk_thm val read = Term.read_raw tmvector
  in
  val op SCC_def =
    DT([],
       [read"(%17 (|%3. (%16 (|%9. ((%22 ((%31 $1) $0)) ((%20 (%15 (|%6. (%15 (|%7. ((%24 ((%20 ((%29 $1) $2)) ((%29 $0) $2))) ((%20 (((%32 $3) $1) $0)) (((%32 $3) $0) $1)))))))) ((%20 (%15 (|%6. (%15 (|%7. ((%24 ((%20 ((%29 $1) $2)) (%39 ((%29 $0) $2)))) ((%34 (%39 (((%32 $3) $1) $0))) (%39 (((%32 $3) $0) $1))))))))) (%39 ((%23 $0) %28)))))))))"])
  val op lift_def =
    DT([],
       [read"(%18 (|%4. (%16 (|%9. (%19 (|%11. ((%22 (((%37 $2) $1) $0)) (%25 (|%6. (%26 (|%8. ((%24 ((%20 ((%29 $1) $3)) ((%30 $0) $2))) (($4 $1) $0)))))))))))))"])
  val op cond_reflexive_def =
    DT([],
       [read"(%16 (|%0. (%17 (|%3. ((%22 ((%35 $1) $0)) (%15 (|%12. ((%24 ($2 $0)) (($1 $0) $0)))))))))"])
  val op scc_disjoint_lemma =
    DT(["DISK_THM"],
       [read"(%17 (|%3. (%16 (|%9. (%16 (|%10. ((%24 ((%20 ((%31 $2) $1)) ((%20 ((%31 $2) $0)) (%39 ((%23 $1) $0))))) ((%27 $1) $0))))))))"])
  val op scc_lemma_x =
    DT(["DISK_THM"],
       [read"(%17 (|%3. (%15 (|%12. (%15 (|%14. ((%24 ((%34 (($2 $1) $0)) (%25 (|%13. ((%20 (($3 $2) $0)) (((%32 $3) $0) $1)))))) (((%32 $2) $1) $0))))))))"])
  val op TC_CASES1_RW =
    DT(["DISK_THM"],
       [read"(%17 (|%3. (%15 (|%12. (%15 (|%14. ((%22 ((%34 (($2 $1) $0)) (%25 (|%13. ((%20 (($3 $2) $0)) (((%32 $3) $0) $1)))))) (((%32 $2) $1) $0))))))))"])
  val op scc_lemma_xx =
    DT(["DISK_THM"],
       [read"(%17 (|%3. (%17 (|%5. (%16 (|%0. (%16 (|%2. ((%24 (%15 (|%12. (%15 (|%13. ((%24 ((%20 ($3 $1)) ($2 $0))) ((%20 ((%24 (($5 $1) $0)) (($4 $1) $0))) (((%32 (|%12. (|%13. ((%20 (($7 $1) $0)) ((%20 ($5 $1)) ($4 $0)))))) $1) $0)))))))) (%15 (|%12. (%15 (|%13. ((%24 ((%20 ($3 $1)) ($2 $0))) (((%32 $4) $1) $0)))))))))))))))"])
  val op scc_lemma_xxx =
    DT(["DISK_THM"],
       [read"(%17 (|%3. (%15 (|%12. (%15 (|%14. ((%24 ((%34 (($2 $1) $0)) (%25 (|%13. ((%20 (((%32 $3) $2) $0)) (($3 $0) $1)))))) (((%32 $2) $1) $0))))))))"])
  val op TC_CASES2_RW =
    DT(["DISK_THM"],
       [read"(%17 (|%3. (%15 (|%12. (%15 (|%14. ((%22 ((%34 (($2 $1) $0)) (%25 (|%13. ((%20 (((%32 $3) $2) $0)) (($3 $0) $1)))))) (((%32 $2) $1) $0))))))))"])
  val op scc_lemma_1_4_2_1_1_1_3_2_1_1 =
    DT(["DISK_THM"],
       [read"(%17 (|%3. (%17 (|%1. (%15 (|%12. (%15 (|%13. ((%24 (%39 (((%32 $3) $1) $0))) (%39 (((%32 (|%12. (|%13. ((%20 (($5 $1) $0)) (($4 $1) $0))))) $1) $0)))))))))))"])
  val op scc_lemma_1_4_2_1_1_1_3_2_1 =
    DT(["DISK_THM"],
       [read"(%17 (|%3. (%17 (|%5. (%17 (|%1. (%15 (|%12. (%15 (|%13. ((%24 ((%20 (%15 (|%12. (%15 (|%13. ((%24 (($4 $1) $0)) ((%24 (($5 $1) $0)) (($6 $1) $0)))))))) (%39 (((%32 $4) $1) $0)))) (%39 (((%32 (|%12. (|%13. ((%20 (($5 $1) $0)) (($4 $1) $0))))) $1) $0)))))))))))))"])
  val op scc_lemma_1_4_1_1_2_1_3 =
    DT(["DISK_THM"],
       [read"(%17 (|%3. (%17 (|%5. (%16 (|%0. ((%24 (%15 (|%12. (%15 (|%13. ((%24 ((%20 ($2 $1)) ($2 $0))) ((%20 ((%24 (($4 $1) $0)) (($3 $1) $0))) (((%32 (|%12. (|%13. ((%20 (($6 $1) $0)) ((%20 ($4 $1)) ($4 $0)))))) $1) $0)))))))) (%15 (|%12. (%15 (|%13. ((%24 ((%20 ($2 $1)) ($2 $0))) (((%32 $3) $1) $0)))))))))))))"])
  val op scc_lemma_1_4_2_1_1_1_3_2_2_1 =
    DT(["DISK_THM"],
       [read"(%17 (|%3. (%17 (|%1. (%15 (|%12. (%15 (|%13. ((%24 (((%32 (|%12. (|%13. ((%20 (($5 $1) $0)) (($4 $1) $0))))) $1) $0)) (((%32 $3) $1) $0))))))))))"])
  val op scc_lemma_1_4_2_1_1_1_3_2_2 =
    DT(["DISK_THM"],
       [read"(%17 (|%5. ((%24 (%38 $0)) (%16 (|%0. (%15 (|%12. (%15 (|%13. ((%24 (((%32 $3) $1) $0)) ((%34 (((%32 (|%12. (|%13. ((%20 (($5 $1) $0)) ((%20 ($4 $1)) ($4 $0)))))) $1) $0)) (%25 (|%14. ((%20 (%39 ($3 $0))) ((%20 (((%32 $4) $2) $0)) (((%32 $4) $0) $1))))))))))))))))"])
  val op scc_lemma_1_4_2_1_1_1_3_2 =
    DT(["DISK_THM"],
       [read"(%17 (|%3. (%17 (|%5. (%16 (|%0. (%15 (|%12. (%15 (|%13. ((%24 ((%20 (%38 $3)) ((%20 (%15 (|%12. (%15 (|%13. ((%24 ((%20 ($4 $1)) ($4 $0))) ((%24 (($5 $1) $0)) (($6 $1) $0)))))))) (%39 (((%32 $4) $1) $0))))) ((%34 (%39 (((%32 $3) $1) $0))) (%25 (|%14. ((%20 (%39 ($3 $0))) ((%20 (((%32 $4) $2) $0)) (((%32 $4) $0) $1)))))))))))))))))"])
  val op scc_tc_inclusion =
    DT(["DISK_THM"],
       [read"(%17 (|%3. (%16 (|%9. (%15 (|%6. (%15 (|%7. ((%24 ((%20 ((%29 $1) $2)) ((%20 ((%29 $0) $2)) ((%20 ((%31 $3) $2)) (%38 $3))))) (((%32 (|%6. (|%7. ((%20 (($5 $1) $0)) ((%20 ((%29 $1) $4)) ((%29 $0) $4)))))) $1) $0))))))))))"])
  val op TC_CASES1_NEQ =
    DT(["DISK_THM"],
       [read"(%17 (|%3. (%15 (|%12. (%15 (|%14. ((%24 (((%32 $2) $1) $0)) ((%34 (($2 $1) $0)) (%25 (|%13. ((%20 (%39 ((%21 $2) $0))) ((%20 (%39 ((%21 $0) $1))) ((%20 (($3 $2) $0)) (((%32 $3) $0) $1))))))))))))))"])
  val op TC_CASES2_NEQ =
    DT(["DISK_THM"],
       [read"(%17 (|%3. (%15 (|%12. (%15 (|%14. ((%24 (((%32 $2) $1) $0)) ((%34 (($2 $1) $0)) (%25 (|%13. ((%20 (%39 ((%21 $2) $0))) ((%20 (%39 ((%21 $0) $1))) ((%20 (((%32 $3) $2) $0)) (($3 $0) $1))))))))))))))"])
  val op SCC_loop_contradict =
    DT(["cheat"],
       [read"(%17 (|%3. (%16 (|%9. (%16 (|%10. ((%24 ((%20 (((%33 (%36 $2)) $1) $0)) (((%33 (%36 $2)) $0) $1))) ((%20 (%39 ((%31 $2) $1))) (%39 ((%31 $2) $0))))))))))"])
  end
  val _ = DB.bindl "SCC"
  [("SCC_def",SCC_def,DB.Def), ("lift_def",lift_def,DB.Def),
   ("cond_reflexive_def",cond_reflexive_def,DB.Def),
   ("scc_disjoint_lemma",scc_disjoint_lemma,DB.Thm),
   ("scc_lemma_x",scc_lemma_x,DB.Thm),
   ("TC_CASES1_RW",TC_CASES1_RW,DB.Thm),
   ("scc_lemma_xx",scc_lemma_xx,DB.Thm),
   ("scc_lemma_xxx",scc_lemma_xxx,DB.Thm),
   ("TC_CASES2_RW",TC_CASES2_RW,DB.Thm),
   ("scc_lemma_1_4_2_1_1_1_3_2_1_1",scc_lemma_1_4_2_1_1_1_3_2_1_1,DB.Thm),
   ("scc_lemma_1_4_2_1_1_1_3_2_1",scc_lemma_1_4_2_1_1_1_3_2_1,DB.Thm),
   ("scc_lemma_1_4_1_1_2_1_3",scc_lemma_1_4_1_1_2_1_3,DB.Thm),
   ("scc_lemma_1_4_2_1_1_1_3_2_2_1",scc_lemma_1_4_2_1_1_1_3_2_2_1,DB.Thm),
   ("scc_lemma_1_4_2_1_1_1_3_2_2",scc_lemma_1_4_2_1_1_1_3_2_2,DB.Thm),
   ("scc_lemma_1_4_2_1_1_1_3_2",scc_lemma_1_4_2_1_1_1_3_2,DB.Thm),
   ("scc_tc_inclusion",scc_tc_inclusion,DB.Thm),
   ("TC_CASES1_NEQ",TC_CASES1_NEQ,DB.Thm),
   ("TC_CASES2_NEQ",TC_CASES2_NEQ,DB.Thm),
   ("SCC_loop_contradict",SCC_loop_contradict,DB.Thm)]

  local open Portable GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val _ = mk_local_grms [("listTheory.list_grammars",
                          listTheory.list_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("SCC", (Term.prim_mk_const { Name = "SCC", Thy = "SCC"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("SCC", (Term.prim_mk_const { Name = "SCC", Thy = "SCC"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("lift", (Term.prim_mk_const { Name = "lift", Thy = "SCC"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("lift", (Term.prim_mk_const { Name = "lift", Thy = "SCC"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("cond_reflexive", (Term.prim_mk_const { Name = "cond_reflexive", Thy = "SCC"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("cond_reflexive", (Term.prim_mk_const { Name = "cond_reflexive", Thy = "SCC"}))
  val SCC_grammars = Parse.current_lgrms()
  end
  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "SCC",
    thydataty = "compute",
    data = "SCC.SCC_def SCC.cond_reflexive_def SCC.lift_def"
  }

val _ = if !Globals.print_thy_loads then print "done\n" else ()
val _ = Theory.load_complete "SCC"
end
