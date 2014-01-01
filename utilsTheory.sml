structure utilsTheory :> utilsTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading utilsTheory ... " else ()
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
          ("utils",
          Arbnum.fromString "1388583099",
          Arbnum.fromString "878680")
          [("list",
           Arbnum.fromString "1380541561",
           Arbnum.fromString "111594")];
  val _ = Theory.incorporate_types "utils" [];

  val idvector = 
    let fun ID(thy,oth) = {Thy = thy, Other = oth}
    in Vector.fromList
  [ID("min", "fun"), ID("min", "bool"), ID("num", "num"),
   ID("list", "list"), ID("bool", "!"), ID("arithmetic", "*"),
   ID("bool", "/\\"), ID("prim_rec", "<"), ID("min", "="),
   ID("min", "==>"), ID("bool", "?"), ID("list", "APPEND"),
   ID("list", "FILTER"), ID("bool", "IN"), ID("list", "LENGTH"),
   ID("list", "LIST_TO_SET"), ID("bool", "~")]
  end;
  local open SharingTables
  in
  val tyvector = build_type_vector idvector
  [TYOP [1], TYV "'a", TYOP [0, 1, 0], TYOP [2], TYOP [3, 1],
   TYOP [0, 2, 0], TYOP [0, 5, 0], TYOP [0, 4, 0], TYOP [0, 7, 0],
   TYOP [0, 3, 0], TYOP [0, 9, 0], TYOP [0, 3, 3], TYOP [0, 3, 11],
   TYOP [0, 0, 0], TYOP [0, 0, 13], TYOP [0, 3, 9], TYOP [0, 4, 7],
   TYOP [0, 4, 4], TYOP [0, 4, 17], TYOP [0, 2, 17], TYOP [0, 1, 5],
   TYOP [0, 4, 3], TYOP [0, 4, 2]]
  end
  val _ = Theory.incorporate_consts "utils" tyvector [];

  local open SharingTables
  in
  val tmvector = build_term_vector idvector tyvector
  [TMV("P1", 2), TMV("P2", 2), TMV("k1", 3), TMV("k2", 3), TMV("l", 4),
   TMV("l'", 4), TMV("pfx", 4), TMV("sfx", 4), TMV("x", 1), TMC(4, 5),
   TMC(4, 6), TMC(4, 8), TMC(4, 10), TMC(5, 12), TMC(6, 14), TMC(7, 15),
   TMC(8, 14), TMC(8, 16), TMC(9, 14), TMC(10, 8), TMC(11, 18),
   TMC(12, 19), TMC(13, 20), TMC(14, 21), TMC(15, 22), TMC(16, 13)]
  end
  local
  val DT = Thm.disk_thm val read = Term.read_raw tmvector
  in
  val op twosorted_list_length =
    DT(["DISK_THM"],
       [read"(%10 (|%0. (%10 (|%1. (%11 (|%4. (%12 (|%2. (%12 (|%3. ((%18 ((%14 (%9 (|%8. ((%18 ((%22 $0) (%24 $3))) ((%16 (%25 ($5 $0))) ($4 $0)))))) ((%14 ((%15 (%23 ((%21 $4) $2))) $1)) (%11 (|%5. ((%18 ((%14 (%19 (|%6. (%19 (|%7. ((%17 ((%20 ((%20 $1) $2)) $0)) $5)))))) (%9 (|%8. ((%18 ((%22 $0) (%24 $1))) ($5 $0)))))) ((%15 (%23 $0)) $1))))))) ((%15 (%23 $2)) ((%13 $1) $0)))))))))))))"])
  end
  val _ = DB.bindl "utils"
  [("twosorted_list_length",twosorted_list_length,DB.Thm)]

  local open Portable GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val _ = mk_local_grms [("listTheory.list_grammars",
                          listTheory.list_grammars)]
  val _ = List.app (update_grms reveal) []

  val utils_grammars = Parse.current_lgrms()
  end

val _ = if !Globals.print_thy_loads then print "done\n" else ()
val _ = Theory.load_complete "utils"
end
