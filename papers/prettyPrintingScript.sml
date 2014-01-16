open HolKernel Parse boolLib bossLib;

open GraphPlanTheoremTheory

val _ = new_theory "prettyPrinting";

val _ = overload_on ("stitch", ``replace_projected``)
val _ = overload_on ("LL", ``problem_plan_bound``)

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Closefix,
                  term_name = "LENGTH",
                  pp_elements = [TOK "BarLeft|", TM, TOK "|BarRight"]}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Closefix,
                  term_name = "CARD",
                  pp_elements = [TOK "BarLeft|", TM, TOK "|BarRight"]}



val _ = export_theory();
