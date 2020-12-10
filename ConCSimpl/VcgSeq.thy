(*  Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

(*  Title:      Vcg.thy
    Author:     Norbert Schirmer, TU Muenchen

Copyright (C) 2004-2008 Norbert Schirmer
Some rights reserved, TU Muenchen

This library is free software; you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as
published by the Free Software Foundation; either version 2.1 of the
License, or (at your option) any later version.

This library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
USA
*)

section \<open>Facilitating the Hoare Logic\<close>
theory VcgSeq
imports VcgCon
begin

axiomatization NoBodyS::"('s,'b,'f) Language.com"

ML_file \<open>hoare_seq.ML\<close>

method_setup hoare = "Hoare.hoare"
  "raw verification condition generator for Hoare Logic"

method_setup hoare_raw = "Hoare.hoare_raw"
  "even more raw verification condition generator for Hoare Logic"

method_setup vcg = "Hoare.vcg"
  "verification condition generator for Hoare Logic"

method_setup vcg_step = "Hoare.vcg_step"
  "single verification condition generation step with light simplification"


method_setup hoare_rule = "Hoare.hoare_rule"
  "apply single hoare rule and solve certain sideconditions"


subsection \<open>Some Fancy Syntax\<close>


(* priority guidline:
 * If command should be atomic for the guard it must have at least priority 21.
 *)

text \<open>reverse application\<close>
definition rapp:: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b" (infixr "|>" 60)
  where "rapp x f = f x"


nonterminal
  switchcase_s and
  switchcases_s and
  bdy_s 
 

notation
  Language.Skip  ("SKIP\<^sub>s") and
  Language.Throw  ("THROW\<^sub>s")

syntax
(*  "_test" ::"('a => 'b)" ("TEST") *)
  "_guarantee"     :: "'s set \<Rightarrow> grd"       ("_\<surd>" [1000] 1000)
  "_guaranteeStrip":: "'s set \<Rightarrow> grd"       ("_#" [1000] 1000)
  "_grd"           :: "'s set \<Rightarrow> grd"       ("_" [1000] 1000)
  "_last_grd"      :: "grd \<Rightarrow> grds"         ("_" 1000)
  "_grds"          :: "[grd, grds] \<Rightarrow> grds" ("_,/ _" [999,1000] 1000)
  "_quote"       :: "'b => ('a => 'b)"
(*  "_antiquoteCur0"  :: "('a => 'b) => 'b"       ("\<acute>_" [1000] 1000)
  "_antiquoteCur"  :: "('a => 'b) => 'b"
  "_antiquoteOld0"  :: "('a => 'b) => 'a => 'b"       ("\<^bsup>_\<^esup>_" [1000,1000] 1000)
  "_antiquoteOld"  :: "('a => 'b) => 'a => 'b" *)
(*  "_Assert"      :: "'a => 'a set"            ("(\<lbrace>_\<rbrace>)" [0] 1000)
  "_AssertState" :: "idt \<Rightarrow> 'a => 'a set"     ("(\<lbrace>_. _\<rbrace>)" [1000,0] 1000) *)
  "_newinit"      :: "[ident,'a] \<Rightarrow> newinit" ("(2\<acute>_ :==/ _)")
  ""             :: "newinit \<Rightarrow> newinits"    ("_")
  "_newinits"    :: "[newinit, newinits] \<Rightarrow> newinits" ("_,/ _")
  "_locnoinit"    :: "ident \<Rightarrow> locinit"               ("\<acute>_")
  "_locinit"      :: "[ident,'a] \<Rightarrow> locinit"          ("(2\<acute>_ :==/ _)")
  ""             :: "locinit \<Rightarrow> locinits"             ("_")
  "_locinits"    :: "[locinit, locinits] \<Rightarrow> locinits" ("_,/ _")
  "_BasicBlock":: "basics \<Rightarrow> basicblock" ("_")
  "_BAssign"   :: "'b => 'b => basic"    ("(_ :==/ _)" [30, 30] 23)
  ""           :: "basic \<Rightarrow> basics"             ("_")
  "_basics"    :: "[basic, basics] \<Rightarrow> basics" ("_,/ _")

syntax
  "_raise_s":: "'c \<Rightarrow> 'c \<Rightarrow> ('a,'b,'f) Language.com"       ("(RAISE _ :==\<^sub>s/ _)" [30, 30] 23)
  "_seq_s"::"('s,'p,'f) Language.com \<Rightarrow> ('s,'p,'f) Language.com \<Rightarrow> ('s,'p,'f) Language.com" ("_;;\<^sub>s/ _" [20, 21] 20)
  "_guards_s"        :: "grds \<Rightarrow> ('s,'p,'f) Language.com \<Rightarrow> ('s,'p,'f) Language.com"
                                            ("(_/\<longmapsto>\<^sub>s _)" [60, 21] 23)
  "_Assign_s"      :: "'b => 'b => ('a,'p,'f) Language.com"    ("(_ :==\<^sub>s/ _)" [30, 30] 23)
  "_Init_s"        :: "ident \<Rightarrow> 'c \<Rightarrow> 'b \<Rightarrow> ('a,'p,'f) Language.com"
                                             ("(\<acute>_ :==\<^sub>s\<^bsub>_\<^esub>/ _)" [30,1000, 30] 23)
  "_GuardedAssign_s":: "'b => 'b => ('a,'p,'f) Language.com"    ("(_ :==\<^sub>g\<^sub>s/ _)" [30, 30] 23)
  
  "_New_s"         :: "['a, 'b, newinits] \<Rightarrow> ('a,'b,'f) Language.com"
                                            ("(_ :==\<^sub>s/(2 NEW _/ [_]))" [30, 65, 0] 23)
  "_GuardedNew_s"  :: "['a, 'b, newinits] \<Rightarrow> ('a,'b,'f) Language.com"
                                            ("(_ :==\<^sub>g\<^sub>s/(2 NEW _/ [_]))" [30, 65, 0] 23)
  "_NNew_s"         :: "['a, 'b, newinits] \<Rightarrow> ('a,'b,'f) Language.com"
                                            ("(_ :==\<^sub>s/(2 NNEW _/ [_]))" [30, 65, 0] 23)
  "_GuardedNNew_s"  :: "['a, 'b, newinits] \<Rightarrow> ('a,'b,'f) Language.com"
                                            ("(_ :==\<^sub>g\<^sub>s/(2 NNEW _/ [_]))" [30, 65, 0] 23)

  "_Cond_s"        :: "'a bexp => ('a,'p,'f) Language.com => ('a,'p,'f) Language.com => ('a,'p,'f) Language.com"
        ("(0IF\<^sub>s (_)/ (2THEN/ _)/ (2ELSE _)/ FI)" [0, 0, 0] 71)
  "_Cond_no_else_s":: "'a bexp => ('a,'p,'f) Language.com => ('a,'p,'f) Language.com"
        ("(0IF\<^sub>s (_)/ (2THEN/ _)/ FI)" [0, 0] 71)
  "_GuardedCond_s" :: "'a bexp => ('a,'p,'f) Language.com => ('a,'p,'f) Language.com => ('a,'p,'f) Language.com"
        ("(0IF\<^sub>g\<^sub>s (_)/ (2THEN _)/ (2ELSE _)/ FI)" [0, 0, 0] 71)
  "_GuardedCond_no_else_s":: "'a bexp => ('a,'p,'f) Language.com => ('a,'p,'f) Language.com"
        ("(0IF\<^sub>g\<^sub>s (_)/ (2THEN _)/ FI)" [0, 0] 71)
  "_While_inv_var_s"   :: "'a bexp => 'a assn  \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bdy_s
                          \<Rightarrow> ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s (_)/ INV (_)/ VAR (_) /_)"  [25, 0, 0, 81] 71)
  "_WhileFix_inv_var_s"   :: "'a bexp => pttrn \<Rightarrow> ('z \<Rightarrow> 'a assn)  \<Rightarrow>
                            ('z \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> bdy_s
                          \<Rightarrow> ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s (_)/ FIX _./ INV (_)/ VAR (_) /_)"  [25, 0, 0, 0, 81] 71)
  "_WhileFix_inv_s"   :: "'a bexp => pttrn \<Rightarrow> ('z \<Rightarrow> 'a assn)  \<Rightarrow> bdy_s
                          \<Rightarrow> ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s (_)/ FIX _./ INV (_) /_)"  [25, 0, 0, 81] 71)
  "_GuardedWhileFix_inv_var_s"   :: "'a bexp => pttrn \<Rightarrow> ('z \<Rightarrow> 'a assn)  \<Rightarrow>
                            ('z \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> bdy_s
                          \<Rightarrow> ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>g\<^sub>s (_)/ FIX _./ INV (_)/ VAR (_) /_)"  [25, 0, 0, 0, 81] 71)
  "_GuardedWhileFix_inv_var_hook_s"   :: "'a bexp \<Rightarrow> ('z \<Rightarrow> 'a assn)  \<Rightarrow>
                            ('z \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> bdy_s
                          \<Rightarrow> ('a,'p,'f) Language.com"
  "_GuardedWhileFix_inv_s"   :: "'a bexp => pttrn \<Rightarrow> ('z \<Rightarrow> 'a assn)  \<Rightarrow> bdy_s
                          \<Rightarrow> ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>g\<^sub>s (_)/ FIX _./ INV (_)/_)"  [25, 0, 0, 81] 71)

  "_GuardedWhile_inv_var_s"::
       "'a bexp => 'a assn  \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bdy_s \<Rightarrow> ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>g\<^sub>s (_)/ INV (_)/ VAR (_) /_)"  [25, 0, 0, 81] 71)
  "_While_inv_s"   :: "'a bexp => 'a assn => bdy_s => ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s (_)/ INV (_) /_)"  [25, 0, 81] 71)
  "_GuardedWhile_inv_s"   :: "'a bexp => 'a assn => ('a,'p,'f) Language.com => ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>g\<^sub>s (_)/ INV (_) /_)"  [25, 0, 81] 71)
  "_While_s"       :: "'a bexp => bdy_s => ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s (_) /_)"  [25, 81] 71)
  "_GuardedWhile_s"       :: "'a bexp => bdy_s => ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>g\<^sub>s (_) /_)"  [25, 81] 71)
  "_While_guard_s"       :: "grds => 'a bexp => bdy_s => ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s (_/\<longmapsto> (1_)) /_)"  [1000,25,81] 71)
  "_While_guard_inv_s":: "grds \<Rightarrow>'a bexp\<Rightarrow>'a assn\<Rightarrow>bdy_s \<Rightarrow> ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s (_/\<longmapsto> (1_)) INV (_) /_)"  [1000,25,0,81] 71)
  "_While_guard_inv_var_s":: "grds \<Rightarrow>'a bexp\<Rightarrow>'a assn\<Rightarrow>('a\<times>'a) set
                             \<Rightarrow>bdy_s \<Rightarrow> ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s (_/\<longmapsto> (1_)) INV (_)/ VAR (_) /_)"  [1000,25,0,0,81] 71)
  "_WhileFix_guard_inv_var_s":: "grds \<Rightarrow>'a bexp\<Rightarrow>pttrn\<Rightarrow>('z\<Rightarrow>'a assn)\<Rightarrow>('z\<Rightarrow>('a\<times>'a) set)
                             \<Rightarrow>bdy_s \<Rightarrow> ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s (_/\<longmapsto> (1_)) FIX _./ INV (_)/ VAR (_) /_)"  [1000,25,0,0,0,81] 71)
  "_WhileFix_guard_inv_s":: "grds \<Rightarrow>'a bexp\<Rightarrow>pttrn\<Rightarrow>('z\<Rightarrow>'a assn)
                             \<Rightarrow>bdy_s \<Rightarrow> ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s (_/\<longmapsto> (1_)) FIX _./ INV (_)/_)"  [1000,25,0,0,81] 71)

  "_Try_Catch_s":: "('a,'p,'f) Language.com \<Rightarrow>('a,'p,'f) Language.com \<Rightarrow> ('a,'p,'f) Language.com"
        ("(0TRY\<^sub>s (_)/ (2CATCH _)/ END)"  [0,0] 71)

  "_DoPre_s" :: "('a,'p,'f) Language.com \<Rightarrow> ('a,'p,'f) Language.com"
  "_Do_s" :: "('a,'p,'f) Language.com \<Rightarrow> bdy_s" ("(2DO\<^sub>s/ (_)) /OD" [0] 1000)
  "_Lab_s":: "'a bexp \<Rightarrow> ('a,'p,'f) Language.com \<Rightarrow> bdy_s"
            ("_\<bullet>\<^sub>s/_" [1000,71] 81)
  "":: "bdy_s \<Rightarrow> ('a,'p,'f) Language.com" ("_")
  "_Spec_s":: "pttrn \<Rightarrow> 's set \<Rightarrow>  ('s,'p,'f) Language.com \<Rightarrow> 's set \<Rightarrow> 's set \<Rightarrow> ('s,'p,'f) Language.com"
            ("(ANNO\<^sub>s _. _/ (_)/ _,/_)" [0,1000,20,1000,1000] 60)
  "_SpecNoAbrupt_s":: "pttrn \<Rightarrow> 's set \<Rightarrow>  ('s,'p,'f) Language.com \<Rightarrow> 's set \<Rightarrow> ('s,'p,'f) Language.com"
            ("(ANNO\<^sub>s _. _/ (_)/ _)" [0,1000,20,1000] 60)
  "_LemAnno_s":: "'n \<Rightarrow> ('s,'p,'f) Language.com \<Rightarrow> ('s,'p,'f) Language.com"
              ("(0 LEMMA\<^sub>s (_)/ _ END)" [1000,0] 71)
  
  "_Loc_s":: "[locinits,('s,'p,'f) Language.com] \<Rightarrow> ('s,'p,'f) Language.com"
                                         ("(2 LOC\<^sub>s _;;/ (_) COL)" [0,0] 71)
  "_Switch_s":: "('s \<Rightarrow> 'v) \<Rightarrow> switchcases_s \<Rightarrow> ('s,'p,'f) Language.com"
              ("(0 SWITCH\<^sub>s (_)/ _ END)" [22,0] 71)
  "_switchcase_s":: "'v set \<Rightarrow> ('s,'p,'f) Language.com \<Rightarrow> switchcase_s" ("_\<Rightarrow>\<^sub>s/ _" )
  "_switchcasesSingle_s"  :: "switchcase_s \<Rightarrow> switchcases_s" ("_")
  "_switchcasesCons_s":: "switchcase_s \<Rightarrow> switchcases_s \<Rightarrow> switchcases_s"
                       ("_/ |\<^sub>s _")
  "_Basic_s":: "basicblock \<Rightarrow> ('s,'p,'f) Language.com" ("(0BASIC\<^sub>s/ (_)/ END)" [22] 71)

(* syntax (ASCII)  
 "_Assert"      :: "'a => 'a set"           ("({|_|})" [0] 1000)
  "_AssertState" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a set"    ("({|_. _|})" [1000,0] 1000) *)


syntax (ASCII) 
  "_While_guard_s"       :: "grds => 'a bexp => bdy_s \<Rightarrow> ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s (_|-> /_) /_)"  [0,0,1000] 71)
  "_While_guard_inv_s":: "grds\<Rightarrow>'a bexp\<Rightarrow>'a assn\<Rightarrow>bdy_s \<Rightarrow> ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s (_|-> /_) INV (_) /_)"  [0,0,0,1000] 71)
  "_guards_s" :: "grds \<Rightarrow> ('s,'p,'f) Language.com \<Rightarrow> ('s,'p,'f) Language.com" ("(_|->\<^sub>s_ )" [60, 21] 23)

syntax (output)
  "_hidden_grds"      :: "grds" ("\<dots>")

translations
  "_Do_s c" => "c"
  "b\<bullet>\<^sub>s c" => "CONST Language.condCatch c b SKIP\<^sub>s"
  "b\<bullet>\<^sub>s (_DoPre_s c)" <= "CONST Language.condCatch c b SKIP\<^sub>s"
  "l\<bullet>\<^sub>s (CONST Language.whileAnnoG gs b I V c)" <= "l\<bullet>\<^sub>s (_DoPre_s (CONST Language.whileAnnoG gs b I V c))"
  "l\<bullet>\<^sub>s (CONST Language.whileAnno b I V c)" <= "l\<bullet>\<^sub>s (_DoPre_s (CONST Language.whileAnno b I V c))"
  "CONST Language.condCatch c b SKIP\<^sub>s" <= "(_DoPre_s (CONST Language.condCatch c b SKIP\<^sub>s))"
  "_Do_s c" <= "_DoPre_s c"              
  "c;;\<^sub>s d" == "CONST Language.Seq c d"
  "_guarantee g" => "(CONST True, g)"
  "_guaranteeStrip g" == "CONST Language.guaranteeStripPair (CONST True) g"
  "_grd g" => "(CONST False, g)"
  "_grds g gs" => "g#gs"
  "_last_grd g" => "[g]"
  "_guards_s gs c" == "CONST Language.guards gs c"

  "{|s. P|}"                   == "{|_antiquoteCur((=) s) \<and> P |}"
  "{|b|}"                   => "CONST Collect (_quote b)"
  "IF\<^sub>s b THEN c1 ELSE c2 FI" => "CONST Language.Cond {|b|} c1 c2"
  "IF\<^sub>s b THEN c1 FI"         ==  "IF\<^sub>s b THEN c1 ELSE SKIP\<^sub>s FI"
  "IF\<^sub>g\<^sub>s b THEN c1 FI"        ==  "IF\<^sub>g\<^sub>s b THEN c1 ELSE SKIP\<^sub>s FI"

  "_While_inv_var_s b I V c"          => "CONST Language.whileAnno {|b|} I V c"
  "_While_inv_var_s b I V (_DoPre_s c)" <= "CONST Language.whileAnno {|b|} I V c"
  "_While_inv_s b I c"                 == "_While_inv_var_s b I (CONST undefined) c"
  "_While_s b c"                       == "_While_inv_s b {|CONST undefined|} c"

  "_While_guard_inv_var_s gs b I V c"          => "CONST Language.whileAnnoG gs {|b|} I V c"
(*  "_While_guard_inv_var gs b I V (_DoPre c)" <= "CONST whileAnnoG gs {|b|} I V c"*)
  "_While_guard_inv_s gs b I c"       == "_While_guard_inv_var_s gs b I (CONST undefined) c"
  "_While_guard_s gs b c"             == "_While_guard_inv_s gs b {|CONST undefined|} c"

  "_GuardedWhile_inv_s b I c"  == "_GuardedWhile_inv_var_s b I (CONST undefined) c"
  "_GuardedWhile_s b c"        == "_GuardedWhile_inv_s b {|CONST undefined|} c"
(*  "\<^bsup>s\<^esup>A"                      => "A s"*)
  "TRY\<^sub>s c1 CATCH c2 END"     == "CONST Language.Catch c1 c2"
  "ANNO\<^sub>s s. P c Q,A" => "CONST Language.specAnno (\<lambda>s. P) (\<lambda>s. c) (\<lambda>s. Q) (\<lambda>s. A)"
  "ANNO\<^sub>s s. P c Q" == "ANNO\<^sub>s s. P c Q,{}"

  "_WhileFix_inv_var_s b z I V c" => "CONST Language.whileAnnoFix {|b|} (\<lambda>z. I) (\<lambda>z. V) (\<lambda>z. c)"
  "_WhileFix_inv_var_s b z I V (_DoPre_s c)" <= "_WhileFix_inv_var_s {|b|} z I V c"
  "_WhileFix_inv_s b z I c" == "_WhileFix_inv_var_s b z I (CONST undefined) c"

  "_GuardedWhileFix_inv_s b z I c" == "_GuardedWhileFix_inv_var_s b z I (CONST undefined) c"

  "_GuardedWhileFix_inv_var_s b z I V c" =>
                         "_GuardedWhileFix_inv_var_hook_s {|b|} (\<lambda>z. I) (\<lambda>z. V) (\<lambda>z. c)"

  "_WhileFix_guard_inv_var_s gs b z I V c" =>
                                      "CONST Language.whileAnnoGFix gs {|b|} (\<lambda>z. I) (\<lambda>z. V) (\<lambda>z. c)"
  "_WhileFix_guard_inv_var_s gs b z I V (_DoPre_s c)" <=
                                      "_WhileFix_guard_inv_var_s gs {|b|} z I V c"
  "_WhileFix_guard_inv_s gs b z I c" == "_WhileFix_guard_inv_var_s gs b z I (CONST undefined) c"
  "LEMMA\<^sub>s x c END" == "CONST lem x c"

translations
 "(_switchcase_s V c)" => "(V,c)"
 "(_switchcasesSingle_s b)" => "[b]"
 "(_switchcasesCons_s b bs)" => "CONST Cons b bs"
 "(_Switch_s v vs)" => "CONST Language.switch (_quote v) vs"


print_ast_translation \<open>
  let
    fun tr c asts = Ast.mk_appl (Ast.Constant c) asts
  in
   [(@{syntax_const "_antiquoteCur"}, K (tr @{syntax_const "_antiquoteCur0"})),
    (@{syntax_const "_antiquoteOld"}, K (tr @{syntax_const "_antiquoteOld0"}))]
  end
\<close> 

print_ast_translation \<open>
  let
    fun dest_abs (Ast.Appl [Ast.Constant @{syntax_const "_abs"}, x, t]) = (x, t)
      | dest_abs _ = raise Match;
    fun spec_tr' [P, c, Q, A] =
      let
        val (x',P') = dest_abs P;
        val (_ ,c') = dest_abs c;
        val (_ ,Q') = dest_abs Q;
        val (_ ,A') = dest_abs A;
      in
        if (A' = Ast.Constant @{const_syntax bot})
        then Ast.mk_appl (Ast.Constant @{syntax_const "_SpecNoAbrupt_s"}) [x', P', c', Q']
        else Ast.mk_appl (Ast.Constant @{syntax_const "_Spec_s"}) [x', P', c', Q', A']
      end;
    fun whileAnnoFix_tr' [b, I, V, c] =
      let
        val (x',I') = dest_abs I;
        val (_ ,V') = dest_abs V;
        val (_ ,c') = dest_abs c;
      in
        Ast.mk_appl (Ast.Constant @{syntax_const "_WhileFix_inv_var_s"}) [b, x', I', V', c']
      end;
  in
   [(@{const_syntax specAnno}, K spec_tr'),
    (@{const_syntax whileAnnoFix}, K whileAnnoFix_tr')]
  end
\<close>



syntax
  "_faccess"  :: "'ref \<Rightarrow> ('ref \<Rightarrow> 'v) \<Rightarrow> 'v"
   ("_\<rightarrow>_" [65,1000] 100)

syntax (ASCII)
  "_faccess"  :: "'ref \<Rightarrow> ('ref \<Rightarrow> 'v) \<Rightarrow> 'v"
   ("_->_" [65,1000] 100)

translations

 "p\<rightarrow>f"        =>  "f p"
 "g\<rightarrow>(_antiquoteCur f)" <= "_antiquoteCur f g"

nonterminal par and pars and actuals

syntax
  "_par" :: "'a \<Rightarrow> par"                                ("_")
  ""    :: "par \<Rightarrow> pars"                               ("_")
  "_pars" :: "[par,pars] \<Rightarrow> pars"                      ("_,/_")
  "_actuals" :: "pars \<Rightarrow> actuals"                      ("'(_')")
  "_actuals_empty" :: "actuals"                        ("'(')")

syntax "_Call_s" :: "'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) Language.com)" ("CALL\<^sub>s __" [1000,1000] 21)
       "_GuardedCall_s" :: "'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) Language.com)" ("CALL\<^sub>g\<^sub>s __" [1000,1000] 21)
       "_CallAss_s":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) Language.com)"
             ("_ :== CALL\<^sub>s __" [30,1000,1000] 21)
       "_Proc_s" :: "'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) Language.com)" ("PROC\<^sub>s __" 21)
       "_ProcAss_s":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) Language.com)"
             ("_ :== PROC\<^sub>s __" [30,1000,1000] 21)
       "_GuardedCallAss_s":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) Language.com)"
             ("_ :== CALL\<^sub>g\<^sub>s __" [30,1000,1000] 21)
       "_DynCall_s" :: "'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) Language.com)" ("DYNCALL\<^sub>s __" [1000,1000] 21)
       "_GuardedDynCall_s" :: "'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) Language.com)" ("DYNCALL\<^sub>g\<^sub>s __" [1000,1000] 21)
       "_DynCallAss_s":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) Language.com)"
             ("_ :== DYNCALL\<^sub>s __" [30,1000,1000] 21)
       "_GuardedDynCallAss_s":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) Language.com)"
             ("_ :== DYNCALL\<^sub>g\<^sub>s __" [30,1000,1000] 21)

       "_Bind_s":: "['s \<Rightarrow> 'v, idt, 'v \<Rightarrow> ('s,'p,'f) Language.com] \<Rightarrow> ('s,'p,'f) Language.com"
                      ("_ \<ggreater>\<^sub>s _./ _" [22,1000,21] 21)
       "_bseq_s"::"('s,'p,'f) Language.com \<Rightarrow> ('s,'p,'f) Language.com \<Rightarrow> ('s,'p,'f) Language.com"
           ("_\<ggreater>\<^sub>s/ _" [22, 21] 21)
       "_FCall_s" :: "['p,actuals,idt,(('a,string,'f) Language.com)]\<Rightarrow> (('a,string,'f) Language.com)"
                      ("CALL\<^sub>s __ \<ggreater> _./ _" [1000,1000,1000,21] 21)



translations
"_Bind_s e i c" == "CONST Language.bind (_quote e) (\<lambda>i. c)"
"_FCall_s p acts i c" == "_FCall_s p acts (\<lambda>i. c)"
"_bseq_s c d" == "CONST Language.bseq c d"



nonterminal modifyargs

syntax
  "_may_modify" :: "['a,'a,modifyargs] \<Rightarrow> bool"
        ("_ may'_only'_modify'_globals _ in [_]" [100,100,0] 100)
  "_may_not_modify" :: "['a,'a] \<Rightarrow> bool"
        ("_ may'_not'_modify'_globals _" [100,100] 100)
  "_may_modify_empty" :: "['a,'a] \<Rightarrow> bool"
        ("_ may'_only'_modify'_globals _ in []" [100,100] 100)
  "_modifyargs" :: "[id,modifyargs] \<Rightarrow> modifyargs" ("_,/ _")
  ""            :: "id => modifyargs"              ("_")

translations
"s may_only_modify_globals Z in []" => "s may_not_modify_globals Z"


definition Let':: "['a, 'a => 'b] => 'b"
  where "Let' = Let"
                  
ML_file \<open>hoare_syntax_seq.ML\<close>

parse_translation \<open>
  let
    val argsC = @{syntax_const "_modifyargs"};
    val globalsN = "globals";
    val ex = @{const_syntax mex};
    val eq = @{const_syntax meq};
    val varn = Hoare.varname;

    fun extract_args (Const (argsC,_)$Free (n,_)$t) = varn n::extract_args t
      | extract_args (Free (n,_)) = [varn n]
      | extract_args t            = raise TERM ("extract_args", [t])

    fun idx [] y = error "idx: element not in list"
     |  idx (x::xs) y = if x=y then 0 else (idx xs y)+1

    fun gen_update ctxt names (name,t) =
        Hoare_Syntax.update_comp ctxt [] false true name (Bound (idx names name)) t

    fun gen_updates ctxt names t = Library.foldr (gen_update ctxt names) (names,t)

    fun gen_ex (name,t) = Syntax.const ex $ Abs (name,dummyT,t)

    fun gen_exs names t = Library.foldr gen_ex (names,t)


    fun tr ctxt s Z names =
      let val upds = gen_updates ctxt (rev names) (Syntax.free globalsN$Z);
          val eq   = Syntax.const eq $ (Syntax.free globalsN$s) $ upds;
      in gen_exs names eq end;

    fun may_modify_tr ctxt [s,Z,names] = tr ctxt s Z
                                           (sort_strings (extract_args names))
    fun may_not_modify_tr ctxt [s,Z] = tr ctxt s Z []
  in
   [(@{syntax_const "_may_modify"}, may_modify_tr),
    (@{syntax_const "_may_not_modify"}, may_not_modify_tr)]
  end
\<close>


print_translation \<open>
  let
    val argsC = @{syntax_const "_modifyargs"};
    val chop = Hoare.chopsfx Hoare.deco;
                                    
    fun get_state ( _ $ _ $ t) = get_state t  (* for record-updates*)
      | get_state ( _ $ _ $ _ $ _ $ _ $ t) = get_state t (* for statespace-updates *)
      | get_state (globals$(s as Const (@{syntax_const "_free"},_) $ Free _)) = s
      | get_state (globals$(s as Const (@{syntax_const "_bound"},_) $ Free _)) = s
      | get_state (globals$(s as Const (@{syntax_const "_var"},_) $ Var _)) = s
      | get_state (globals$(s as Const _)) = s
      | get_state (globals$(s as Free _)) = s
      | get_state (globals$(s as Bound _)) = s
      | get_state t              = raise Match;

    fun mk_args [n] = Syntax.free (chop n)
      | mk_args (n::ns) = Syntax.const argsC $ Syntax.free (chop n) $ mk_args ns
      | mk_args _      = raise Match;

    fun tr' names (Abs (n,_,t)) = tr' (n::names) t
      | tr' names (Const (@{const_syntax mex},_) $ t) = tr' names t
      | tr' names (Const (@{const_syntax meq},_) $ (globals$s) $ upd) =
            let val Z = get_state upd;

            in (case names of
                  [] => Syntax.const @{syntax_const "_may_not_modify"} $ s $ Z
                | xs => Syntax.const @{syntax_const "_may_modify"} $ s $ Z $ mk_args (rev names))
            end;

    fun may_modify_tr' [t] = tr' [] t
    fun may_not_modify_tr' [_$s,_$Z] = Syntax.const @{syntax_const "_may_not_modify"} $ s $ Z
  in
    [(@{const_syntax mex}, K may_modify_tr'),
     (@{const_syntax meq}, K may_not_modify_tr')]
  end
\<close>


(* decorate state components with suffix *)
(*
parse_ast_translation {*
 [(@{syntax_const "_Free"}, K Hoare_Syntax.free_arg_ast_tr),
  (@{syntax_const "_In"}, K Hoare_Syntax.in_arg_ast_tr),
  (@{syntax_const "_Where"}, K Hoare_Syntax.where_arg_ast_tr @{syntax_const "_Where"}),
  (@{syntax_const "_WhereElse"}, K Hoare_Syntax.where_arg_ast_tr @{syntax_const "_WhereElse"})
]
*}
*)
(*
parse_ast_translation {*
 [(@{syntax_const "_antiquoteOld"},
    Hoare_Syntax.antiquoteOld_varname_tr @{syntax_const "_antiquoteOld"})]
*}
*)




parse_translation \<open>
 [(@{syntax_const "_Call_s"}, Hoare_Syntax.call_tr false false),
  (@{syntax_const "_FCall_s"}, Hoare_Syntax.fcall_tr),
  (@{syntax_const "_CallAss_s"}, Hoare_Syntax.call_ass_tr false false),
  (@{syntax_const "_GuardedCall_s"}, Hoare_Syntax.call_tr false true),
  (@{syntax_const "_GuardedCallAss_s"}, Hoare_Syntax.call_ass_tr false true),
  (@{syntax_const "_Proc_s"}, Hoare_Syntax.proc_tr),
  (@{syntax_const "_ProcAss_s"}, Hoare_Syntax.proc_ass_tr),
  (@{syntax_const "_DynCall_s"}, Hoare_Syntax.call_tr true false),
  (@{syntax_const "_DynCallAss_s"}, Hoare_Syntax.call_ass_tr true false),
  (@{syntax_const "_GuardedDynCall_s"}, Hoare_Syntax.call_tr true true),
  (@{syntax_const "_GuardedDynCallAss_s"}, Hoare_Syntax.call_ass_tr true true)]
\<close>

(*
  (@{syntax_const "_Call"}, Hoare_Syntax.call_ast_tr),
  (@{syntax_const "_CallAss"}, Hoare_Syntax.call_ass_ast_tr),
  (@{syntax_const "_GuardedCall"}, Hoare_Syntax.guarded_call_ast_tr),
  (@{syntax_const "_GuardedCallAss"}, Hoare_Syntax.guarded_call_ass_ast_tr)
*)



(* parse_translation \<open>
 [(@{syntax_const "_antiquoteCur"},
    (Hoare_Syntax.antiquote_varname_tr @{syntax_const "_antiquoteCur"}))]
\<close>                      

parse_translation \<open>
[(@{syntax_const "_antiquoteOld"}, Hoare_Syntax.antiquoteOld_tr),
  (@{syntax_const "_BasicBlock"}, Hoare_Syntax.basic_assigns_tr)]
\<close>

parse_translation \<open>
  let   
     fun quote_tr1 ctxt t =      
(*       let 
         val y = writeln (@{make_string} t);
         val z = writeln ("quote result: "^(@{make_string} (Hoare_Syntax.quote_tr ctxt @{syntax_const "_antiquoteCur"} t))) 
       in *)
         Hoare_Syntax.quote_tr ctxt @{syntax_const "_antiquoteCur"} t     
(*       end; *)
     fun quote_tr ctxt [t] = quote_tr1 ctxt t     
     | quote_tr ctxt ts = raise TERM ("quote_tr", ts);
  in [(@{syntax_const "_quote"}, quote_tr)] end
\<close>
*)
(* parse_translation \<open>
  let   
     fun assert_tr1 ctxt t =      
       let 
         val x = (Syntax.const @{const_syntax Collect}) $ 
                           (Hoare_Syntax.quote_tr ctxt @{syntax_const "_antiquoteCur"} t)
         (* val y = writeln (@{make_string} t);
         val z = writeln (@{make_string} x); *)
       in x     
     end; 
     fun assert_tr ctxt [t] = assert_tr1 ctxt t
       | assert_tr ctxt ts = raise TERM ("assert_tr", ts);
  in [(@{syntax_const "_Assert"}, assert_tr)] end
\<close> *)

(* parse_translation \<open>
  let 
    fun test_tr ctxt [] = 
    let val x =  writeln (Syntax.string_of_term ctxt (Syntax.free "x_'")) in 
       (Syntax.free "x_'")
    end;
  in[(@{syntax_const "_test"},test_tr)] end
\<close> *)


parse_translation \<open>
 [(@{syntax_const "_Assign_s"}, Hoare_Syntax.assign_tr),
  (@{syntax_const "_raise_s"}, Hoare_Syntax.raise_tr),
  (@{syntax_const "_New_s"}, Hoare_Syntax.new_tr),
  (@{syntax_const "_NNew_s"}, Hoare_Syntax.nnew_tr),
  (@{syntax_const "_GuardedAssign_s"}, Hoare_Syntax.guarded_Assign_tr),
  (@{syntax_const "_GuardedNew_s"}, Hoare_Syntax.guarded_New_tr),
  (@{syntax_const "_GuardedNNew_s"}, Hoare_Syntax.guarded_NNew_tr),
  (@{syntax_const "_GuardedWhile_inv_var_s"}, Hoare_Syntax.guarded_While_tr),
  (@{syntax_const "_GuardedWhileFix_inv_var_hook_s"}, Hoare_Syntax.guarded_WhileFix_tr),
  (@{syntax_const "_GuardedCond_s"}, Hoare_Syntax.guarded_Cond_tr),
  (@{syntax_const "_Basic_s"}, Hoare_Syntax.basic_tr)]
\<close>

parse_translation \<open>
 [(@{syntax_const "_Init_s"}, Hoare_Syntax.init_tr),
  (@{syntax_const "_Loc_s"}, Hoare_Syntax.loc_tr)]
\<close>


print_translation \<open>
 [(@{const_syntax Language.Basic}, Hoare_Syntax.assign_tr'),
  (@{const_syntax Language.raise}, Hoare_Syntax.raise_tr'),
  (@{const_syntax Language.Basic}, Hoare_Syntax.new_tr'),
  (@{const_syntax Language.Basic}, Hoare_Syntax.init_tr'),
  (@{const_syntax Language.Spec}, Hoare_Syntax.nnew_tr'),
  (@{const_syntax Language.block}, Hoare_Syntax.loc_tr'),
  (@{const_syntax Collect}, Hoare_Syntax.assert_tr'),
  (@{const_syntax Language.Cond}, Hoare_Syntax.bexp_tr' "_Cond"),
  (@{const_syntax Language.switch}, Hoare_Syntax.switch_tr'),
  (@{const_syntax Language.Basic}, Hoare_Syntax.basic_tr'),
  (@{const_syntax Language.guards}, Hoare_Syntax.guards_tr'),
  (@{const_syntax Language.whileAnnoG}, Hoare_Syntax.whileAnnoG_tr'),
  (@{const_syntax Language.whileAnnoGFix}, Hoare_Syntax.whileAnnoGFix_tr'),
  (@{const_syntax Language.bind}, Hoare_Syntax.bind_tr')]
\<close>


print_translation \<open>
  let
    fun spec_tr' ctxt ((coll as Const _)$
                   ((splt as Const _) $ (t as (Abs (s,T,p))))::ts) =
          let
            fun selector (Const (c, T)) = Hoare.is_state_var c
              | selector (Const (@{syntax_const "_free"}, _) $ (Free (c, T))) =
                  Hoare.is_state_var c
              | selector _ = false;
          in
            if Hoare_Syntax.antiquote_applied_only_to selector p then
              Syntax.const @{const_syntax Spec} $ coll $
                (splt $ Hoare_Syntax.quote_mult_tr' ctxt selector
                    Hoare_Syntax.antiquoteCur Hoare_Syntax.antiquoteOld  (Abs (s,T,t)))
             else raise Match
          end
      | spec_tr' _ ts = raise Match
  in [(@{const_syntax Language.Spec}, spec_tr')] end
\<close>

syntax
"_Measure":: "('a \<Rightarrow> nat) \<Rightarrow> ('a \<times> 'a) set"
      ("MEASURE _" [22] 1)
"_Mlex":: "('a \<Rightarrow> nat) \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"
      (infixr "<*MLEX*>" 30)


translations
 "MEASURE f"       => "(CONST measure) (_quote f)"
 "f <*MLEX*> r"       => "(_quote f) <*mlex*> r"



print_translation \<open>
  let
    fun selector (Const (c,T)) = Hoare.is_state_var c
      | selector _ = false;

    fun measure_tr' ctxt ((t as (Abs (_,_,p)))::ts) =
          if Hoare_Syntax.antiquote_applied_only_to selector p
          then Hoare_Syntax.app_quote_tr' ctxt (Syntax.const @{syntax_const "_Measure"}) (t::ts)
          else raise Match
      | measure_tr' _ _ = raise Match

    fun mlex_tr' ctxt ((t as (Abs (_,_,p)))::r::ts) =
          if Hoare_Syntax.antiquote_applied_only_to selector p
          then Hoare_Syntax.app_quote_tr' ctxt (Syntax.const @{syntax_const "_Mlex"}) (t::r::ts)
          else raise Match
      | mlex_tr' _ _ = raise Match

  in
   [(@{const_syntax measure}, measure_tr'),
    (@{const_syntax mlex_prod}, mlex_tr')]
  end
\<close>


print_translation \<open>
 [(@{const_syntax Language.call}, Hoare_Syntax.call_tr'),
  (@{const_syntax Language.dynCall}, Hoare_Syntax.dyn_call_tr'),
  (@{const_syntax Language.fcall}, Hoare_Syntax.fcall_tr'),
  (@{const_syntax Language.Call}, Hoare_Syntax.proc_tr')]
\<close>

end
