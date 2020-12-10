section {* User Guide \label{sec:UserGuide}*}
(*<*)
theory Test 
imports HeapList VcgSeq 
  "~~/src/HOL/Statespace/StateSpaceSyntax" "~~/src/HOL/Library/LaTeXsugar"
begin 
record globals_i = x_'::"nat \<times> nat"
record locals_j = y_':: "nat \<times> nat"


lemma "\<lbrace>fst \<acute>x = fst \<acute>y \<rbrace> \<noteq> \<emptyset>" apply auto   
  by (metis locals_j.select_convs(1))
  
(**\<acute>x is unfolded into 
   Const @{syntax_const "_antiquoteCur"}$(Const ("x_'",dummy))
   Const @{syntax_const "_antiquoteCur"}$(Free ("x_'",dummy))
   Const @{syntax_const "_antiquoteCur"}$ n$
**)

term "\<acute>y :==\<^sub>s \<acute>x"
term "\<acute>y :== \<acute>x"
  term "(1,1)"

ML\<open>Syntax.read_term @{context} "\<acute>x :==\<^sub>s \<acute>y"\<close> 
ML\<open>

(*
FIXME:
update of global and local components:
One should generally provide functions:
glob_upd:: ('g => 'g) => 's => 's
loc_upd:: ('l => 'l) => 's => 's
so that global and local updates can nicely be composed.
loc_upd for the record implementation is vacuous.
Right now for example an assignment of NEW to a global variable returns
a funny repeated update of global components...

This would make the composition more straightforward...
Basically one wants the map on a component rather then the update. Maps can
be composed nicer...
*)
\<close>

ML\<open>
val l = Syntax.read_term @{context} "LanguageCon.Skip";

val v = writeln (Syntax.string_of_term @{context} l);
val v = writeln (@{make_string} l)
\<close>
record globals_state2 = u_'::"nat" z_'::"nat" w_'::"nat" p_'::ref 
                         next_' :: "ref \<Rightarrow> ref"
                         cont_' :: "ref \<Rightarrow> nat"                         
                         alloc_'::"ref list"
                         free_'::nat x_'::nat
record locals1 = mm_' :: "nat" yy_' :: "nat" nn_':: "nat" obj_':: "ref \<Rightarrow> int" p1_' :: "ref"  y_' ::"nat" q_'::ref
term "\<acute>mm :==\<^sub>s \<acute>mm ;;\<^sub>s \<acute>u :==\<^sub>s \<acute>nn"
term "LOC\<^sub>s \<acute>mm :== 1, \<acute>u :== 2, \<acute>z :== 2, \<acute>yy :== 3;; \<acute>u :==\<^sub>s 5 COL"
term "(\<lambda>s. ((fst (fst s, snd s\<lparr>locals1.mm_' := 1\<rparr>))\<lparr>globals_state2.u_' := 2\<rparr>,
        snd (fst s, snd s\<lparr>locals1.mm_' := 1\<rparr>)))"

procedures a(y|yy) = "\<acute>y :== \<acute>x;;\<acute>yy :== \<acute>x"

procedures b(y|yy) = "\<acute>y :== \<acute>x;;\<acute>yy :==\<^sub>g \<acute>x"

context a_impl begin
term "\<acute>x :== DYNCALL a(\<acute>y)" 
end

context b_impl begin
term "\<acute>x :== CALL\<^sub>g b(\<acute>y)" 
end


term "IF\<^sub>g ( (\<acute>x) =   \<acute>x) 
      THEN \<acute>x :== \<acute>x 
      ELSE \<acute>y :== \<acute>y FI"

term "WHILE\<^sub>s ( (\<acute>x) =   \<acute>x) 
      DO\<^sub>s \<acute>x :==\<^sub>s \<acute>x OD"

term "\<lbrace>(\<acute>y) =  \<acute>y \<rbrace>"
term "\<acute>x :==\<^sub>g \<acute>x "

term "\<acute>p :==\<^sub>g \<acute>q"

term "\<acute>p1 :== NEW sz [\<acute>cont:==0, \<acute>next:==Null]"
term "\<acute>p :==\<^sub>s NEW sz [\<acute>cont:==0,\<acute>next:== Null]"
term "\<acute>p :== NEW sz [\<acute>obj:==0,\<acute>cont:==0,\<acute>next:== Null]"
definition h::"nat \<Rightarrow> nat \<Rightarrow> nat"
  where "h x y \<equiv> x + y"


ML\<open>
val l = Syntax.read_term @{context} "\<acute>p :== NEW sz [\<acute>obj:==0,\<acute>cont:==0,\<acute>next:== Null]";

val v = writeln (Syntax.string_of_term @{context} l);
val v = writeln (@{make_string} l)
\<close>
(* \<acute>x :==\<^sub>s \<acute>y is translated into 
Basic (\<lambda>s. s\<lparr>x_':= (y_' s)\<rparr>)
*)
