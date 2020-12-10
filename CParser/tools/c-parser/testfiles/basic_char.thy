(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory basic_char
imports "CParser.CTranslation"
begin

(* locale "globals1"
begin
definition g1::"nat" where "g1 \<equiv> 0"
end *)

(* record locals_myvars1 = i_':: nat
record globals1 = j_'::nat

datatype event = Evnt
ML \<open> 
val t = Syntax.read_term @{context} "(\<acute>i:==\<acute>j)::(((globals1 \<times> locals_myvars1), nat, nat, event) LanguageCon.com)";
val b = Binding.name "myfunc"
val v = ((b, NoSyn), ((Thm.def_binding b, []), t))
val lthy = Named_Target.init "basic_char.globals1" @{theory}
val x = lthy |> Local_Theory.open_target |> snd
      |> Local_Theory.define  v |> #2 |> Local_Theory.close_target
val _ = writeln ("body: "^ (@{make_string} (Syntax.read_term x "myfunc")))
val thy = Local_Theory.exit_global lthy
val _ = writeln (@{make_string} (type_of (Syntax.read_term @{context} "prod")))
\<close>

*)
                      
external_file "basic_char.c" 
install_C_file  "basic_char.c"

ML\<open>
 val T = strip_type (Type("fun",[Type("A",[]),Type("B",[])]))
 val T = strip_type (Type("fun",[Type("A",[]),Type("B",[])]))
 val T1 = fst T ---> snd T
 val T2 = strip_type T1
 val l = Syntax.read_term @{context} "(x::nat)";
 fun print_t t = 
 let val _ = writeln ("name " ^ (@{make_string} @{typ "nat"})) in
   t
  end
 val l = print_t l
\<close>


context basic_char
begin
abbreviation "i \<equiv> i_'"
term "the (\<Gamma> 1)"
  thm f1_body_def

  
lemma "the (\<Gamma> f1_'proc) = (f1_body)"
  by (simp add: basic_char_global_addresses.f1_impl)

end

end

