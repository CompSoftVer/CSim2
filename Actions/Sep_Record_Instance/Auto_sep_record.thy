theory Auto_sep_record
imports Main  "Sep_Algebra.Separation_Algebra"
"Sep_Algebra.Sep_Heap_Instance" "Lib.Lib"

keywords "sep_record" :: thy_decl  and "kk":: thy_decl

begin
ML_file "../lib/mkterm_antiquote.ML"
ML_file "../lib/utils.ML"
ML_file "auto_sep_record.ML"

record h =
  a::"nat option"
  b::"nat option"

 
sep_record "h" 

ML\<open>

val full_rec_name =  Binding.empty 

val full_rec_name2 = Binding.empty
                             
val full_rec_name1 =  (Binding.name "h") |> Binding.restricted NONE |> Binding.concealed 
val v = Binding.name_of full_rec_name1
\<close>

record ('a::sep_algebra) d = uno :: "'a"
record ('a::sep_algebra,'c::sep_algebra) d1 = "'a d" + 
                              tres::"(nat \<Rightarrow> ('c option))"
                              tres'::"(nat \<Rightarrow> ('c option))"

ML\<open>                           
val u = Theory.parents_of @{theory}
val z = @{context}            

val u = @{theory_context Pure}
val h = Proof_Context.transfer @{theory} u
\<close>


sep_record "d" "nat option"

sep_record "d1"  "nat option" "nat option" 
thm sep_disj_d1_ext_def   

ML\<open>

val x1 = Attrib.setup_config_bool @{binding my_flag1} (K false)
val x = Attrib.setup_config_bool (Binding.name "my_flag") (K false)
\<close>



experiment begin
declare [[show_types = true]]

lemma "True \<noteq> False" by auto

end
notepad begin
term "d1"
end
end


   