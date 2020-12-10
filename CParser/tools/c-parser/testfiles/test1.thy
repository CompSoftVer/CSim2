theory test1
  imports "../CTranslation"
begin
external_file "test.c"    
ML {*
structure test1=
 struct
open IsarInstall ProgramAnalysis
  
fun global_details vi = (srcname vi, length (get_vi_attrs vi))

val all_global_details = get_globals #> map global_details


end
*}

ML {*
open IsarInstall CalculateState ProgramAnalysis
val mensafe = NONE
val ctyps = NONE
val cdefs = NONE
val s = "test.c"
val thy= @{theory}
val statetylist_opt = NONE
val ast = get_Csyntax thy s
val functions = stmt_translation.extract_defined_functions ast
val thy1 = install_C_file(((((mensafe),ctyps),cdefs),s),statetylist_opt) thy

val cenv = get_csenv thy1 "test.c"|> the

val ast1 = SyntaxTransforms.remove_embedded_fncalls cenv ast
val mungedb = get_mungedb thy1 "test.c" |> the
val ghostty = get_ghostty thy1 "test.c"
val umm_types_file = gen_umm_types_file cenv "test.c"
val senv = get_senv cenv

*}
end
