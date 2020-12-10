(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory jiraver313
  imports "CParser.CTranslation"
begin

ML \<open>Feedback.verbosity_level := 6\<close>

declare [[calculate_modifies_proofs = false ]]

external_file "jiraver313.c"
install_C_file memsafe "jiraver313.c"

ML \<open>
local
open Absyn
val cpp_record =
    {cpp_path = SOME "/usr/bin/cpp", error_detail = 10}
val (decls, _) =
  StrictCParser.parse (IsarInstall.do_cpp cpp_record) 15 []
    (IsarInstall.mk_thy_relative @{theory} "jiraver313.c");
in
val Decl d = hd decls
val VarDecl vd = RegionExtras.node d
end
\<close>

context jiraver313
begin
term foo
term bar
thm f_body_def
thm g_body_def

end

end
