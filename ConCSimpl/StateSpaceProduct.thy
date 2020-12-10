(*
    Author:     David Sanan
    Maintainer:  David Sanan, sanan at ntu edu sg
    License:     LGPL
*)

(*  Title:      StateSpace.thy
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

section {* State Space Template *}
theory StateSpaceProduct imports EmbSimpl.Hoare
begin


type_synonym ('g, 'n, 'val) stateSP = "'g \<times> ('n \<Rightarrow> 'val)"

definition
  upd_globals:: "('g \<Rightarrow> 'g) \<Rightarrow> 'g \<times> 'l \<Rightarrow> 'g \<times> 'l"
where
  "upd_globals upd s = (upd (fst s), snd s)" 


definition
  globals_update:: "('g \<Rightarrow> 'g) \<Rightarrow> 'g \<times> 'l \<Rightarrow> 'g \<times> 'l"
where
  "globals_update upd s = (upd (fst s), snd s)" 

declare globals_update_def[simp]

definition globals ::"'g \<times> 'l \<Rightarrow> 'g"
  where "globals s \<equiv> fst s"

definition locals :: " ('g, 'n, 'val) stateSP \<Rightarrow> ('n \<Rightarrow> 'val)"
  where
"locals s \<equiv> snd s" 

definition upd_locals::"( ('n \<Rightarrow> 'val) \<Rightarrow>  ('n \<Rightarrow> 'val)) \<Rightarrow> ('g, 'n, 'val) stateSP \<Rightarrow> ('g, 'n, 'val) stateSP" 
  where
"upd_locals upd s = (fst s, upd (snd s))"

definition locals_update::"( ('n \<Rightarrow> 'val) \<Rightarrow>  ('n \<Rightarrow> 'val)) \<Rightarrow> ('g, 'n, 'val) stateSP \<Rightarrow> ('g, 'n, 'val) stateSP" 
  where
"locals_update upd s = (fst s, upd (snd s))"

declare locals_update_def[simp]


lemma upd_globals_conv: "upd_globals f = (\<lambda>s. (f (fst s), snd s))"
  by (rule ext) (simp add: upd_globals_def)

lemma globals_updates_conv: "globals_update f = (\<lambda>s. (f (fst s), snd s))"
  by (rule ext) (simp)


lemma upd_locals_conv: "upd_locals f = (\<lambda>s. (fst s, f (snd s)))"
  by (rule ext) (simp add: upd_locals_def)

lemma locals_updates_conv: "locals_update f = (\<lambda>s. (fst s, f (snd s)))"
  by (rule ext) (simp)


end
