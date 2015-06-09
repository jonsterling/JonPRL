signature CTT_UTIL =
sig
  include CTT
  val Auto : Lcf.tactic

  type intro_args =
    {term : Syntax.t option,
     fresh_variable : name option,
     level : Level.t option}

  type elim_args =
    {target : name,
     names : name list,
     term : term option}

  val Intro : intro_args -> Lcf.tactic
  val Elim : elim_args -> Lcf.tactic

end
