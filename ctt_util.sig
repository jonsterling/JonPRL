signature CTT_UTIL =
sig
  include CTT
  val Auto : Lcf.tactic
  val DeepReduce : Lcf.tactic
end
