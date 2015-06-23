signature TACTIC_SCRIPT =
sig
  type tactic
  include INTENSIONAL_PARSER where type t = tactic
end
