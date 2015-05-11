structure Syntax : ABT_UTIL =
struct
  structure V = Variable ()
  structure Abt = Abt
    (structure Operator = Operator
     structure Variable = V)

  structure AbtUtil = AbtUtil(Abt)
  open AbtUtil
end
