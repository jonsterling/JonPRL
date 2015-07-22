structure Builtins : BUILTINS =
struct
  structure Syntax = Syntax
  structure Conv = Conv
  type label = string

  open OperatorType Syntax Conv
  infix $ $$

  local
    fun makeConv oper f tbl =
      StringListDict.insert tbl (Operator.toString oper) (fn P =>
        case out P of
             oper' $ es =>
               if Operator.eq (oper, oper') then
                 f es
               else
                 raise Conv
           | _ => raise Conv)

    val unfoldMember =
      makeConv MEM (fn #[M,A] => EQ $$ #[M,M,A] | _ => raise Conv)
  in
    (* add definitions here via composition: unfoldX o unfoldY o unfoldZ... *)
    val definitions = unfoldMember
  end

  val unfold = StringListDict.lookup (definitions StringListDict.empty)
end
