structure Builtins : BUILTINS =
struct
  structure Syntax = Syntax
  structure Conv = Conv
  type label = string

  open OperatorType Syntax Conv
  infix $ $$ \\

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

    val unfoldAnd =
      makeConv AND (fn #[A,B] => PROD $$ #[A,Variable.named "_" \\ B] | _ => raise Conv)

    val unfoldImplies =
      makeConv IMPLIES (fn #[A,B] => FUN $$ #[A,Variable.named "_" \\ B] | _ => raise Conv)

    val unfoldIff =
      makeConv IFF (fn #[A,B] => AND $$ #[IMPLIES $$ #[A,B], IMPLIES $$ #[B,A]] | _ => raise Conv)

    val unfoldId =
      makeConv ID
        (fn #[] => let val v = Variable.named "x" in LAM $$ #[v \\ ``v] end
          | _ => raise Conv)

    val unfoldBot =
      makeConv BOT (fn #[] => FIX $$ #[ID $$ #[]] | _ => raise Conv)

    val unfoldSquash =
      makeConv SQUASH (fn #[T] =>
        let
          val v  = Variable.named "_"
          val ax = AX $$ #[]
        in
          IMAGE $$ #[T, LAM $$ #[v \\ ax]]
        end
      | _ => raise Conv)

  in
    (* add definitions here via composition: unfoldX o unfoldY o unfoldZ... *)
  val definitions =
      unfoldMember
      o unfoldAnd
      o unfoldImplies
      o unfoldIff
      o unfoldId
      o unfoldBot
      o unfoldSquash
  end

  val unfold = StringListDict.lookup (definitions StringListDict.empty)
end
