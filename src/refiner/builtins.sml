structure Builtins : BUILTINS =
struct
  structure Syntax = Syntax
  structure Conv = Conv
  type label = Label.t

  open OperatorType Syntax Conv
  infix $ $$ \\

  type operator = Syntax.Operator.t

  local
    fun makeConv theta f tbl =
      StringListDict.insert tbl (Operator.toString theta) (theta, fn P =>
        case out P of
             theta' $ es =>
               if Operator.eq (theta, theta') then
                 f es
               else
                 raise Conv
           | _ => raise Conv)

    val unfoldMember =
      makeConv MEM (fn #[M,A] => EQ $$ #[M,M,A] | _ => raise Conv)

    val unfoldAnd =
      makeConv AND (fn #[A,B] => PROD $$ #[A,Variable.named "x" \\ B] | _ => raise Conv)

    val unfoldImplies =
      makeConv IMPLIES (fn #[A,B] => FUN $$ #[A,Variable.named "x" \\ B] | _ => raise Conv)

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
          val v = Variable.named "x"
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
