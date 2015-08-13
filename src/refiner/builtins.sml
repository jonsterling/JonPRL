structure Builtins : BUILTINS =
struct
  structure Syntax = Syntax
  structure Conv = Conv

  open CttCalculus CttCalculusInj Syntax Conv
  infix $ $$ \\

  type operator = UniversalOperator.t

  structure Dict = SplayDict
    (structure Key =
     struct
       type t = Syntax.Operator.t
       val eq = Syntax.Operator.eq
       fun compare (theta, theta') =
         String.compare
           (Syntax.Operator.toString theta,
            Syntax.Operator.toString theta')
     end)

  local
    fun makeConv (theta : CttCalculus.t) f tbl =
      Dict.insert tbl (`> theta) (fn P =>
        case out P of
             theta' $ es =>
               if Operator.eq (`> theta, theta') then
                 f es
               else
                 raise Conv
           | _ => raise Conv)

    val unfoldMember =
      makeConv MEM (fn #[M,A] => `> EQ $$ #[M,M,A] | _ => raise Conv)

    val unfoldAnd =
      makeConv AND (fn #[A,B] => `> PROD $$ #[A,Variable.named "x" \\ B] | _ => raise Conv)

    val unfoldImplies =
      makeConv IMPLIES (fn #[A,B] => `> FUN $$ #[A,Variable.named "x" \\ B] | _ => raise Conv)

    val unfoldIff =
      makeConv IFF (fn #[A,B] => `> AND $$ #[`> IMPLIES $$ #[A,B], `> IMPLIES $$ #[B,A]] | _ => raise Conv)

    val unfoldId =
      makeConv ID
        (fn #[] => let val v = Variable.named "x" in `> LAM $$ #[v \\ ``v] end
          | _ => raise Conv)

    val unfoldBot =
      makeConv BOT (fn #[] => `> FIX $$ #[`> ID $$ #[]] | _ => raise Conv)

    val unfoldSquash =
      makeConv SQUASH (fn #[T] =>
        let
          val v = Variable.named "x"
          val ax = `> AX $$ #[]
        in
          `> IMAGE $$ #[T, `> LAM $$ #[v \\ ax]]
        end
      | _ => raise Conv)

    val unfoldFst =
      makeConv FST (fn #[T] =>
        let
          val x = Variable.named "x"
          val y = Variable.named "y"
        in
          `> SPREAD $$ #[T, x \\ (y \\ ``x)]
        end
      | _ => raise Conv)

    val unfoldSnd =
      makeConv SND (fn #[T] =>
        let
          val x = Variable.named "x"
          val y = Variable.named "y"
        in
          `> SPREAD $$ #[T, x \\ (y \\ ``y)]
        end
      | _ => raise Conv)

    val unfoldSubtypeRel =
      makeConv SUBTYPE_REL (fn #[A,B] =>
        let
          val x = Variable.named "p"
        in
          `> MEM $$ #[`> ID $$ #[], `> FUN $$ #[A, x \\ B]]
        end
      | _ => raise Conv)

    val unfoldBunion =
      makeConv BUNION (fn #[A,B] =>
        let
          val v = Variable.named "x"
          val w = Variable.named ""
          val snd = `> LAM $$ #[v \\ (`> SND $$ #[``v])]
          val unt = `> UNIT $$ #[]
          val two = `> PLUS $$ #[unt, unt]
          val dec = `> DECIDE $$ #[``v, w \\ A, w \\ B]
          val prd = `> PROD $$ #[two, v \\ dec]
        in
          `> IMAGE $$ #[prd, snd]
        end
      | _ => raise Conv)

    val unfoldUnit =
      makeConv UNIT (fn #[] =>
        let
          val ax = `> AX $$ #[]
        in
          `> APPROX $$ #[ax, ax]
        end
      | _ => raise Conv)

    val unfoldVoid =
      makeConv VOID (fn #[] =>
        let val ax = `> AX $$ #[]
            val bot = `> BOT $$ #[]
        in `> APPROX $$ #[ax,bot]
	end
      | _ => raise Conv)

    val unfoldHasValue =
      makeConv HASVALUE (fn #[T] =>
        let val ax = `> AX $$ #[]
	    val v = Variable.named ""
	    val cbv = `> CBV $$ #[ax,v \\ T]
        in `> APPROX $$ #[ax,cbv]
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
      o unfoldFst
      o unfoldSnd
      o unfoldSubtypeRel
      o unfoldBunion
      o unfoldUnit
      o unfoldVoid
      o unfoldHasValue
  end

  val unfold = Dict.lookup (definitions Dict.empty)
end
