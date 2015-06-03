structure Syntax : PARSE_ABT =
struct
  structure V = StringVariable
  structure Abt = Abt
    (structure Operator = Operator
     structure Variable = V)

  structure MyOp = Operator
  structure ParseAbt = ParseAbt
    (structure Syntax = AbtUtil(Abt)
     structure Operator = Operator)
  open ParseAbt

  local
    infix $ \
    infix 8 $$ // \\
    open MyOp
  in
    val to_string =
    let
      fun enclose E =
        case out E of
             ` x => display E
           | O $ #[] => display E
           | _ => "(" ^ display E ^ ")"

      and display E =
        case out E of
             ISECT $ #[A,xB] =>
               let
                 val (x, B) = unbind xB
               in
                 "⋂" ^ Variable.to_string x ^ " ∈ " ^ display A ^ ". " ^ display B
               end

           | FUN $ #[A, xB] =>
               let
                 val (x, B) = unbind xB
               in
                 if has_free (B, x) then
                   "Π" ^ Variable.to_string x ^ " ∈ " ^ display A ^ ". " ^ display B
                 else
                   enclose A ^ " => " ^ display B
               end

           | PROD $ #[A, xB] =>
               let
                 val (x, B) = unbind xB
               in
                 if has_free (B, x) then
                   "Σ" ^ Variable.to_string x ^ " ∈ " ^ display A ^ ". " ^ display B
                 else
                   enclose A ^ " × " ^ display B
               end

           | SUBSET $ #[A, xB] =>
               let
                 val (x, B) = unbind xB
               in
                 if has_free (B, x) then
                   "{" ^ Variable.to_string x ^ " ∈ " ^ display A ^ " | " ^ display B ^ "}"
                 else
                   "{" ^ display A ^ " | " ^ display B ^ "}"
               end


           | LAM $ #[xE] =>
               let
                 val (x, E) = unbind xE
               in
                 "λ" ^ dvar (x, E) ^ ". " ^ display E
               end

           | AP $ #[M, N] =>
               enclose M ^ "[" ^ display N ^ "]"

           | PAIR $ #[M, N] =>
               "⟨" ^ display M ^ ", " ^ display N ^ "⟩"

           | MEM $ #[M, A] =>
               display M ^ " ∈ " ^ display A

           | EQ $ #[M, N, A] =>
               display M ^ " = " ^ display N ^ " ∈ " ^ display A

           | UNIV i $ #[] =>
               "U" ^ subscript i

           | SPREAD $ #[M, xyN] =>
               let
                 val (x, yN) = unbind xyN
                 val (y, N) = unbind yN
               in
                 "let " ^ dvar (x, yN) ^ "," ^ dvar (y, N) ^ " = " ^ display M ^ " in " ^ display N
               end

           | UNIV_EQ i $ #[] =>
               "U⁼" ^ subscript i

           | EQ_EQ $ #[A,M,N] =>
               display M ^ " =⁼ " ^ display N ^ " ∈⁼ " ^ display A

           | UNIT_INTRO $ #[] =>
              "⬧"

           | UNIT_ELIM $ #[x,D] =>
               "let ⬧ = "  ^ display x ^ " in " ^ display D

           | PROD_EQ $ #[D, xE] =>
               let
                 val (x, E) = unbind xE
               in
                 if has_free (E, x) then
                   "Σ⁼" ^ Variable.to_string x ^ " ∈ " ^ display D ^ ". " ^ display E
                 else
                   enclose D ^ " ×⁼ " ^ display E
               end

           | PROD_INTRO $ #[M, D, E, xF] =>
               let
                 val (x, F) = unbind xF
               in
                 "⟨⸤" ^ display M ^ "⸥ by "
                  ^ display D
                  ^ ", " ^ display E
                  ^ " : "
                  ^ (if has_free (F, x) then
                      "[" ^ display M ^ "/" ^ dvar (x, F) ^ "]("^ display xF ^ ")"
                    else
                      display F)
                  ^ "⟩"
               end

           | PROD_ELIM $ #[D, xyE] =>
               let
                 val (x, yE) = unbind xyE
                 val (y, E) = unbind yE
               in
                 "let " ^ dvar (x, yE) ^ "," ^ dvar (y, E) ^ " = " ^ display D ^ " in " ^ display E
               end

           | SPREAD_EQ $ #[D, xyzE] =>
               let
                 val (x, yzE) = unbind xyzE
                 val (y, zE) = unbind yzE
                 val (z, E) = unbind zE
               in
                 "let⁼ " ^ dvar (x, yzE) ^ "," ^ dvar (y, zE) ^ " = " ^ display D ^ " by " ^ dvar (z, E) ^ " in " ^ display E
               end

           | FUN_EQ $ #[D, xE] =>
               let
                 val (x, E) = unbind xE
               in
                 if has_free (E, x) then
                   "Π⁼" ^ Variable.to_string x ^ " ∈ " ^ display D ^ ". " ^ display E
                 else
                   enclose D ^ " =>⁼ " ^ display E
               end

           | FUN_INTRO $ #[xD, E] =>
               let
                 val (x, D) = unbind xD
               in
                 "λ" ^ dvar (x, D) ^ " ∈ " ^ display E ^ ". " ^ display D
               end

           | FUN_ELIM $ #[f, s, D, yzE] =>
               let
                 val (y, zE) = unbind yzE
                 val (z, E) = unbind zE
               in
                 "let " ^ dvar (y, zE) ^ " = " ^ enclose f ^ "[" ^ display s ^ " : " ^ display D ^ "] by " ^ dvar (z, E) ^ " in " ^ display E
               end

           | ISECT_EQ $ #[D, xE] =>
               let
                 val (x, E) = unbind xE
               in
                 "⋂⁼" ^ Variable.to_string x ^ " ∈ " ^ display D ^ ". " ^ display E
               end

           | LAM_EQ $ #[xD, E] =>
               let
                 val (x, D) = unbind xD
               in
                 "λ⁼" ^ dvar (x, D) ^ " ∈ " ^ display E ^ ". " ^ display D
               end

           | AP_EQ $ #[D, E] =>
               display D ^ "[" ^ display E ^ "]⁼"

           | ISECT_INTRO $ #[xD, E] =>
               let
                 val (x, D) = unbind xD
               in
                 "λ[" ^ dvar (x, D) ^ " ∈ " ^ display E ^ "]. " ^ display D
               end

           | VOID_ELIM $ #[D] =>
               "!" ^ display D

           | HYP_EQ $ #[x] =>
               display x ^ "⁼"

           | EQ_SUBST $ #[D, E, xF] =>
               "rewrite " ^ display D ^ " at " ^ display xF ^ " in " ^ display E

           | EQ_SYM $ #[D] =>
               "sym " ^ display D

           | WITNESS $ #[M, D] =>
               "⸤" ^ display M ^ "⸥ by " ^ display D

           | CUM $ #[D] =>
               "cumulativity " ^ display D

           | _ => to_string_open display E

      and dvar (x, E) =
        if has_free (E, x) then Variable.to_string x else "_"

      and subscript i =
        case i of
             0 => "₀"
           | 1 => "₁"
           | 2 => "₂"
           | 3 => "₃"
           | 4 => "₄"
           | 5 => "₅"
           | 6 => "₆"
           | 7 => "₇"
           | 8 => "₈"
           | 9 => "₉"
           | _ => let val m = i mod 10 in subscript ((i - m) div 10) ^ subscript m end
    in
      display
    end
  end
end
